{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Pretty printing.
module Taype.Cute
  ( Cute,
    cute,
    CuteM (..),
    runCuteM,
    contCuteM,
    cuteDefs,
    cuteDef,
    hang,
    indent,
    sep1,
    sepWith,
    nameOrBinder,
    printDoc,
  )
where

import Bound
import Data.HashMap.Strict ((!?))
import qualified Data.Text as T
import Prettyprinter hiding (Doc, hang, indent)
import qualified Prettyprinter as PP
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter.Util (putDocW)
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.Prelude
import Taype.Syntax
import Prelude hiding (group)

indentLevel :: Int
indentLevel = 2

hang :: Doc -> Doc
hang = PP.hang indentLevel

indent :: Doc -> Doc
indent = PP.indent indentLevel

sepWith :: Foldable t => Doc -> t Doc -> Doc
sepWith s = concatWith (\x y -> x <> s <> y)

sep1 :: Doc -> Doc
sep1 = group . (line <>)

printDoc :: MonadIO m => Options -> Doc -> m ()
printDoc Options {..} = liftIO . maybe putDoc putDocW optWidth

-- | A context for fresh name generation and environment
newtype CuteM a = CuteM {unCuteM :: FreshT (Reader Options) a}
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadReader Options)

runCuteM :: Options -> CuteM a -> a
runCuteM opts (CuteM m) = runReader (runFreshT m) opts

contCuteM :: Options -> Int -> CuteM a -> a
contCuteM opts n (CuteM m) = runReader (contFreshT n m) opts

instance IsString a => IsString (CuteM a) where
  fromString = return . fromString

-- | Pretty print class with fresh name generator and environment
class Cute a where
  cute :: a -> CuteM Doc
  default cute :: Pretty a => a -> CuteM Doc
  cute = return <$> pretty

instance Cute Int

instance Cute Text

instance Cute Kind

instance Cute Label

instance Cute Err where
  cute Err {..} = do
    Options {optFile = file, optCode = code} <- ask
    return $
      "!!" <> pretty errCategory <> "!!" <> hardline
        <> pretty (renderFancyLocation file code errLoc)
        <> hardline
        <> hardline
        <> errMsg
        <> hardline

instance Cute (TCtx Text) where
  cute tctx = do
    docs <- mapM go tctx
    return $
      hang $
        "Typing context" <> colon <> hardline
          <> if null tctx then "<empty>" else sepWith hardline docs
    where
      go (x, (t, l)) = cuteBinder x (Just l) (Just t)

instance Cute (Expr Text) where
  cute = cuteExpr

-- | Pretty printer for Taype expressions
cuteExpr :: Expr Text -> CuteM Doc
cuteExpr V {..} = cute name
cuteExpr GV {..} = cute ref
cuteExpr e@Pi {..} = do
  (x, body) <- unbind1NameOrBinder binder bnd
  binderDoc <- cuteTypeBinder e x label ty binder
  bodyDoc <- cuteExpr body
  return $ binderDoc <+> "->" <> line <> bodyDoc
cuteExpr e@Lam {} = cuteLam False e
cuteExpr e@App {appKind = Just InfixApp, args = left : right : _, ..} = do
  fnDoc <- cuteSubExprAgg fn
  cuteInfix e fnDoc left right
cuteExpr App {appKind = Just InfixApp} = oops "Not enough infix operands"
cuteExpr App {..} = do
  fnDoc <- cuteSubExprAgg fn
  cuteApp fnDoc args
cuteExpr e@Let {} = cuteLet e
cuteExpr TUnit = "Unit"
cuteExpr VUnit = "()"
cuteExpr TBool = "Bool"
cuteExpr OBool = "~Bool"
cuteExpr BLit {..} = if bLit then "True" else "False"
cuteExpr TInt = "Int"
cuteExpr OInt = "~Int"
cuteExpr ILit {..} = cute iLit
cuteExpr Ite {..} = cuteIte "" cond ifTrue ifFalse
cuteExpr Case {..} = do
  condDoc <- cuteExpr cond
  altDocs <- mapM cuteCaseAlt alts
  return $ cuteCaseDoc "" True condDoc altDocs
cuteExpr OIte {..} = cuteIte "~" cond ifTrue ifFalse
cuteExpr e@Prod {..} = cuteInfix e "*" left right
cuteExpr Pair {..} = cutePair "" left right
cuteExpr PCase {..} = cutePCase "" cond lBinder rBinder bnd2
cuteExpr e@OProd {..} = cuteInfix e "~*" left right
cuteExpr OPair {..} = cutePair "~" left right
cuteExpr OPCase {..} = cutePCase "~" cond lBinder rBinder bnd2
cuteExpr e@OSum {..} = cuteInfix e "~+" left right
cuteExpr OInj {..} = do
  typeDoc <- fromMaybe "" <$> mapM cuteInjType mTy
  cuteApp ((if tag then "~inl" else "~inr") <> typeDoc) [inj]
  where
    cuteInjType ty = angles <$> cuteExpr ty
cuteExpr OCase {..} = do
  condDoc <- cuteExpr cond
  (xl, lBody) <- unbind1NameOrBinder lBinder lBnd
  (xr, rBody) <- unbind1NameOrBinder rBinder rBnd
  lBodyDoc <- cuteExpr lBody
  rBodyDoc <- cuteExpr rBody
  return $
    cuteCaseDoc "~" True condDoc $
      cuteAltDocs [("~inl", [xl], lBodyDoc), ("~inr", [xr], rBodyDoc)]
cuteExpr Mux {..} = cuteApp "mux" [cond, ifTrue, ifFalse]
cuteExpr Asc {..} = do
  typeDoc <- cuteExpr ty
  exprDoc <- cuteExpr expr
  return $ parens $ hang $ align exprDoc <> sep1 (colon <+> typeDoc)
cuteExpr Promote {..} = do
  doc <- cuteSubExprAgg expr
  return $ "!" <> doc
cuteExpr Tape {..} = cuteApp "tape" [expr]
cuteExpr Loc {..} = cuteExpr expr

-- | Cute printer for Taype definitions
cuteDefs :: Options -> GCtx Text -> [Text] -> Doc
cuteDefs options gctx =
  foldMap $ \name -> cuteDef options gctx name <> hardline <> hardline

cuteDef :: Options -> GCtx Text -> Text -> Doc
cuteDef options gctx name =
  case fromMaybe (oops "definition not in context") (gctx !? name) of
    FunDef {..} ->
      "#" <> brackets (pretty attr) <> hardline <> funDoc
      where
        funDoc =
          hang $
            "fn" <+> go (cuteBinder name label (Just ty)) <+> equals
              <> go (cuteLam True expr)
    ADTDef {..} ->
      "data" <+> pretty name
        <+> align
          ( equals
              <+> group (sepWith (line <> pipe <> space) (cuteCtor <$> ctors))
          )
      where
        cuteCtor (ctor, paraTypes) =
          hang $
            pretty ctor
              <> group (foldMap ((line <>) . go . cuteSubExprAgg) paraTypes)
    OADTDef {..} ->
      hang $ "obliv" <+> pretty name <+> rest
      where
        rest = go $ do
          (x, body) <- unbind1NameOrBinder binder bnd
          binderDoc <- cuteBinder x (Just SafeL) (Just ty)
          bodyDoc <- cuteExpr body
          return $ parens binderDoc <+> equals <> hardline <> bodyDoc
    _ -> oops "builtin functions or constructors in the definitions"
  where
    go = runCuteM options

cuteBinder :: Text -> Maybe Label -> Maybe (Ty Text) -> CuteM Doc
cuteBinder x l Nothing =
  ifM
    (asks optPrintLabels &&^ return (isJust l))
    ((<>) . parens <$> cute x <*> cuteLabel l)
    (cute x)
cuteBinder x l (Just ty) = do
  typeDoc <- cuteExpr ty
  labelDoc <- ifM (asks optPrintLabels) (cuteLabel l) ""
  return $
    hang $
      pretty x
        <> ( if T.length x <= indentLevel
               then (space <>)
               else sep1
           )
          (colon <> labelDoc <+> align (group typeDoc))

cuteEnclosedBinder :: Text -> Maybe Label -> Maybe (Ty Text) -> CuteM Doc
cuteEnclosedBinder x l mTy = do
  doc <- cuteBinder x l mTy
  return $ if isJust mTy then parens doc else doc

cuteTypeBinder ::
  Ty Text ->
  Text ->
  Maybe Label ->
  Ty Text ->
  Maybe Binder ->
  CuteM Doc
cuteTypeBinder super x l ty = \case
  Just Anon ->
    ifM
      (asks optInternalNames)
      go
      ( ifM
          (asks optPrintLabels &&^ return (isJust l))
          ((<>) . parens <$> cuteExpr ty <*> cuteLabel l)
          (cuteSubExpr super ty)
      )
  _ -> go
  where
    go = parens <$> cuteBinder x l (Just ty)

cuteLabel :: Maybe Label -> CuteM Doc
cuteLabel = maybe "" cute

cuteLam :: Bool -> Expr Text -> CuteM Doc
cuteLam isRoot e = do
  (binderDocs, bodyDoc) <- go e
  return $
    if null binderDocs
      then if isRoot then sep1 bodyDoc else oops "Lambda has no binder"
      else
        if isRoot -- Quite hacky here
          then
            group
              ( flatAlt
                  (hardline <> group (mkBindersDoc binderDocs) <> hardline)
                  (space <> mkBindersDoc binderDocs)
              )
              <> column
                ( \k ->
                    nesting
                      (\i -> if k <= i then indent bodyDoc else sep1 bodyDoc)
                )
          else hang $ group (mkBindersDoc binderDocs) <> sep1 bodyDoc
  where
    mkBindersDoc binderDocs = backslash <> align (vsep binderDocs) <+> "->"
    go :: Expr Text -> CuteM ([Doc], Doc)
    go Lam {..} = do
      (x, body) <- unbind1NameOrBinder binder bnd
      binderDoc <- cuteEnclosedBinder x label mTy
      (binderDocs, bodyDoc) <- go body
      return (binderDoc : binderDocs, bodyDoc)
    go Loc {..} = go expr
    go expr = ([],) <$> cuteExpr expr

cuteLet :: Expr Text -> CuteM Doc
cuteLet e = do
  (bindingDocs, bodyDoc) <- go e
  return $
    if null bindingDocs
      then oops "Let has no binding"
      else group $ mkDoc bindingDocs bodyDoc
  where
    mkDoc bindingDocs bodyDoc =
      align $
        "let"
          <+> align (sepWith hardline (mkBindingDoc <$> bindingDocs))
          <> line'
          <+> "in"
          <+> align bodyDoc
    mkBindingDoc (binderDoc, rhsDoc) = hang $ binderDoc <+> equals <> sep1 rhsDoc
    go :: Expr Text -> CuteM ([(Doc, Doc)], Doc)
    go Let {..} = do
      (x, body) <- unbind1NameOrBinder binder bnd
      binderDoc <- cuteBinder x label mTy
      rhsDoc <- cuteExpr rhs
      (bindingDocs, bodyDoc) <- go body
      return ((binderDoc, rhsDoc) : bindingDocs, bodyDoc)
    go Loc {..} = go expr
    go expr = ([],) <$> cuteExpr expr

cuteIte :: Doc -> Expr Text -> Expr Text -> Expr Text -> CuteM Doc
cuteIte accent cond ifTrue ifFalse = do
  condDoc <- cuteExpr cond
  ifTrueDoc <- cuteExpr ifTrue
  ifFalseDoc <- cuteExpr ifFalse
  return $
    group $
      accent <> "if" <+> condDoc
        <> line
        <> hang ("then" <> sep1 ifTrueDoc)
        <> line
        <> hang ("else" <> sep1 ifFalseDoc)

cuteInfix :: Expr Text -> Doc -> Expr Text -> Expr Text -> CuteM Doc
cuteInfix super infixDoc left right = do
  leftDoc <- cuteSubExpr super left
  rightDoc <- cuteSubExpr super right
  return $ hang $ leftDoc <> sep1 (infixDoc <+> rightDoc)

cutePair :: Doc -> Expr Text -> Expr Text -> CuteM Doc
cutePair accent left right = do
  leftDoc <- cuteExpr left
  rightDoc <- cuteExpr right
  return $ cutePairDoc accent leftDoc rightDoc

cutePCase ::
  Doc ->
  Expr Text ->
  Maybe Binder ->
  Maybe Binder ->
  Scope Bool Expr Text ->
  CuteM Doc
cutePCase accent cond lBinder rBinder bnd2 = do
  condDoc <- cuteExpr cond
  ((xl, xr), body) <- unbind2NamesOrBinders (lBinder, rBinder) bnd2
  bodyDoc <- cuteExpr body
  return $
    cuteCaseDoc
      accent
      False
      condDoc
      [ hang $
          cutePairDoc accent (pretty xl) (pretty xr) <+> "->" <> sep1 bodyDoc
      ]

cutePairDoc :: Doc -> Doc -> Doc -> Doc
cutePairDoc accent leftDoc rightDoc =
  accent <> parens (align (leftDoc <> comma <> sep1 rightDoc))

cuteApp :: Doc -> [Expr Text] -> CuteM Doc
cuteApp fnDoc exprs = do
  docs <- mapM cuteSubExprAgg exprs
  return $ hang $ fnDoc <> group (foldMap (line <>) docs)

cuteCaseAlt :: CaseAlt Expr Text -> CuteM Doc
cuteCaseAlt CaseAlt {..} = do
  (xs, body) <- unbindManyNamesOrBinders binders bnd
  bodyDoc <- cuteExpr body
  return $ cuteAltDoc ctor xs bodyDoc

cuteCaseDoc :: Foldable t => Doc -> Bool -> Doc -> t Doc -> Doc
cuteCaseDoc accent usePipe condDoc altDocs =
  align $
    accent <> "case" <+> condDoc <+> "of"
      <> ( if usePipe
             then foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
             else foldMap (hardline <>) altDocs
         )
      <> hardline
      <> "end"

cuteAltDocs :: (Functor t) => t (Text, [Text], Doc) -> t Doc
cuteAltDocs = (go <$>)
  where
    go (ctor, xs, bodyDoc) = cuteAltDoc ctor xs bodyDoc

cuteAltDoc :: Text -> [Text] -> Doc -> Doc
cuteAltDoc ctor xs bodyDoc =
  hang
    ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
        <+> "->" <> sep1 bodyDoc
    )

-- | Add parentheses to the expressions according to their precedence level
cuteSubExpr :: Expr Text -> Expr Text -> CuteM Doc
cuteSubExpr super sub = cuteSubExprIf sub $ exprLevel super > exprLevel sub

-- | Add parentheses to the expressions more aggressively
cuteSubExprAgg :: Expr Text -> CuteM Doc
cuteSubExprAgg sub = cuteSubExprIf sub $ exprLevel sub == 0

cuteSubExprIf :: Expr Text -> Bool -> CuteM Doc
cuteSubExprIf sub b = do
  doc <- cuteExpr sub
  return $ if b then doc else parens $ align doc

exprLevel :: Expr a -> Int
exprLevel = \case
  V {} -> 0
  GV {} -> 0
  -- Do not distinguish infix further
  App {appKind = Just InfixApp} -> 20
  App {} -> 10
  TUnit -> 0
  VUnit -> 0
  TBool -> 0
  OBool -> 0
  BLit {} -> 0
  TInt -> 0
  OInt -> 0
  ILit {} -> 0
  Prod {} -> 20
  Pair {} -> 0
  OProd {} -> 20
  OPair {} -> 0
  OSum {} -> 20
  OInj {} -> 10
  Mux {} -> 10
  Promote {} -> 0
  Tape {} -> 10
  Asc {} -> 0
  Loc {..} -> exprLevel expr
  _ -> 90

nameOrBinder :: Options -> Name -> Maybe Binder -> Text
nameOrBinder Options {..} x mb =
  let name = optNamePrefix <> show x
   in if optInternalNames then name else maybe name toText mb

freshNameOrBinder :: Maybe Binder -> CuteM Text
freshNameOrBinder binder = do
  opt <- ask
  -- Always generate new name even if we use binder
  x <- fresh
  return $ nameOrBinder opt x binder

unbind1NameOrBinder ::
  Monad f => Maybe Binder -> Scope () f Text -> CuteM (Text, f Text)
unbind1NameOrBinder = unbindBy . freshNameOrBinder

unbind2NamesOrBinders ::
  Monad f =>
  (Maybe Binder, Maybe Binder) ->
  Scope Bool f Text ->
  CuteM ((Text, Text), f Text)
unbind2NamesOrBinders (binder1, binder2) =
  unbindBy $ (,) <$> freshNameOrBinder binder1 <*> freshNameOrBinder binder2

unbindManyNamesOrBinders ::
  Monad f => [Maybe Binder] -> Scope Int f Text -> CuteM ([Text], f Text)
unbindManyNamesOrBinders = unbindBy . mapM freshNameOrBinder

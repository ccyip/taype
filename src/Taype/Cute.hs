{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
    cuteExpr,
    cuteDefs,
    cuteDef,
  )
where

import Bound
import Data.HashMap.Strict ((!?))
import qualified Data.Text as T
import Prettyprinter hiding (hang, indent)
import qualified Prettyprinter as PP
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.Syntax
import Prelude hiding (group)

indentLevel :: Int
indentLevel = 2

hang :: Doc ann -> Doc ann
hang = PP.hang indentLevel

indent :: Doc ann -> Doc ann
indent = PP.indent indentLevel

sepWith :: Foldable t => Doc ann -> t (Doc ann) -> Doc ann
sepWith s = concatWith (\x y -> x <> s <> y)

sep1 :: Doc ann -> Doc ann
sep1 = group . (line <>)

-- | A context for fresh name generation and environment
newtype CuteM a = CuteM {unCuteM :: FreshT (Reader Options) a}
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadReader Options)

runCuteM :: Options -> CuteM a -> a
runCuteM opts (CuteM m) = runReader (runFreshT m) opts

instance IsString a => IsString (CuteM a) where
  fromString = return . fromString

-- | Pretty print class with fresh name generator and environment
class Cute a where
  cute :: a -> CuteM (Doc ann)
  default cute :: Pretty a => a -> CuteM (Doc ann)
  cute = return <$> pretty

instance Cute Int

instance Cute Text

instance Cute (Expr Text) where
  cute = cuteExpr

-- | Pretty printer for Taype expressions
cuteExpr :: Expr Text -> CuteM (Doc ann)
cuteExpr V {..} = cute name
cuteExpr GV {..} = cute ref
cuteExpr e@Pi {..} = do
  x <- freshNameOrBinder binder
  binderDoc <- cuteTypeBinder e x label ty binder
  bodyDoc <- cuteExpr $ instantiate1Name x body
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
cuteExpr PCase {..} = cutePCase "" cond lBinder rBinder body2
cuteExpr e@OProd {..} = cuteInfix e "~*" left right
cuteExpr OPair {..} = cutePair "~" left right
cuteExpr OPCase {..} = cutePCase "~" cond lBinder rBinder body2
cuteExpr e@OSum {..} = cuteInfix e "~+" left right
cuteExpr OInj {..} = do
  typeDoc <- fromMaybe "" <$> mapM cuteInjType mTy
  cuteApp ((if tag then "~inl" else "~inr") <> typeDoc) [inj]
  where
    cuteInjType ty = angles <$> cuteExpr ty
cuteExpr OCase {..} = do
  condDoc <- cuteExpr cond
  xl <- freshNameOrBinder lBinder
  xr <- freshNameOrBinder rBinder
  lBodyDoc <- cuteExpr $ instantiate1Name xl lBody
  rBodyDoc <- cuteExpr $ instantiate1Name xr rBody
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
cuteDefs :: Options -> GCtx Text -> [Text] -> Doc ann
cuteDefs options gctx =
  foldMap $ \name -> cuteDef options gctx name <> hardline <> hardline

cuteDef :: Options -> GCtx Text -> Text -> Doc ann
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
          (equals <+> group (sepWith (line <> pipe <> space) (cuteCtor <$> ctors)))
      where
        cuteCtor :: Text -> Doc ann
        cuteCtor ctor = case gctx !? ctor of
          Just (CtorDef {paraTypes}) ->
            hang $
              pretty ctor
                <> group (foldMap ((line <>) . go . cuteSubExprAgg) paraTypes)
          _ -> oops $ "Cannot find the definition of constructor " <> show ctor
    OADTDef {..} ->
      hang $ "obliv" <+> pretty name <+> rest
      where
        rest = go $ do
          x <- freshNameOrBinder binder
          binderDoc <- cuteBinder x (Just SafeL) (Just ty)
          bodyDoc <- cuteExpr (instantiate1Name x body)
          return $ parens binderDoc <+> equals <> hardline <> bodyDoc
    _ -> oops "builtin functions or constructors in the definitions"
  where
    go = runCuteM options

cuteBinder :: Text -> Maybe Label -> Maybe (Ty Text) -> CuteM (Doc ann)
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
          (colon <> labelDoc <+> align typeDoc)

cuteEnclosedBinder :: Text -> Maybe Label -> Maybe (Ty Text) -> CuteM (Doc ann)
cuteEnclosedBinder x l mTy = do
  doc <- cuteBinder x l mTy
  return $ if isJust mTy then parens doc else doc

cuteTypeBinder ::
  Ty Text ->
  Text ->
  Maybe Label ->
  Ty Text ->
  Binder ->
  CuteM (Doc ann)
cuteTypeBinder super x l ty = \case
  Named _ _ -> go
  Anon ->
    ifM
      (asks optInternalNames)
      go
      ( ifM
          (asks optPrintLabels &&^ return (isJust l))
          ((<>) . parens <$> cuteExpr ty <*> cuteLabel l)
          (cuteSubExpr super ty)
      )
  where
    go = parens <$> cuteBinder x l (Just ty)

cuteLabel :: Maybe Label -> CuteM (Doc ann)
cuteLabel Nothing = ""
cuteLabel (Just SafeL) = "⊥"
cuteLabel (Just LeakyL) = "⊤"

cuteLam :: Bool -> Expr Text -> CuteM (Doc ann)
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
    go :: Expr Text -> CuteM ([Doc ann], Doc ann)
    go Lam {..} = do
      x <- freshNameOrBinder binder
      binderDoc <- cuteEnclosedBinder x label mTy
      (binderDocs, bodyDoc) <- go $ instantiate1Name x body
      return (binderDoc : binderDocs, bodyDoc)
    go Loc {..} = go expr
    go expr = ([],) <$> cuteExpr expr

cuteLet :: Expr Text -> CuteM (Doc ann)
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
    go :: Expr Text -> CuteM ([(Doc ann, Doc ann)], Doc ann)
    go Let {..} = do
      x <- freshNameOrBinder binder
      binderDoc <- cuteBinder x label mTy
      rhsDoc <- cuteExpr rhs
      (bindingDocs, bodyDoc) <- go $ instantiate1Name x body
      return ((binderDoc, rhsDoc) : bindingDocs, bodyDoc)
    go Loc {..} = go expr
    go expr = ([],) <$> cuteExpr expr

cuteIte :: Doc ann -> Expr Text -> Expr Text -> Expr Text -> CuteM (Doc ann)
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

cuteInfix :: Expr Text -> Doc ann -> Expr Text -> Expr Text -> CuteM (Doc ann)
cuteInfix super infixDoc left right = do
  leftDoc <- cuteSubExpr super left
  rightDoc <- cuteSubExpr super right
  return $ hang $ leftDoc <> sep1 (infixDoc <+> rightDoc)

cutePair :: Doc ann -> Expr Text -> Expr Text -> CuteM (Doc ann)
cutePair accent left right = do
  leftDoc <- cuteExpr left
  rightDoc <- cuteExpr right
  return $ cutePairDoc accent leftDoc rightDoc

cutePCase ::
  Doc ann ->
  Expr Text ->
  Binder ->
  Binder ->
  Scope Bool Expr Text ->
  CuteM (Doc ann)
cutePCase accent cond lBinder rBinder body2 = do
  condDoc <- cuteExpr cond
  xl <- freshNameOrBinder lBinder
  xr <- freshNameOrBinder rBinder
  bodyDoc <- cuteExpr $ instantiate2Names xl xr body2
  return $
    cuteCaseDoc
      accent
      False
      condDoc
      [ hang $
          cutePairDoc accent (pretty xl) (pretty xr) <+> "->" <> sep1 bodyDoc
      ]

cutePairDoc :: Doc ann -> Doc ann -> Doc ann -> Doc ann
cutePairDoc accent leftDoc rightDoc =
  accent <> parens (align (leftDoc <> comma <> sep1 rightDoc))

cuteApp :: Doc ann -> [Expr Text] -> CuteM (Doc ann)
cuteApp fnDoc exprs = do
  docs <- mapM cuteSubExprAgg exprs
  return $ hang $ fnDoc <> group (foldMap (line <>) docs)

cuteCaseAlt :: CaseAlt Expr Text -> CuteM (Doc ann)
cuteCaseAlt CaseAlt {..} = do
  xs <- freshNamesOrBinders binders
  bodyDoc <- cuteExpr $ instantiateNames xs body
  return $ cuteAltDoc ctor xs bodyDoc

cuteCaseDoc :: Foldable t => Doc ann -> Bool -> Doc ann -> t (Doc ann) -> Doc ann
cuteCaseDoc accent usePipe condDoc altDocs =
  align $
    accent <> "case" <+> condDoc <+> "of"
      <> ( if usePipe
             then foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
             else foldMap (hardline <>) altDocs
         )
      <> hardline
      <> "end"

cuteAltDocs :: (Functor t) => t (Text, [Text], Doc ann) -> t (Doc ann)
cuteAltDocs = (go <$>)
  where
    go (ctor, xs, bodyDoc) = cuteAltDoc ctor xs bodyDoc

cuteAltDoc :: Text -> [Text] -> Doc ann -> Doc ann
cuteAltDoc ctor xs bodyDoc =
  hang
    ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
        <+> "->" <> sep1 bodyDoc
    )

-- | Add parentheses to the expressions according to their precedence level
cuteSubExpr :: Expr Text -> Expr Text -> CuteM (Doc ann)
cuteSubExpr super sub = cuteSubExprIf sub $ exprLevel super > exprLevel sub

-- | Add parentheses to the expressions more aggressively
cuteSubExprAgg :: Expr Text -> CuteM (Doc ann)
cuteSubExprAgg sub = cuteSubExprIf sub $ exprLevel sub == 0

cuteSubExprIf :: Expr Text -> Bool -> CuteM (Doc ann)
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

freshNameOrBinder :: Binder -> CuteM Text
freshNameOrBinder binder = do
  Options {..} <- ask
  -- Always generate new name even if we use binder
  x <- freshWith $ (optNamePrefix <>) . show
  return $ if optInternalNames then x else toText binder

freshNamesOrBinders :: [Binder] -> CuteM [Text]
freshNamesOrBinders = mapM freshNameOrBinder

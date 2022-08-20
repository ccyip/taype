{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

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
    CuteM(..),
    runCuteM,
    cuteExpr,
    cuteDefs,
    cuteDef,
  )
where

import Bound
import Data.HashMap.Strict ((!?))
import Prettyprinter hiding (hang, indent)
import qualified Prettyprinter as PP
import Taype.Environment
import Taype.Error
import Taype.Fresh
import Taype.Syntax
import Prelude hiding (group)

indentLevel :: Int
indentLevel = 2

hang :: Doc ann -> Doc ann
hang = PP.hang indentLevel

indent :: Doc ann -> Doc ann
indent = PP.indent indentLevel

newtype CuteM a = CuteM { unCuteM :: FreshT (Reader Options) a }
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadReader Options)

runCuteM :: Options -> CuteM a -> a
runCuteM opt (CuteM m) = runReader (runFreshT m) opt

instance IsString a => IsString (CuteM a) where
  fromString = return . fromString

-- | Pretty print class with fresh name generator and environment
class Cute a where
  cute :: a -> CuteM (Doc ann)
  default cute :: Pretty a => a -> CuteM (Doc ann)
  cute = return <$> pretty

instance Cute Int
instance Cute Text

-- | Pretty printer for Taype expressions
cuteExpr :: Expr Text -> CuteM (Doc ann)
cuteExpr V {..} = cute name
cuteExpr GV {..} = cute ref
cuteExpr Pi {..} = do
  x <- freshName
  binderDoc <- cuteBinder x (Just typ)
  bodyDoc <- cuteExpr $ instantiate1Name x body
  return $ parens binderDoc <+> "->" <> line <> bodyDoc
cuteExpr Lam {..} = do
  x <- freshName
  binderDoc <- cuteEnclosedBinder x maybeType
  bodyDoc <- cuteExpr $ instantiate1Name x body
  return $ hang $ backslash <> binderDoc <+> "->" <> group (line <> bodyDoc)
cuteExpr e@App {appKind = Just InfixApp, args = left : right : _, ..} = do
  fnDoc <- cuteSubExprAgg fn
  cuteInfix e fnDoc left right
cuteExpr App {appKind = Just InfixApp} = oops "Not enough infix operands"
cuteExpr App {..} = do
  fnDoc <- cuteSubExprAgg fn
  cuteApp fnDoc args
cuteExpr Let {..} = do
  x <- freshName
  binderDoc <- cuteBinder x maybeType
  rhsDoc <- cuteExpr rhs
  bodyDoc <- cuteExpr $ instantiate1Name x body
  return $
    align $
      "let" <+> hang (binderDoc <+> equals <> softline <> rhsDoc)
        <+> "in" <> group (line <> bodyDoc)
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
  altsDoc <- mapM cuteAlt alts
  return $
    align $
      "case" <+> condDoc <+> "of"
        <> foldMap (hardline <>) (toList altsDoc)
        <> hardline
        <> "end"
  where
    cuteAlt CaseAlt {..} = do
      xs <- freshNames $ length binders
      bodyDoc <- cuteExpr $ instantiateNames xs body
      return $
        pipe
          <+> hang
            ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
                <+> "->" <> softline <> bodyDoc
            )
cuteExpr OIte {..} = cuteIte "~" cond ifTrue ifFalse
cuteExpr e@Prod {..} = cuteInfix e "*" left right
cuteExpr Pair {..} = cutePair "" left right
cuteExpr PCase {..} = cutePCase "" cond body2
cuteExpr e@OProd {..} = cuteInfix e "~*" left right
cuteExpr OPair {..} = cutePair "~" left right
cuteExpr OPCase {..} = cutePCase "~" cond body2
cuteExpr e@OSum {..} = cuteInfix e "~+" left right
cuteExpr OInj {..} = do
  typeDoc <- fromMaybe "" <$> mapM cuteInjType maybeType
  cuteApp ((if tag then "~inl" else "~inr") <> typeDoc) [inj]
  where
    cuteInjType typ = angles <$> cuteExpr typ
cuteExpr OCase {..} = do
  condDoc <- cuteExpr cond
  xl <- freshName
  xr <- freshName
  lBodyDoc <- cuteExpr $ instantiate1Name xl lBody
  rBodyDoc <- cuteExpr $ instantiate1Name xr rBody
  return $
    align $
      "~case" <+> condDoc <+> "of" <> hardline
        <> pipe <+> hang ("~inl" <+> pretty xl <+> "->" <> softline <> lBodyDoc)
        <> hardline
        <> pipe <+> hang ("~inr" <+> pretty xr <+> "->" <> softline <> rBodyDoc)
        <> hardline
        <> "end"
cuteExpr Mux {..} = cuteApp "mux" [cond, ifTrue, ifFalse]
cuteExpr Asc {..} = do
  typeDoc <- cuteExpr typ
  exprDoc <- cuteExpr expr
  return $ parens $ align $ exprDoc <> line <> colon <+> typeDoc
cuteExpr Promote {..} = do
  doc <- cuteSubExprAgg expr
  return $ "!" <> doc
cuteExpr Tape {..} = cuteApp "tape" [expr]
cuteExpr Loc {..} = cuteExpr expr

-- | Cute printer for Taype definitions
cuteDefs :: [Text] -> Env Text -> Doc ann
cuteDefs defs env =
  foldMap (\name -> cuteDef name env <> hardline <> hardline) defs

cuteDef :: Text -> Env Text -> Doc ann
cuteDef name Env {..} =
  case fromMaybe (oops "definition not in context") (gctx !? name) of
    FunDef {..} ->
      "#" <> brackets (pretty attr) <> hardline
        <> "fn"
        <+> pretty name
        <+> colon
        <+> alignType (go $ cuteExpr typ)
        <+> equals
        <> hardline
        <> indent (go $ cuteExpr expr)
    ADTDef {..} ->
      "data" <+> pretty name
        <+> align
          ( group
              ( equals
                  <+> concatWith
                    (\x y -> x <> line <> pipe <+> y)
                    (cuteCtor <$> ctors)
              )
          )
      where
        cuteCtor :: Text -> Doc ann
        cuteCtor ctor = case gctx !? ctor of
          Just (CtorDef {paraTypes}) ->
            hang $
              pretty ctor
                <> group (foldMap ((line <>) . go . cuteSubExprAgg) paraTypes)
          _ -> oops $ "Cannot find the definition of constructor " <> show ctor
    OADTDef {..} ->
      "obliv" <+> pretty name <+> rest
      where
        rest = go $ do
          x <- freshName
          binderDoc <- cuteBinder x (Just typ)
          bodyDoc <- cuteExpr (instantiate1Name x body)
          return $ parens binderDoc <+> equals <> hardline <> bodyDoc
    _ -> oops "builtin functions or constructors in the definitions"
  where
    go = runCuteM options

cuteBinder :: Text -> Maybe (Typ Text) -> CuteM (Doc ann)
cuteBinder x Nothing = cute x
cuteBinder x (Just typ) = do
  typeDoc <- cuteExpr typ
  return $ hang $ pretty x <> softline <> colon <+> alignType typeDoc

cuteEnclosedBinder :: Text -> Maybe (Typ Text) -> CuteM (Doc ann)
cuteEnclosedBinder x maybeType = do
  doc <- cuteBinder x maybeType
  return $ if isJust maybeType then parens doc else doc

cuteIte :: Doc ann -> Expr Text -> Expr Text -> Expr Text -> CuteM (Doc ann)
cuteIte accent cond ifTrue ifFalse = do
  condDoc <- cuteExpr cond
  ifTrueDoc <- cuteExpr ifTrue
  ifFalseDoc <- cuteExpr ifFalse
  return $
    group $
      accent <> "if" <+> condDoc
        <> line
        <> "then" <+> ifTrueDoc
        <> line
        <> "else" <+> ifFalseDoc

cuteInfix :: Expr Text -> Doc ann -> Expr Text -> Expr Text -> CuteM (Doc ann)
cuteInfix super infixDoc left right = do
  leftDoc <- cuteSubExpr super left
  rightDoc <- cuteSubExpr super right
  return $ hang $ leftDoc <> softline <> infixDoc <+> rightDoc

cutePair :: Doc ann -> Expr Text -> Expr Text -> CuteM (Doc ann)
cutePair accent left right = do
  leftDoc <- cuteExpr left
  rightDoc <- cuteExpr right
  return $
    accent <> lparen
      <> align (leftDoc <> comma <> softline <> rightDoc <> rparen)

cutePCase :: Doc ann -> Expr Text -> Scope Bool Expr Text -> CuteM (Doc ann)
cutePCase accent cond body2 = do
  condDoc <- cuteExpr cond
  xl <- freshName
  xr <- freshName
  bodyDoc <- cuteExpr $ instantiate2Names xl xr body2
  return $
    align $
      accent <> "case" <+> condDoc <+> "of" <> hardline
        <> hang
          ( accent <> parens (pretty xl <> comma <+> pretty xr)
              <+> "->" <> softline <> bodyDoc
          )
        <> hardline
        <> "end"

cuteApp :: Doc ann -> [Expr Text] -> CuteM (Doc ann)
cuteApp fnDoc exprs = do
  docs <- mapM cuteSubExprAgg exprs
  return $ hang $ fnDoc <> group (foldMap (line <>) docs)

-- | Add parentheses to the expressions according to their precedence level
cuteSubExpr :: Expr Text -> Expr Text -> CuteM (Doc ann)
cuteSubExpr super sub = cuteSubExprIf sub $ exprLevel super > exprLevel sub

-- | Add parentheses to the expressions more aggressively
cuteSubExprAgg :: Expr Text -> CuteM (Doc ann)
cuteSubExprAgg sub = cuteSubExprIf sub $ exprLevel sub == 0

cuteSubExprIf :: Expr Text -> Bool -> CuteM (Doc ann)
cuteSubExprIf sub b = do
  doc <- cuteExpr sub
  return $ if b then doc else parens doc

alignType :: Doc ann -> Doc ann
alignType = align . group

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
  Loc {..} -> exprLevel expr
  _ -> 90

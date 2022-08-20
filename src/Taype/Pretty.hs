{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Pretty printing.
module Taype.Pretty (prettyExpr, prettyDefs, prettyDef) where

import Bound
import Prettyprinter hiding (hang, indent)
import qualified Prettyprinter as PP
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

-- | Pretty printer for Taype expressions
prettyExpr :: Expr Text -> Fresh (Doc ann)
prettyExpr V {..} = return $ pretty name
prettyExpr GV {..} = return $ pretty ref
prettyExpr Pi {..} = do
  x <- freshName
  binderDoc <- prettyBinder x (Just typ)
  bodyDoc <- prettyExpr $ instantiate1Name x body
  return $ parens binderDoc <+> "->" <> line <> bodyDoc
prettyExpr Lam {..} = do
  x <- freshName
  binderDoc <- prettyEnclosedBinder x maybeType
  bodyDoc <- prettyExpr $ instantiate1Name x body
  return $ hang $ backslash <> binderDoc <+> "->" <> group (line <> bodyDoc)
prettyExpr e@App {appKind = Just InfixApp, args = left : right : _, ..} = do
  fnDoc <- prettySubExprAgg fn
  prettyInfix e fnDoc left right
prettyExpr App {appKind = Just InfixApp} = oops "Not enough infix operands"
prettyExpr App {..} = do
  fnDoc <- prettySubExprAgg fn
  prettyApp fnDoc args
prettyExpr Let {..} = do
  x <- freshName
  binderDoc <- prettyBinder x maybeType
  rhsDoc <- prettyExpr rhs
  bodyDoc <- prettyExpr $ instantiate1Name x body
  return $
    align $
      "let" <+> hang (binderDoc <+> equals <> softline <> rhsDoc)
        <+> "in" <> group (line <> bodyDoc)
prettyExpr TUnit = return "Unit"
prettyExpr VUnit = return "()"
prettyExpr TBool = return "Bool"
prettyExpr OBool = return "~Bool"
prettyExpr BLit {..} = return $ if bLit then "True" else "False"
prettyExpr TInt = return "Int"
prettyExpr OInt = return "~Int"
prettyExpr ILit {..} = return $ pretty iLit
prettyExpr Ite {..} = prettyIte "if" cond ifTrue ifFalse
prettyExpr Case {..} = do
  condDoc <- prettyExpr cond
  altsDoc <- mapM prettyAlt alts
  return $
    align $
      "case" <+> condDoc <+> "of"
        <> foldMap (hardline <>) (toList altsDoc)
        <> hardline
        <> "end"
  where
    prettyAlt CaseAlt {..} = do
      xs <- freshNames $ length binders
      bodyDoc <- prettyExpr $ instantiateNames xs body
      return $
        pipe
          <+> hang
            ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
                <+> "->" <> softline <> bodyDoc
            )
prettyExpr OIte {..} = prettyIte "~if" cond ifTrue ifFalse
prettyExpr e@Prod {..} = prettyInfix e "*" left right
prettyExpr Pair {..} = prettyPair lparen left right
prettyExpr PCase {..} = prettyPCase "case" lparen cond body2
prettyExpr e@OProd {..} = prettyInfix e "~*" left right
prettyExpr OPair {..} = prettyPair ("~" <> lparen) left right
prettyExpr OPCase {..} = prettyPCase "~case" ("~" <> lparen) cond body2
prettyExpr e@OSum {..} = prettyInfix e "~+" left right
prettyExpr OInj {..} = do
  typeDoc <- fromMaybe "" <$> mapM prettyInjType maybeType
  prettyApp ((if tag then "~inl" else "~inr") <> typeDoc) [inj]
  where
    prettyInjType typ = angles <$> prettyExpr typ
prettyExpr OCase {..} = do
  condDoc <- prettyExpr cond
  xl <- freshName
  xr <- freshName
  lBodyDoc <- prettyExpr $ instantiate1Name xl lBody
  rBodyDoc <- prettyExpr $ instantiate1Name xr rBody
  return $
    align $
      "~case" <+> condDoc <+> "of" <> hardline
        <> pipe <+> hang ("~inl" <+> pretty xl <+> "->" <> softline <> lBodyDoc)
        <> hardline
        <> pipe <+> hang ("~inr" <+> pretty xr <+> "->" <> softline <> rBodyDoc)
        <> hardline
        <> "end"
prettyExpr Mux {..} = prettyApp "mux" [cond, ifTrue, ifFalse]
prettyExpr Asc {..} = do
  typeDoc <- prettyExpr typ
  exprDoc <- prettyExpr expr
  return $ parens $ align $ exprDoc <> line <> colon <+> typeDoc
prettyExpr Promote {..} = do
  doc <- prettySubExprAgg expr
  return $ "!" <> doc
prettyExpr Tape {..} = prettyApp "tape" [expr]
prettyExpr Loc {..} = prettyExpr expr

-- | Pretty printer for Taype definitions
prettyDefs :: [NamedDef Text] -> Doc ann
prettyDefs defs = foldMap (prettyDef defs) defs <> hardline

prettyDef :: [NamedDef Text] -> NamedDef Text -> Doc ann
prettyDef defs NamedDef {name, def} = case def of
  FunDef {..} ->
    "#" <> brackets (pretty attr) <> hardline
      <> "fn"
      <+> pretty name
      <+> colon
      <+> alignType (runFresh $ prettyExpr typ)
      <+> equals
      <> hardline
      <> indent (runFresh $ prettyExpr expr)
      <> defSep
  ADTDef {..} ->
    "data" <+> pretty name
      <+> align
        ( group
            ( equals
                <+> concatWith
                  (\x y -> x <> line <> pipe <+> y)
                  (prettyCtors defs <$> ctors)
            )
        )
      <> defSep
  OADTDef {..} ->
    "obliv" <+> pretty name <+> rest
      <> defSep
    where
      rest = runFresh $ do
        x <- freshName
        binderDoc <- prettyBinder x (Just typ)
        bodyDoc <- prettyExpr (instantiate1Name x body)
        return $ parens binderDoc <+> equals <> hardline <> bodyDoc
  -- Do not show builtin definition or constructors
  _ -> mempty
  where
    defSep = hardline <> hardline

prettyCtors :: [NamedDef Text] -> Text -> Doc ann
prettyCtors defs ctor =
  hang $
    pretty ctor <> group (foldMap ((line <>) . runFresh . prettySubExprAgg) types)
  where
    types =
      fromMaybe (oops $ "Cannot find the definition of " <> show ctor) $
        listToMaybe
          [ paraTypes
            | NamedDef {name, def = CtorDef {paraTypes}} <- defs,
              name == ctor
          ]

prettyBinder :: Text -> Maybe (Typ Text) -> Fresh (Doc ann)
prettyBinder x Nothing = return $ pretty x
prettyBinder x (Just typ) = do
  typeDoc <- prettyExpr typ
  return $ hang $ pretty x <> softline <> colon <+> alignType typeDoc

prettyEnclosedBinder :: Text -> Maybe (Typ Text) -> Fresh (Doc ann)
prettyEnclosedBinder x maybeType = do
  doc <- prettyBinder x maybeType
  return $ if isJust maybeType then parens doc else doc

prettyIte :: Doc ann -> Expr Text -> Expr Text -> Expr Text -> Fresh (Doc ann)
prettyIte ifDoc cond ifTrue ifFalse = do
  condDoc <- prettyExpr cond
  ifTrueDoc <- prettyExpr ifTrue
  ifFalseDoc <- prettyExpr ifFalse
  return $
    group $
      ifDoc <+> condDoc
        <> line
        <> "then" <+> ifTrueDoc
        <> line
        <> "else" <+> ifFalseDoc

prettyInfix :: Expr Text -> Doc ann -> Expr Text -> Expr Text -> Fresh (Doc ann)
prettyInfix super infixDoc left right = do
  leftDoc <- prettySubExpr super left
  rightDoc <- prettySubExpr super right
  return $ hang $ leftDoc <> softline <> infixDoc <+> rightDoc

prettyPair :: Doc ann -> Expr Text -> Expr Text -> Fresh (Doc ann)
prettyPair lDoc left right = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ lDoc <> align (leftDoc <> comma <> softline <> rightDoc <> rparen)

prettyPCase :: Doc ann -> Doc ann -> Expr Text -> Scope Bool Expr Text -> Fresh (Doc ann)
prettyPCase caseDoc lDoc cond body2 = do
  condDoc <- prettyExpr cond
  xl <- freshName
  xr <- freshName
  bodyDoc <- prettyExpr $ instantiate2Names xl xr body2
  return $
    align $
      caseDoc <+> condDoc <+> "of" <> hardline
        <> hang
          ( lDoc <> pretty xl <> comma <+> pretty xr <> rparen
              <+> "->" <> softline <> bodyDoc
          )
        <> hardline
        <> "end"

prettyApp :: Doc ann -> [Expr Text] -> Fresh (Doc ann)
prettyApp fnDoc exprs = do
  docs <- mapM prettySubExprAgg exprs
  return $ hang $ fnDoc <> group (foldMap (line <>) docs)

-- | Add parentheses to the expressions according to their precedence level
prettySubExpr :: Expr Text -> Expr Text -> Fresh (Doc ann)
prettySubExpr super sub = prettySubExprIf sub $ exprLevel super > exprLevel sub

-- | Add parentheses to the expressions more aggressively
prettySubExprAgg :: Expr Text -> Fresh (Doc ann)
prettySubExprAgg sub = prettySubExprIf sub $ exprLevel sub == 0

prettySubExprIf :: Expr Text -> Bool -> Fresh (Doc ann)
prettySubExprIf sub b = do
  doc <- prettyExpr sub
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

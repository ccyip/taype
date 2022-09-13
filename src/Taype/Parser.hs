{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Parser for the taype language.
module Taype.Parser (parse) where

import Control.Applicative.Combinators (choice)
import Control.Applicative.Combinators.NonEmpty (sepBy1)
import Control.Monad.Error.Class
import Data.List.NonEmpty (some1)
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Error
import Taype.Lexer (LocatedToken (..), Token)
import qualified Taype.Lexer as L
import Taype.Prelude
import Taype.Syntax
import Text.Earley hiding (Parser, token)

type Parser r = Prod r Text LocatedToken

pLocatedTerminal :: (Token -> Maybe a) -> Parser r (Int, a)
pLocatedTerminal match = terminal match'
  where
    match' LocatedToken {..} = (offset,) <$> match token

pLocatedToken :: Token -> Parser r Int
pLocatedToken expected = terminal match
  where
    match LocatedToken {..}
      | expected == token = Just offset
      | otherwise = Nothing

pToken :: Token -> Parser r ()
pToken = void <$> pLocatedToken

pLocatedIdent :: Parser r (Int, Text)
pLocatedIdent = pLocatedTerminal match
  where
    match (L.Ident name) = Just name
    match _ = Nothing

pIdent :: Parser r Text
pIdent = snd <$> pLocatedIdent

pLocatedBinder :: Parser r (Int, Binder)
pLocatedBinder =
  choice
    [ (,Anon) <$> pLocatedToken L.Underscore,
      (\(loc, name) -> (loc, Named loc name)) <$> pLocatedIdent
    ]

pBinder :: Parser r Binder
pBinder = snd <$> pLocatedBinder

pLocatedOInj :: Parser r (Int, Bool)
pLocatedOInj = pLocatedTerminal match
  where
    match (L.OInj b) = Just b
    match _ = Nothing

pLocatedBLit :: Parser r (Int, Bool)
pLocatedBLit = pLocatedTerminal match
  where
    match (L.BLit b) = Just b
    match _ = Nothing

pLocatedILit :: Parser r (Int, Int)
pLocatedILit = pLocatedTerminal match
  where
    match (L.ILit i) = Just i
    match _ = Nothing

pLocatedInfix :: [Text] -> Parser r (Int, Text)
pLocatedInfix ops =
  choice $
    ops <&> \op -> (,op) <$> pLocatedToken (L.Infix op)

getLoc :: Expr a -> Int
getLoc Loc {loc} = loc
getLoc _ = oops "Location not available"

infixToTypeFormer :: Text -> (Ty a -> Ty a -> Ty a)
infixToTypeFormer x | x == prodTCtor = Prod
infixToTypeFormer x | x == oblivName prodTCtor = OProd
infixToTypeFormer x | x == oblivName sumTCtor = OSum
infixToTypeFormer _ = oops "unknown type infix"

-- | The grammar for taype language
grammar :: Grammar r (Parser r [(Text, Def Text)])
grammar = mdo
  -- A program is a list of global definitions.
  pProg <- rule $ many pDef

  -- Global definition
  pDef <-
    rule $
      choice
        [ -- ADT definition
          do
            pToken L.Data
            ~(loc, name) <- pLocatedIdent
            pToken L.Equals
            let pCtor = (,) <$> pIdent <*> many pAtomType
            ctors <- pCtor `sepBy1` pToken L.Bar
            return (name, ADTDef {..}),
          -- Oblivious ADT definition
          do
            pToken L.Obliv
            ~(loc, name) <- pLocatedIdent
            let pArg = do
                  pToken L.LParen
                  binder <- pBinder
                  pToken L.Colon
                  ty <- pType
                  pToken L.RParen
                  return (binder, ty)
            ~(binder, ty) <- pArg
            pToken L.Equals
            body <- pType
            return
              ( name,
                OADTDef
                  { bnd = abstractBinder binder body,
                    binder = Just binder,
                    ..
                  }
              ),
          -- Function definition
          do
            let pAttr = do
                  pToken L.LAttr
                  attr <-
                    choice
                      [ SectionAttr <$ pToken (L.Ident "section"),
                        RetractionAttr <$ pToken (L.Ident "retraction"),
                        SafeAttr <$ pToken (L.Ident "safe"),
                        LeakyAttr <$ pToken (L.Ident "leaky")
                      ]
                  pToken L.RBrace
                  return attr
            attr <- optional pAttr
            pToken L.Fn
            ~(loc, name) <- pLocatedIdent
            pToken L.Colon
            ty <- pType
            pToken L.Equals
            expr <- pExpr
            return
              ( name,
                FunDef
                  { attr = fromMaybe LeakyAttr attr,
                    label = Nothing,
                    ..
                  }
              )
        ]

  -- Expression
  pExpr <-
    rule $
      choice
        [ -- Lambda abstraction
          do
            pToken L.Lambda
            args <- some1 pLocatedFunArg
            pToken L.Arrow
            body <- pExpr
            return $
              let go ((loc, binder), mTy) body' =
                    Loc {expr = lam_ binder mTy body', ..}
               in foldr go body args,
          -- Let
          pLet pExpr,
          -- If conditional
          pIf ite_ L.If pExpr,
          -- Oblivious (leaky) if conditional
          pIf oite_ L.OIf pExpr,
          -- Product elimination
          pPCase pcase_ L.Case L.LParen pExpr,
          -- Oblivious product elimination
          pPCase opcase_ L.OCase L.LOParen pExpr,
          -- Case analysis
          pCase pExpr,
          -- Oblivious (leaky) case analysis
          do
            loc <- pLocatedToken L.OCase
            cond <- pExpr
            pToken L.Of
            optional $ pToken L.Bar
            pToken $ L.OInj True
            lBinder <- pBinder
            pToken L.Arrow
            lBody <- pExpr
            pToken L.Bar
            pToken $ L.OInj False
            rBinder <- pBinder
            pToken L.Arrow
            rBody <- pExpr
            pToken L.End
            return Loc {expr = ocase_ cond lBinder lBody rBinder rBody, ..},
          -- Next precedence
          pCompareExpr
        ]

  let pInfixExpr = pInfix $ \ref left right -> app_ (GV {..}) [left, right]

  -- Comparative infix
  pCompareExpr <-
    rule $
      choice
        [ pInfixExpr
            ["==", "<=", oblivName "==", oblivAccent <> "<="]
            pAddExpr
            pAddExpr,
          pAddExpr
        ]

  -- Left-associative additive infix
  pAddExpr <-
    rule $
      choice
        [ pInfixExpr
            ["+", "-", oblivName "+", oblivAccent <> "-"]
            pAddExpr
            pMulExpr,
          pMulExpr
        ]

  -- Left-associative multiplicative infix
  --
  -- We do not have any of these at the moment, but we will probably add at
  -- least integer multiplication in the future.
  pMulExpr <- rule pAppExpr

  -- Application expression
  pAppExpr <-
    rule $
      choice
        [ -- Application
          pApp app_ pAtomExpr,
          -- MUX
          do
            loc <- pLocatedToken L.Mux
            cond <- pAtomExpr
            left <- pAtomExpr
            right <- pAtomExpr
            return Loc {expr = Mux {..}, ..},
          -- Oblivious injection
          do
            ~(loc, tag) <- pLocatedOInj
            mTy <- optional $ do
              pToken L.LAngle
              ty <- pType
              pToken L.RAngle
              return ty
            inj <- pAtomExpr
            return Loc {expr = OInj {..}, ..},
          -- Tape
          do
            loc <- pLocatedToken L.Tape
            expr <- pAtomExpr
            return Loc {expr = Tape {..}, ..},
          -- Next precedence
          pAtomExpr
        ]

  -- Atomic expression
  pAtomExpr <-
    rule $
      choice
        [ -- Unit value
          pLocatedToken L.LParen <* pToken L.RParen <&> \loc ->
            Loc {expr = VUnit, ..},
          -- Boolean literal
          pLocatedBLit <&> \(loc, bLit) -> Loc {expr = BLit {..}, ..},
          -- Integer literal
          pLocatedILit <&> \(loc, iLit) -> Loc {expr = ILit {..}, ..},
          -- Variable
          pLocatedIdent <&> \(loc, name) -> Loc {expr = V {..}, ..},
          -- Pair
          pPair Pair L.LParen,
          -- Oblivious pair
          pPair OPair L.LOParen,
          -- Ascription
          pParen $ do
            expr <- pExpr
            loc <- pLocatedToken L.Colon
            ty <- pType
            return Loc {expr = Asc {..}, ..},
          -- Parenthesized expression
          pParen pExpr
        ]

  -- Type
  --
  -- Technically we can have one production rule for both expressions and types.
  -- However, separating them allows us to easily disambiguate term-level and
  -- type-level operations.
  pType <-
    rule $
      choice
        [ -- Dependent function type
          do
            ~(loc, binder, ty) <-
              choice
                [ do
                    ty <- pProdType
                    return (getLoc ty, Anon, ty),
                  do
                    loc <- pLocatedToken L.LParen
                    binder <- pBinder
                    pToken L.Colon
                    ty <- pType
                    pToken L.RParen
                    return (loc, binder, ty)
                ]
            pToken L.Arrow
            body <- pType
            return Loc {expr = pi_ binder ty body, ..},
          -- Let
          pLet pType,
          -- If conditional
          pIf ite_ L.If pType,
          -- Product elimination
          pPCase pcase_ L.Case L.LParen pType,
          -- Case analysis
          pCase pType,
          -- Next precedence
          pProdType
        ]

  let pInfixType = pInfix infixToTypeFormer

  -- Right-associative product type
  pProdType <-
    rule $ choice [pInfixType [prodTCtor] pOSumType pProdType, pOSumType]

  -- Right-associative oblivious sum type
  pOSumType <-
    rule $
      choice
        [ pInfixType [oblivName sumTCtor] pOProdType pOSumType,
          pOProdType
        ]

  -- Right-associative oblivious product type
  pOProdType <-
    rule $
      choice
        [ pInfixType [oblivName prodTCtor] pAppType pOProdType,
          pAppType
        ]

  -- Type application
  pAppType <-
    rule $
      choice
        [ pApp app_ pAtomType,
          -- Next precedence
          pAtomType
        ]

  -- Atomic type
  pAtomType <-
    rule $
      choice
        [ -- Unit type
          pLocatedToken L.TUnit <&> \loc -> Loc {expr = TUnit, ..},
          -- Boolean type
          pLocatedToken L.TBool <&> \loc -> Loc {expr = TBool, ..},
          -- Oblivious Boolean type
          pLocatedToken L.OBool <&> \loc -> Loc {expr = OBool, ..},
          -- Integer type
          pLocatedToken L.TInt <&> \loc -> Loc {expr = TInt, ..},
          -- Oblivious integer type
          pLocatedToken L.OInt <&> \loc -> Loc {expr = OInt, ..},
          -- Variable
          pLocatedIdent <&> \(loc, name) -> Loc {expr = V {..}, ..},
          -- Parenthesized type
          pParen pType
        ]

  -- Common production rules
  let -- Let-like binding
      pLet pBody = do
        let pBinding = do
              binder <- pLocatedBinder
              mTy <- optional $ pToken L.Colon *> pType
              pToken L.Equals
              rhs <- pExpr
              return (binder, mTy, rhs)
        pToken L.Let
        bindings <- some1 pBinding
        pToken L.In
        body <- pBody
        return $
          let go ((loc, binder), mTy, rhs) body' =
                Loc {expr = let_ binder mTy rhs body', ..}
           in foldr go body bindings
      -- If-like conditional
      pIf former ifToken pBranch = do
        loc <- pLocatedToken ifToken
        cond <- pExpr
        pToken L.Then
        left <- pBranch
        pToken L.Else
        right <- pBranch
        return Loc {expr = former cond left right, ..}
      -- Product-like elimination
      pPCase former caseToken openParenToken pBody = do
        loc <- pLocatedToken caseToken
        cond <- pExpr
        pToken L.Of
        optional $ pToken L.Bar
        pToken openParenToken
        left <- pBinder
        pToken L.Comma
        right <- pBinder
        pToken L.RParen
        pToken L.Arrow
        body <- pBody
        pToken L.End
        return Loc {expr = former cond left right body, ..}
      -- Public case-like elimination
      pCase pBody = do
        let pAlt = do
              ctor <- pIdent
              binders <- many pBinder
              pToken L.Arrow
              body <- pBody
              return (ctor, binders, body)
        loc <- pLocatedToken L.Case
        cond <- pExpr
        pToken L.Of
        optional $ pToken L.Bar
        alts <- pAlt `sepBy1` pToken L.Bar
        pToken L.End
        return Loc {expr = case_ cond alts, ..}
      -- Pair-like
      pPair former openParenToken = do
        pToken openParenToken
        prefix <- some1 $ pExpr <* pToken L.Comma
        end <- pExpr
        pToken L.RParen
        return $
          let go left right = Loc {expr = former left right, loc = getLoc left}
           in foldr go end prefix
      -- Application-like
      pApp former pFn = do
        fn <- pFn
        args <- some1 pAtomExpr
        return $ Loc {loc = getLoc fn, expr = former fn $ toList args}
      -- Parenthesized
      pParen pBody = pToken L.LParen *> pBody <* pToken L.RParen
      -- Infix
      pInfix former ops pLeft pRight = do
        left <- pLeft
        ~(_, name) <- pLocatedInfix ops
        right <- pRight
        return Loc {expr = former name left right, loc = getLoc left, ..}

  -- Function argument
  pLocatedFunArg <-
    rule $
      choice
        [ (,Nothing) <$> pLocatedBinder,
          do
            pToken L.LParen
            binder <- pLocatedBinder
            pToken L.Colon
            ty <- pType
            pToken L.RParen
            return (binder, Just ty),
          pToken L.LParen *> pLocatedFunArg <* pToken L.RParen
        ]

  return pProg

-- | Main parser
parse :: MonadError Err m => [LocatedToken] -> m [(Text, Def Text)]
parse tokens =
  case fullParses (parser grammar) tokens of
    ([], rpt) -> throwError $ renderParserError rpt
    ([defs], _) -> return defs
    (parses, _) ->
      oops $ "Ambiguous grammar: there are " <> show (length parses) <> " parses!"

renderParserError :: Report Text [LocatedToken] -> Err
renderParserError Report {..} =
  Err
    { errLoc = maybe (-1) offset unexpectedToken,
      errCategory = "Parsing Error",
      errMsg
    }
  where
    unexpectedToken = listToMaybe unconsumed
    errMsg = maybe "Unexpected end of input" showUnexpected unexpectedToken
    showUnexpected LocatedToken {..} = "Unexpected" <+> renderToken token

renderToken :: Token -> Doc
renderToken = \case
  L.Lambda -> "lambda abstraction"
  L.Underscore -> squotes "_"
  L.Arrow -> dquotes "->"
  L.Equals -> squotes equals
  L.Colon -> squotes colon
  L.Bar -> squotes pipe
  L.Comma -> squotes comma
  L.LAngle -> squotes "<"
  L.RAngle -> squotes ">"
  L.LAttr -> dquotes $ "#" <> lbracket
  L.RBrace -> squotes rbracket
  L.LParen -> squotes lparen
  L.LOParen -> dquotes $ pretty oblivAccent <> lparen
  L.RParen -> squotes rparen
  L.TUnit -> "Unit"
  L.TBool -> pretty boolTCtor
  L.OBool -> pretty $ oblivName boolTCtor
  L.BLit _ -> "boolean literal"
  L.TInt -> "Int"
  L.OInt -> pretty $ oblivName "Int"
  L.ILit _ -> "integer literal"
  L.Data -> "data"
  L.Obliv -> "obliv"
  L.Fn -> "fn"
  L.Let -> "let"
  L.In -> "in"
  L.If -> "if"
  L.OIf -> pretty $ oblivName "if"
  L.Then -> "then"
  L.Else -> "else"
  L.Mux -> "mux"
  L.Case -> "case"
  L.OCase -> pretty $ oblivName "case"
  L.Of -> "of"
  L.End -> "end"
  L.Tape -> "tape"
  L.OInj tag -> pretty $ oblivName $ if tag then "inl" else "inr"
  L.Ident ident -> "identifier" <+> dquotes (pretty ident)
  L.Infix ident -> "infix" <+> dquotes (pretty ident)

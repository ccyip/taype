{-# LANGUAGE ApplicativeDo #-}
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
-- Parser for taype.
module Taype.Parser (parse) where

import Bound
import Control.Applicative.Combinators (choice)
import Control.Applicative.Combinators.NonEmpty (sepBy1)
import Data.List.NonEmpty (some1)
import Taype.Error
import Taype.Lexer (LocatedToken (..), Token)
import qualified Taype.Lexer as L
import Taype.Syntax
import Text.Earley hiding (Parser, token)

type Parser r = Prod r Text LocatedToken

pTerminal :: (Token -> Maybe a) -> Parser r a
pTerminal match = terminal match'
  where
    match' LocatedToken {..} = match token

pToken :: Token -> Parser r ()
pToken expected = void $ satisfy match
  where
    match LocatedToken {..} = expected == token

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

matchIdent :: Token -> Maybe Text
matchIdent (L.Ident name) = Just name
matchIdent _ = Nothing

pIdent :: Parser r Text
pIdent = pTerminal matchIdent

pLocatedIdent :: Parser r (Int, Text)
pLocatedIdent = pLocatedTerminal matchIdent

-- Binders are always located
pBinder :: Parser r Binder
pBinder =
  choice
    [ Anon <$ pToken L.Underscore,
      uncurry Named <$> pLocatedIdent
    ]

matchOInj :: Token -> Maybe Bool
matchOInj (L.OInj b) = Just b
matchOInj _ = Nothing

pLocatedOInj :: Parser r (Int, Bool)
pLocatedOInj = pLocatedTerminal matchOInj

matchBLit :: Token -> Maybe Bool
matchBLit (L.BLit b) = Just b
matchBLit _ = Nothing

pLocatedBLit :: Parser r (Int, Bool)
pLocatedBLit = pLocatedTerminal matchBLit

matchILit :: Token -> Maybe Int
matchILit (L.ILit i) = Just i
matchILit _ = Nothing

pLocatedILit :: Parser r (Int, Int)
pLocatedILit = pLocatedTerminal matchILit

pLocatedInfix :: [Text] -> Parser r (Int, Text)
pLocatedInfix ops =
  choice $
    ops <&> \op -> (,op) <$> pLocatedToken (L.Infix op)

getLoc :: Expr a -> Int
getLoc Loc {loc} = loc
getLoc _ = oops "Location not available"

infixToTypeFormer :: Text -> (Typ a -> Typ a -> Typ a)
infixToTypeFormer "*" = Prod
infixToTypeFormer "~*" = OProd
infixToTypeFormer "~+" = OSum
infixToTypeFormer _ = oops "unknown type infix"

grammar :: Grammar r (Parser r [NamedDef Text])
grammar = mdo
  -- A program is a list of global definitions
  pProg <- rule $ concat <$> many pDef

  -- Global definition
  pDef <-
    rule $
      choice
        [ -- ADT definition
          do
            pToken L.Data
            ~(loc, name) <- pLocatedIdent
            pToken L.Equals
            let pCtor = (,) <$> pLocatedIdent <*> many pAtomType
            ctors <- pCtor `sepBy1` pToken L.Bar
            return $
              let ctorDefs = toList $ ctorToDef <$> ctors
                  ctorToDef ((ctorLoc, ctorName), paraTypes) =
                    NamedDef
                      { name = ctorName,
                        loc = ctorLoc,
                        def = CtorDef {dataType = name, ..}
                      }
               in NamedDef
                    { def = ADTDef {ctors = snd . fst <$> ctors},
                      ..
                    } :
                  ctorDefs,
          -- Oblivious ADT definition
          do
            pToken L.Obliv
            ~(loc, name) <- pLocatedIdent
            let pArg = do
                  pToken L.LParen
                  argName <- pIdent
                  pToken L.Colon
                  typ <- pType
                  pToken L.RParen
                  return (argName, typ)
            -- Only support one argument for oblivious type at the moment
            ~(argName, typ) <- pArg
            pToken L.Equals
            body <- pType
            return $
              one $
                NamedDef
                  { def =
                      OADTDef {body = abstract1 argName body, ..},
                    ..
                  },
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
            typ <- pType
            pToken L.Equals
            expr <- pExpr
            return $
              one $
                NamedDef
                  { def =
                      FunDef
                        { attr = fromMaybe LeakyAttr attr,
                          label = Nothing,
                          ..
                        },
                    ..
                  }
        ]

  -- Expression
  pExpr <-
    rule $
      choice
        [ -- Lambda abstraction
          do
            loc <- pLocatedToken L.Lambda
            args <- some1 pFunArg
            pToken L.Arrow
            body <- pExpr
            return Loc {expr = lams_ args body, ..},
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

  let pInfixExpr = pInfix $ \ref left right -> iapp_ (GV {..}) [left, right]

  -- Comparative infix
  pCompareExpr <-
    rule $ choice [pInfixExpr ["==", "~=", "<=", "~<="] pAddExpr pAddExpr, pAddExpr]

  -- Left-associative additive infix
  pAddExpr <-
    rule $ choice [pInfixExpr ["+", "-", "~+", "~-"] pAddExpr pMulExpr, pMulExpr]

  -- Left-associative multiplicative infix. We do not have any of these at the
  -- moment, but we will probably have at least integer multiplication in the
  -- future
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
            ifTrue <- pAtomExpr
            ifFalse <- pAtomExpr
            return Loc {expr = Mux {..}, ..},
          -- Oblivious injection
          do
            ~(loc, tag) <- pLocatedOInj
            maybeType <- optional $ do
              pToken L.LAngle
              typ <- pType
              pToken L.RAngle
              return typ
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
            typ <- pType
            return Loc {expr = Asc {..}, ..},
          -- Parenthesized expression
          pParen pExpr
        ]

  -- Type. Technically we can have one production rule for both expressions and
  -- types. However, separating them allows us to easily disambiguate term-level
  -- and type-level operations.
  pType <-
    rule $
      choice
        [ -- Dependent function type
          do
            ~(binder, typ) <-
              choice
                [ (Anon,) <$> pProdType,
                  do
                    pToken L.LParen
                    binder <- pBinder
                    pToken L.Colon
                    typ <- pProdType
                    pToken L.RParen
                    return (binder, typ)
                ]
            loc <- pLocatedToken L.Arrow
            body <- pType
            return Loc {expr = pi_ binder typ body, ..},
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
    rule $ choice [pInfixType ["*"] pOSumType pProdType, pOSumType]

  -- Right-associative oblivious sum type
  pOSumType <-
    rule $ choice [pInfixType ["~+"] pOProdType pOSumType, pOProdType]

  -- Right-associative oblivious product type
  pOProdType <-
    rule $ choice [pInfixType ["~*"] pAppType pOProdType, pAppType]

  -- Type application
  pAppType <-
    rule $
      choice
        [ pApp tapp_ pAtomType,
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
          pLocatedIdent <&> \(loc, ref) -> Loc {expr = GV {..}, ..},
          -- Parenthesized type
          pParen pType
        ]

  -- Common production rules
  let -- Let-like binding
      pLet pBody = do
        let pBinding = do
              binder <- pBinder
              maybeType <- optional $ pToken L.Colon *> pType
              pToken L.Equals
              rhs <- pExpr
              return (binder, maybeType, rhs)
        loc <- pLocatedToken L.Let
        bindings <- some1 pBinding
        pToken L.In
        body <- pBody
        return Loc {expr = lets_ bindings body, ..}
      -- If-like conditional
      pIf former ifToken pBranch = do
        loc <- pLocatedToken ifToken
        cond <- pExpr
        pToken L.Then
        ifTrue <- pBranch
        pToken L.Else
        ifFalse <- pBranch
        return Loc {expr = former cond ifTrue ifFalse, ..}
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
        prefix <- some1 $ flip (,) <$> pExpr <*> pLocatedToken L.Comma
        end <- pExpr
        pToken L.RParen
        return $
          let go (loc, left) right = Loc {expr = former left right, ..}
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
        ~(loc, name) <- pLocatedInfix ops
        right <- pRight
        return Loc {expr = former name left right, ..}

  -- Function argument
  pFunArg <-
    rule $
      choice
        [ (,Nothing) <$> pBinder,
          do
            pToken L.LParen
            binder <- pBinder
            pToken L.Colon
            typ <- pType
            pToken L.RParen
            return (binder, Just typ),
          pToken L.LParen *> pFunArg <* pToken L.RParen
        ]

  return pProg

-- | Main parser
parse :: [LocatedToken] -> Either LocatedError [NamedDef a]
parse tokens =
  case fullParses (parser grammar) tokens of
    ([], rpt) -> Left $ renderParserError rpt
    ([defs], _) -> Right $ close <$> defs
    (parses, _) ->
      oops $ "Ambiguous grammar: there are " <> show (length parses) <> " parses!"
  where
    close NamedDef {..} = NamedDef {def = def >>>= GV, ..}

renderParserError :: Report Text [LocatedToken] -> LocatedError
renderParserError Report {..} =
  LocatedError
    { errLoc = maybe (-1) offset unexpectedToken,
      errCategory = "Parsing Error",
      errMsg
    }
  where
    unexpectedToken = listToMaybe unconsumed
    errMsg = maybe "unexpected end of input" showUnexpected unexpectedToken
    showUnexpected LocatedToken {..} = "unexpected " <> renderToken token

renderToken :: Token -> Text
renderToken = \case
  L.Lambda -> "lambda abstraction"
  L.Underscore -> "'_'"
  L.Arrow -> "\"->\""
  L.Equals -> "'='"
  L.Colon -> "':'"
  L.Bar -> "'|'"
  L.Comma -> "','"
  L.LAngle -> "'<'"
  L.RAngle -> "'>'"
  L.LAttr -> "\"#[\""
  L.RBrace -> "']'"
  L.LParen -> "'('"
  L.LOParen -> "\"~(\""
  L.RParen -> "')'"
  L.TUnit -> "Unit"
  L.TBool -> "Bool"
  L.OBool -> "~Bool"
  L.BLit _ -> "boolean literal"
  L.TInt -> "Int"
  L.OInt -> "~Int"
  L.ILit _ -> "integer literal"
  L.Data -> "data"
  L.Obliv -> "obliv"
  L.Fn -> "fn"
  L.Let -> "let"
  L.In -> "in"
  L.If -> "if"
  L.OIf -> "~if"
  L.Then -> "then"
  L.Else -> "else"
  L.Mux -> "mux"
  L.Case -> "case"
  L.OCase -> "~case"
  L.Of -> "of"
  L.End -> "end"
  L.Tape -> "tape"
  L.OInj tag -> if tag then "~inl" else "~inr"
  L.Ident ident -> "identifier \"" <> ident <> "\""
  L.Infix ident -> "infix \"" <> ident <> "\""

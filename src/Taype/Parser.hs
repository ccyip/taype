{-# LANGUAGE ApplicativeDo #-}
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

matchBinder :: Token -> Maybe Binder
matchBinder L.Underscore = Just Anon
matchBinder token = Named <$> matchIdent token

pBinder :: Parser r Binder
pBinder = pTerminal matchBinder

pLocatedBinder :: Parser r (Int, Binder)
pLocatedBinder = pLocatedTerminal matchBinder

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
            loc <- pLocatedToken L.Data
            name <- pIdent
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
            loc <- pLocatedToken L.Obliv
            name <- pIdent
            let pArg = do
                  pToken L.OpenParen
                  argName <- pIdent
                  pToken L.Colon
                  typ <- pType
                  pToken L.CloseParen
                  return (argName, typ)
            -- Only support one argument for oblivious type at the moment
            arg <- pArg
            pToken L.Equals
            body <- pType
            return $
              one $
                let (argName, typ) = arg
                 in NamedDef
                      { def =
                          OADTDef {body = abstract1 argName body, ..},
                        ..
                      },
          -- Function definition
          do
            let pAttr = do
                  pToken L.OpenAttr
                  attr <-
                    choice
                      [ SectionAttr <$ pToken (L.Ident "section"),
                        RetractionAttr <$ pToken (L.Ident "retraction"),
                        SafeAttr <$ pToken (L.Ident "safe"),
                        LeakyAttr <$ pToken (L.Ident "leaky")
                      ]
                  pToken L.CloseBrace
                  return attr
            attr <- optional pAttr
            loc <- pLocatedToken L.Fn
            name <- pIdent
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

  -- Common production rules
  let -- Let-like binding
      pLet pBody = do
        let pBinding = do
              binder <- pLocatedBinder
              maybeType <- optional $ pToken L.Colon *> pType
              pToken L.Equals
              rhs <- pExpr
              return (binder, maybeType, rhs)
        pToken L.Let
        bindings <- some1 pBinding
        pToken L.In
        body0 <- pBody
        return $
          let go ((loc, binder), maybeType, rhs) body =
                Loc {expr = let_ binder maybeType rhs body, ..}
           in foldr go body0 bindings
      -- If-like conditional
      pIf ifToken pBranch former = do
        loc <- pLocatedToken ifToken
        cond <- pExpr
        pToken L.Then
        ifTrue <- pBranch
        pToken L.Else
        ifFalse <- pBranch
        return Loc {expr = former cond ifTrue ifFalse, ..}
      -- Product-like elimination
      pPCase caseToken openParenToken pBody former = do
        loc <- pLocatedToken caseToken
        cond <- pExpr
        pToken L.Of
        pToken L.Bar
        pToken openParenToken
        left <- pBinder
        pToken L.Comma
        right <- pBinder
        pToken L.CloseParen
        pToken L.Arrow
        body <- pBody
        return Loc {expr = former cond left right body, ..}
      -- Public case-like elimination
      pCase pBody = do
        let pAlt = do
              pToken L.Bar
              ctor <- pIdent
              binders <- many pBinder
              pToken L.Arrow
              body <- pBody
              return (ctor, binders, body)
        loc <- pLocatedToken L.Case
        cond <- pExpr
        pToken L.Of
        alts <- some1 pAlt
        return Loc {expr = case_ cond alts, ..}
      -- Pair-like
      pPair openParenToken former = do
        pToken openParenToken
        prefix <- some1 $ flip (,) <$> pExpr <*> pLocatedToken L.Comma
        end <- pExpr
        pToken L.CloseParen
        return $
          let go (loc, left) right = Loc {expr = former left right, ..}
           in foldr go end prefix
      -- Application-like
      pApp pFn former = do
        fn <- pFn
        args <- many pAtomExpr
        return $ case args of
          [] -> fn
          _ -> Loc {loc = getLoc fn, expr = former fn args}
      -- Parenthesized
      pParen pBody = pToken L.OpenParen *> pBody <* pToken L.CloseParen

  -- Expression
  pExpr <-
    rule $
      choice
        [ -- Lambda abstraction
          do
            pToken L.Lambda
            args <- some1 pFunArg
            pToken L.Arrow
            body0 <- pExpr
            return $
              let go ((loc, binder), maybeType) body =
                    Loc {expr = lam_ binder maybeType body, ..}
               in foldr go body0 args,
          -- Let
          pLet pExpr,
          -- If conditional
          pIf L.If pExpr ite_,
          -- Oblivious (leaky) if conditional
          pIf L.OIf pExpr oite_,
          -- Product elimination
          pPCase L.Case L.OpenParen pExpr pcase_,
          -- Oblivious product elimination
          pPCase L.OCase L.OpenOParen pExpr opcase_,
          -- Case analysis
          pCase pExpr,
          -- Oblivious (leaky) case analysis
          do
            loc <- pLocatedToken L.OCase
            cond <- pExpr
            pToken L.Of
            pToken L.Bar
            pToken $ L.OInj True
            lBinder <- pBinder
            pToken L.Arrow
            lBody <- pExpr
            pToken L.Bar
            pToken $ L.OInj False
            rBinder <- pBinder
            pToken L.Arrow
            rBody <- pExpr
            return Loc {expr = ocase_ cond lBinder lBody rBinder rBody, ..},
          -- Ascription
          do
            expr <- pCompareExpr
            loc <- pLocatedToken L.Colon
            typ <- pType
            return Loc {expr = Asc {..}, ..},
          -- Next precedence
          pCompareExpr
        ]

  -- Type. Technically we can have one production rule for both expressions and
  -- types. However, separating them allows us to easily disambiguate term-level
  -- and type-level operations.
  pType <-
    rule $
      choice
        [ -- Dependent function type
          do
            typeArg <-
              choice
                [ (Anon,) <$> pProdType,
                  do
                    pToken L.OpenParen
                    binder <- pBinder
                    pToken L.Colon
                    typ <- pProdType
                    pToken L.CloseParen
                    return (binder, typ)
                ]
            loc <- pLocatedToken L.Arrow
            body <- pType
            return $
              let (binder, typ) = typeArg
               in Loc {expr = pi_ binder typ body, ..},
          -- Let
          pLet pType,
          -- If conditional
          pIf L.If pType ite_,
          -- Product elimination
          pPCase L.Case L.OpenParen pType pcase_,
          -- Case analysis
          pCase pType,
          -- Next precedence
          pProdType
        ]

  let pInfixExpr ops pLeft pRight = do
        left <- pLeft
        op <- pLocatedInfix ops
        right <- pRight
        return $
          let (loc, ref) = op
           in Loc {expr = iapp_ (GV {..}) [left, right], ..}

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
          pApp pAtomExpr app_,
          -- MUX
          do
            loc <- pLocatedToken L.Mux
            cond <- pAtomExpr
            ifTrue <- pAtomExpr
            ifFalse <- pAtomExpr
            return Loc {expr = Mux {..}, ..},
          -- Oblivious injection
          do
            locatedTag <- pLocatedOInj
            maybeType <- optional $ do
              pToken L.OpenAngle
              typ <- pType
              pToken L.CloseAngle
              return typ
            inj <- pAtomExpr
            return $
              let (loc, tag) = locatedTag
               in Loc {expr = OInj {..}, ..},
          -- Tape
          do
            loc <- pLocatedToken L.Tape
            expr <- pAtomExpr
            return Loc {expr = Tape {..}, ..}
        ]

  -- Atomic expression
  pAtomExpr <-
    rule $
      choice
        [ -- Unit value
          pLocatedToken L.OpenParen <* pToken L.CloseParen <&> \loc ->
            Loc {expr = VUnit, ..},
          -- Boolean literal
          pLocatedBLit <&> \(loc, bLit) -> Loc {expr = BLit {..}, ..},
          -- Integer literal
          pLocatedILit <&> \(loc, iLit) -> Loc {expr = ILit {..}, ..},
          -- Variable
          pLocatedIdent <&> \(loc, name) -> Loc {expr = V {..}, ..},
          -- Pair
          pPair L.OpenParen Pair,
          -- Oblivious pair
          pPair L.OpenOParen OPair,
          -- Parenthesized expression
          pParen pExpr
        ]

  let pInfixType op former pLeft pRight = do
        left <- pLeft
        loc <- pLocatedToken $ L.Infix op
        right <- pRight
        return $ Loc {expr = former left right, ..}

  -- Right-associative product type
  pProdType <-
    rule $ choice [pInfixType "*" Prod pOSumType pProdType, pOSumType]

  -- Right-associative oblivious sum type
  pOSumType <-
    rule $ choice [pInfixType "~+" OSum pOProdType pOSumType, pOProdType]

  -- Right-associative oblivious product type
  pOProdType <-
    rule $ choice [pInfixType "~*" OProd pAppType pOProdType, pAppType]

  -- Type application
  pAppType <- rule $ pApp pAtomType tapp_

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

  -- Function argument
  pFunArg <-
    rule $
      choice
        [ (,Nothing) <$> pLocatedBinder,
          do
            pToken L.OpenParen
            binder <- pLocatedBinder
            pToken L.Colon
            typ <- pType
            pToken L.CloseParen
            return (binder, Just typ),
          pToken L.OpenParen *> pFunArg <* pToken L.CloseParen
        ]

  return pProg

-- | Main parser
parse :: [LocatedToken] -> Either LocatedError [NamedDef Text]
parse tokens =
  case fullParses (parser grammar) tokens of
    ([], rpt) -> Left $ renderParserError rpt
    ([ast], _) -> Right ast
    (asts, _) ->
      oops $ "Ambiguous grammar: there are " <> show (length asts) <> " parses!"

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
    showUnexpected LocatedToken {..} = "unexpected " <> show token

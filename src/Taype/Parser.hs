{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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
import Taype.Lexer qualified as L
import Taype.Prelude
import Taype.Syntax
import Text.Earley hiding (Parser, token)
import Prelude hiding (Sum (..))

type Parser r = Prod r Text LocatedToken

pLocatedTerminal :: (Token -> Maybe a) -> Parser r (Int, a)
pLocatedTerminal match = terminal go
  where
    go LocatedToken {..} = (offset,) <$> match token

pLocatedToken :: Token -> Parser r Int
pLocatedToken expected = terminal match
  where
    match LocatedToken {..}
      | expected == token = Just offset
      | otherwise = Nothing

pToken :: Token -> Parser r ()
pToken = void <$> pLocatedToken

pLocatedFn :: Parser r (Int, LLabel)
pLocatedFn = pLocatedTerminal match
  where
    match (L.Fn l) = Just l
    match _ = Nothing

pFn :: Parser r LLabel
pFn = snd <$> pLocatedFn

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

pLocatedInj :: Parser r (Int, (OLabel, Bool))
pLocatedInj = pLocatedTerminal match
  where
    match (L.Inj l b) = Just (l, b)
    match _ = Nothing

pLocatedOProj :: Parser r (Int, OProjKind)
pLocatedOProj = pLocatedTerminal match
  where
    match (L.OProj k) = Just k
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

pairKindToParen :: PairKind -> Token
pairKindToParen = \case
  PublicP -> L.LParen
  OblivP -> L.LOParen
  PsiP -> L.LPParen

pLocatedLParenOf :: [PairKind] -> Parser r (Int, PairKind)
pLocatedLParenOf ks =
  choice [(,k) <$> pLocatedToken (pairKindToParen k) | k <- ks]

getLoc :: Expr a -> Int
getLoc Loc {loc} = loc
getLoc _ = oops "Location not available"

setLoc :: Int -> Expr a -> Expr a
setLoc loc Loc {loc = _, ..} = Loc {..}
setLoc loc expr = Loc {..}

infixToTypeFormer :: Text -> (Ty a -> Ty a -> Ty a)
infixToTypeFormer "+" = Sum PublicL
infixToTypeFormer "*" = Prod PublicL
infixToTypeFormer x | x == oblivName "*" = Prod OblivL
infixToTypeFormer x | x == oblivName "+" = Sum OblivL
infixToTypeFormer _ = oops "unknown type infix"

-- | The grammar for taype language
grammar :: forall r. Grammar r (Parser r (Defs Text))
grammar = mdo
  -- A program is a list of global definitions.
  pProg <- rule $ many pDef

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
      pPMatch matchToken pPatPair pBody = do
        loc <- pLocatedToken matchToken
        cond <- pExpr
        pToken L.With
        optional $ pToken L.Bar
        pat <- pPatPair
        pToken L.DArrow
        body <- pBody
        pToken L.End
        return Loc {expr = pmatchPat_ cond pat body, ..}
      -- Sum elimination
      pSMatch matchToken olabel = do
        loc <- pLocatedToken matchToken
        cond <- pExpr
        pToken L.With
        optional $ pToken L.Bar
        pToken $ L.Inj olabel True
        lPat <- pPat
        pToken L.DArrow
        lBody <- pExpr
        pToken L.Bar
        pToken $ L.Inj olabel False
        rPat <- pPat
        pToken L.DArrow
        rBody <- pExpr
        pToken L.End
        return Loc {expr = smatchPat_ olabel cond lPat lBody rPat rBody, ..}
      -- Public match-like elimination
      pMatch pBody = do
        let pAlt = do
              ctor <- pIdent
              binders <- many pBinder
              pToken L.DArrow
              body <- pBody
              return (ctor, binders, body)
        loc <- pLocatedToken L.Match
        cond <- pExpr
        pToken L.With
        optional $ pToken L.Bar
        alts <- pAlt `sepBy1` pToken L.Bar
        pToken L.End
        return Loc {expr = match_ cond alts, ..}
      -- Pair-like
      pPair former openParenToken = do
        loc <- pLocatedToken openParenToken
        prefix <- some1 $ pExpr <* pToken L.Comma
        end <- pExpr
        pToken L.RParen
        return $
          let go left right = Loc {expr = former left right, loc = getLoc left}
           in setLoc loc $ foldr go end prefix
      -- Application-like
      pApp former pHd = do
        fn <- pHd
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
      -- Variable
      pVar = pLocatedIdent <&> \(loc, name) -> Loc {expr = V {..}, ..}

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
            ~(binder, viewTy) <- pArg
            pToken L.Equals
            body <- pType
            return
              ( name,
                OADTDef
                  { bnd = abstractBinder binder body,
                    binder = Just binder,
                    pubName = "",
                    ..
                  }
              ),
          -- Function definition
          do
            label <- pFn
            ~(loc, name) <- pLocatedIdent
            pToken L.Colon
            ty <- pType
            pToken L.Equals
            expr <- pExpr
            return (name, FunDef {attr = NotAnInst, poly = MonoT, ..})
        ]

  -- Expression
  pExpr <-
    rule $
      choice
        [ -- Lambda abstraction
          do
            pToken L.Lambda
            args <- some1 pLocatedFunArg
            pToken L.DArrow
            body <- pExpr
            return $
              let go ((loc, pat), mTy) body' =
                    Loc {expr = lamPat_ pat mTy body', ..}
               in foldr go body args,
          -- Let
          pLet pExpr,
          -- If conditional
          pIf ite_ L.If pExpr,
          -- Oblivious (possibly leaky) if conditional
          pIf oite_ L.OIf pExpr,
          -- Product and Psi type elimination
          pPMatch L.Match (pPatPairOf [PublicP, PsiP]) pExpr,
          -- Oblivious product elimination
          pPMatch L.OMatch (pPatPairOf [OblivP]) pExpr,
          -- ADT elimination
          pMatch pExpr,
          -- Public sum elimination
          pSMatch L.Match PublicL,
          -- Oblivious (possibly leaky) sum elimination
          pSMatch L.OMatch OblivL,
          -- Next precedence
          pOrExpr
        ]

  let pInfixExpr = pInfix $ \ref left right -> GV {..} @@ [left, right]

  -- Left-associative Boolean or
  pOrExpr <-
    rule $
      choice
        [ pInfixExpr ["||", oblivName "||"] pOrExpr pAndExpr,
          pAndExpr
        ]

  -- Left-associative Boolean and
  pAndExpr <-
    rule $
      choice
        [ pInfixExpr ["&&", oblivName "&&"] pAndExpr pCompareExpr,
          pCompareExpr
        ]

  -- Comparative infix
  pCompareExpr <-
    rule $
      choice
        [ pInfixExpr
            ["<=", oblivName "=", oblivName "<="]
            pAddExpr
            pAddExpr,
          do
            left <- pAddExpr
            pToken L.Equals
            right <- pAddExpr
            return Loc {expr = PolyEq left right, loc = getLoc left},
          pAddExpr
        ]

  -- Left-associative additive infix
  pAddExpr <-
    rule $
      choice
        [ pInfixExpr
            ["+", "-", oblivName "+", oblivName "-"]
            pAddExpr
            pMulExpr,
          pMulExpr
        ]

  -- Left-associative multiplicative infix
  pMulExpr <-
    rule $
      choice
        [ pInfixExpr
            ["*", "/", oblivName "*", oblivName "/"]
            pMulExpr
            pAppExpr,
          pAppExpr
        ]

  -- Application expression
  pAppExpr <-
    rule $
      choice
        [ -- Application
          pApp (@@) pAtomExpr,
          -- Next precedence
          pAtomExpr
        ]

  -- Atomic expression
  pAtomExpr <-
    rule $
      choice
        [ -- Unit value
          pLocatedToken L.LParen
            <* pToken L.RParen <&> \loc ->
              Loc {expr = VUnit, ..},
          -- Boolean literal
          pLocatedBLit <&> \(loc, bLit) -> Loc {expr = BLit {..}, ..},
          -- Integer literal
          pLocatedILit <&> \(loc, iLit) -> Loc {expr = ILit {..}, ..},
          -- Variable
          pVar,
          -- Pair
          pPair (Pair PublicP) L.LParen,
          -- Oblivious pair
          pPair (Pair OblivP) L.LOParen,
          -- Dependent pair (Psi type)
          pPair (Pair PsiP) L.LPParen,
          -- Injection
          do
            ~(loc, (olabel, tag)) <- pLocatedInj
            expr <- pAtomExpr
            return Loc {expr = inj_ olabel tag expr, ..},
          -- Oblivious projection
          do
            ~(loc, tag) <- pLocatedOProj
            expr <- pAtomExpr
            return Loc {expr = oproj_ tag expr, ..},
          -- Arbitrary oblivious value
          do
            loc <- pLocatedToken L.Arb
            return Loc {expr = Arb Nothing, ..},
          -- Preprocessor
          do
            ~(loc, ppx) <- pLocatedPpx
            return Loc {expr = Ppx {..}, ..},
          -- Ascription
          pParen $ do
            expr <- pExpr
            ~(loc, trustMe) <-
              choice
                [ (,False) <$> pLocatedToken L.Colon,
                  (,True) <$> pLocatedToken L.DoubleColon
                ]
            ty <- pType
            return Loc {expr = Asc {..}, ..},
          -- Parenthesized expression
          pParen pExpr
        ]

  -- Preprocessor
  pLocatedPpx <-
    rule $
      choice
        [ do
            loc <- pLocatedToken L.ItePpx
            condTy <- pAtomType
            retTy <- pAtomType
            return (loc, ItePpx {..}),
          do
            ~(loc, ctor) <-
              pLocatedTerminal
                ( \case
                    L.CtorPpx ctor -> Just ctor
                    _ -> Nothing
                )
            retTy <- pAtomType
            return (loc, CtorPpx {..}),
          do
            loc <- pLocatedToken L.MatchPpx
            condTy <- pAtomType
            retTy <- pAtomType
            return (loc, MatchPpx {dyn = True, ..}),
          do
            ~(loc, fn) <-
              pLocatedTerminal
                ( \case
                    L.BuiltinPpx fn -> Just fn
                    _ -> Nothing
                )
            ty <- pAtomType
            return (loc, BuiltinPpx {..}),
          do
            loc <- pLocatedToken L.CoercePpx
            fromTy <- pAtomType
            toTy <- pAtomType
            return (loc, CoercePpx {..}),
          do
            loc <- pLocatedToken L.LiftPpx
            fn <- pIdent
            return (loc, LiftPpx {to = Nothing, ..})
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
                    ty <- pSumType
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
          pPMatch L.Match (pPatPairOf [PublicP]) pType,
          -- ADT elimination
          pMatch pType,
          -- Next precedence
          pSumType
        ]

  let pInfixType = pInfix infixToTypeFormer

  -- Right-associative sum type
  pSumType <-
    rule $ choice [pInfixType ["+"] pProdType pSumType, pProdType]

  -- Right-associative product type
  pProdType <-
    rule $ choice [pInfixType ["*"] pOSumType pProdType, pOSumType]

  -- Right-associative oblivious sum type
  pOSumType <-
    rule $
      choice
        [ pInfixType [oblivName "+"] pOProdType pOSumType,
          pOProdType
        ]

  -- Right-associative oblivious product type
  pOProdType <-
    rule $
      choice
        [ pInfixType [oblivName "*"] pAppType pOProdType,
          pAppType
        ]

  -- Type application
  pAppType <-
    rule $
      choice
        [ pApp (@@) pVar,
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
          pLocatedToken L.TBool <&> \loc -> Loc {expr = TBool PublicL, ..},
          -- Oblivious Boolean type
          pLocatedToken L.OBool <&> \loc -> Loc {expr = TBool OblivL, ..},
          -- Integer type
          pLocatedToken L.TInt <&> \loc -> Loc {expr = TInt PublicL, ..},
          -- Oblivious integer type
          pLocatedToken L.OInt <&> \loc -> Loc {expr = TInt OblivL, ..},
          -- Unsigned integer type
          pLocatedToken L.UInt <&> \loc -> Loc {expr = UInt, ..},
          -- Psi type
          do
            loc <- pLocatedToken L.Psi
            oadtName <- pIdent
            return Loc {expr = Psi {viewTy = Nothing, ..}, ..},
          -- Variable
          pVar,
          -- Type variable
          pLocatedToken L.TV <&> \loc -> Loc {expr = TV 0, ..},
          -- Parenthesized type
          pParen pType
        ]

  -- Function argument
  pLocatedFunArg <-
    rule $
      choice
        [ (,Nothing) <$> pLocatedPat,
          do
            pToken L.LParen
            binder <- pLocatedPat
            pToken L.Colon
            ty <- pType
            pToken L.RParen
            return (binder, Just ty),
          pToken L.LParen *> pLocatedFunArg <* pToken L.RParen
        ]

  -- Pattern
  pLocatedPat <-
    rule $
      choice
        [ second VarP <$> pLocatedBinder,
          pLocatedPatPairOf [PublicP, OblivP, PsiP]
        ]
  let pLocatedPatPairOf ks = do
        ~(patLoc, pairKind) <- pLocatedLParenOf ks
        prefix <- some1 $ pLocatedPat <* pToken L.Comma
        end <- pLocatedPat
        pToken L.RParen
        return $
          let go (loc, left) (_, right) =
                (loc, PairP loc pairKind left right)
              (_, pat) = foldr go end prefix
              pat' = case pat of
                PairP _ k l r -> PairP patLoc k l r
                p -> p
           in (patLoc, pat')
  let pPat = snd <$> pLocatedPat
  let pPatPairOf ks = snd <$> pLocatedPatPairOf ks

  return pProg

-- | Main parser
parse :: (MonadError Err m) => [LocatedToken] -> m (Defs Text)
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
      errClass = ErrorC,
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
  L.Psi -> squotes $ pretty psiAccent
  L.Arrow -> dquotes "->"
  L.DArrow -> dquotes "=>"
  L.Equals -> squotes equals
  L.Colon -> squotes colon
  L.DoubleColon -> squotes $ colon <> colon
  L.Bar -> squotes pipe
  L.Comma -> squotes comma
  L.LParen -> squotes lparen
  L.LOParen -> dquotes $ pretty oblivAccent <> lparen
  L.LPParen -> dquotes $ pretty psiAccent <> lparen
  L.RParen -> squotes rparen
  L.TUnit -> "unit"
  L.TBool -> "bool"
  L.OBool -> pretty $ oblivName "bool"
  L.BLit _ -> "boolean literal"
  L.TInt -> "int"
  L.OInt -> pretty $ oblivName "int"
  L.UInt -> "uint"
  L.ILit _ -> "integer literal"
  L.Data -> "data"
  L.Obliv -> "obliv"
  L.Fn SafeL -> "fn"
  L.Fn LeakyL -> "fn'"
  L.Let -> "let"
  L.In -> "in"
  L.If -> "if"
  L.OIf -> pretty $ oblivName "if"
  L.Then -> "then"
  L.Else -> "else"
  L.Match -> "match"
  L.OMatch -> pretty $ oblivName "match"
  L.With -> "with"
  L.End -> "end"
  L.Inj olabel tag ->
    pretty $
      accentOfOLabel olabel
        <> if tag then "inl" else "inr"
  L.OProj tag -> pretty $ oblivName $ case tag of
    TagP -> "prt"
    LeftP -> "prl"
    RightP -> "prr"
  L.Ident ident -> "identifier" <+> dquotes (pretty ident)
  L.Infix ident -> "infix" <+> dquotes (pretty ident)
  L.TV -> "'a"
  L.Arb -> pretty $ oblivAccent <> oblivAccent
  L.ItePpx -> pretty $ ppxName "if"
  L.MatchPpx -> pretty $ ppxName "match"
  L.CoercePpx -> pretty $ ppxName "coerce"
  L.LiftPpx -> pretty $ ppxName "lift"
  L.CtorPpx x -> pretty $ ppxName x
  L.BuiltinPpx x -> pretty $ ppxName x

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Lexer for the taype language.
module Taype.Lexer
  ( Token (..),
    LocatedToken (..),
    Parser,
    lex,
    printTokens,
  )
where

import Control.Monad.Error.Class
import Data.Char
import Data.Text qualified as T
import Taype.Common
import Taype.Cute hiding (space)
import Taype.Error
import Text.Megaparsec hiding (Token, showErrorItem, token, tokens)
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

-- | Taype tokens
data Token
  = Lambda
  | Underscore
  | Psi
  | Arrow
  | DArrow
  | Equals
  | Colon
  | DoubleColon
  | Bar
  | Comma
  | LParen
  | LOParen
  | LPParen
  | RParen
  | TUnit
  | TBool
  | OBool
  | BLit Bool
  | TInt
  | OInt
  | UInt
  | ILit Int
  | Data
  | Obliv
  | Fn LLabel
  | Let
  | In
  | If
  | OIf
  | Then
  | Else
  | Match
  | OMatch
  | With
  | End
  | Inj OLabel Bool
  | OProj OProjKind
  | Ident Text
  | Infix Text
  | TV
  | Arb
  | ItePpx
  | CtorPpx Text
  | MatchPpx
  | BuiltinPpx Text
  | CoercePpx
  | LiftPpx
  deriving stock (Eq, Show)

-- | Token with location information
data LocatedToken = LocatedToken {token :: Token, offset :: Int}
  deriving stock (Eq, Show)

type Parser = Parsec Void Text

space :: Parser ()
space = L.space C.space1 (L.skipLineComment commentDelim) empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

-- | The main token parser
pToken :: Parser Token
pToken =
  choice
    [ pIdent <?> "identifier",
      Arrow <$ symbol "->",
      DArrow <$ symbol "=>",
      choice ((Infix <$>) . symbol <$> allInfixes) <?> "infix",
      choice
        [ TUnit <$ symbol "unit",
          TBool <$ symbol "bool",
          OBool <$ symbol (oblivName "bool"),
          TInt <$ symbol "int",
          OInt <$ symbol (oblivName "int"),
          UInt <$ symbol "uint"
        ]
        <?> "built-in type",
      choice
        [ Data <$ symbol "data",
          Obliv <$ symbol "obliv",
          Fn LeakyL <$ symbol "fn'",
          Fn SafeL <$ symbol "fn",
          Let <$ symbol "let",
          If <$ symbol "if",
          OIf <$ symbol (oblivName "if"),
          Then <$ symbol "then",
          Else <$ symbol "else",
          Match <$ symbol "match",
          OMatch <$ symbol (oblivName "match"),
          With <$ symbol "with",
          End <$ symbol "end",
          Inj PublicL True <$ symbol "inl",
          Inj PublicL False <$ symbol "inr",
          Inj OblivL True <$ symbol (oblivName "inl"),
          Inj OblivL False <$ symbol (oblivName "inr"),
          In <$ symbol "in",
          OProj TagP <$ symbol (oblivName "prt"),
          OProj LeftP <$ symbol (oblivName "prl"),
          OProj RightP <$ symbol (oblivName "prr")
        ]
        <?> "keyword",
      choice
        [ BLit True <$ symbol "true",
          BLit False <$ symbol "false",
          ILit <$> pILit
        ]
        <?> "literal",
      Lambda <$ symbol "\\",
      Equals <$ symbol "=",
      DoubleColon <$ symbol "::",
      Colon <$ symbol ":",
      Bar <$ symbol "|",
      Comma <$ symbol ",",
      Underscore <$ symbol "_",
      LParen <$ symbol "(",
      LOParen <$ symbol (oblivName "("),
      LPParen <$ symbol (psiName "("),
      RParen <$ symbol ")",
      Psi <$ symbol psiAccent,
      TV <$ symbol "'a",
      Arb <$ symbol (oblivAccent <> oblivAccent),
      pPpx <?> "preprocessor"
    ]

isIdent0 :: Char -> Bool
isIdent0 c = isLetter c || c == '_'

isIdent :: Char -> Bool
isIdent c = isAlphaNum c || c == '_' || c == '\''

pIdentComp :: Parser Text
pIdentComp = do
  accent <- option "" $ chunk oblivAccent
  x <- satisfy isIdent0
  xs <- takeWhileP Nothing isIdent
  return $ accent <> T.cons x xs

pIdent :: Parser Token
pIdent = lexeme . try $ do
  comps <- sepBy1 pIdentComp $ chunk instInfix
  let ident = T.intercalate instInfix comps
  guard (ident `notElem` reserved)
  return $ Ident ident

pILit :: Parser Int
pILit =
  lexeme $
    choice
      [ L.decimal,
        try $
          between (symbol "(") (symbol ")") $
            L.signed mempty L.decimal
      ]

pPpx :: Parser Token
pPpx =
  choice
    [ ItePpx <$ symbol (ppxName "if"),
      MatchPpx <$ symbol (ppxName "match"),
      CoercePpx <$ symbol (ppxName "coerce"),
      LiftPpx <$ symbol (ppxName "lift"),
      CtorPpx <$> lexeme (try pCtorPpx),
      BuiltinPpx <$> lexeme (try pBuiltinPpx)
    ]
  where
    pCtorPpx = do
      void $ chunk ppxAccent
      x <- C.upperChar
      xs <- takeWhileP Nothing isIdent
      return $ T.cons x xs
    pBuiltinPpx = do
      void $ chunk ppxAccent
      takeWhile1P Nothing (not . isSpace)

-- | Reserved tokens that cannot be used for identifier
reserved :: [Text]
reserved =
  [ "_",
    "data",
    "obliv",
    "fn",
    "fn'",
    "let",
    "in",
    "if",
    oblivName "if",
    "then",
    "else",
    "match",
    oblivName "match",
    "with",
    "end",
    "inl",
    "inr",
    oblivName "inl",
    oblivName "inr",
    oblivName "prt",
    oblivName "prl",
    oblivName "prr",
    "unit",
    "bool",
    oblivName "bool",
    "int",
    oblivName "int",
    "uint",
    "true",
    "false"
  ]

-- | Parse a token with offset.
pLocatedToken :: Parser LocatedToken
pLocatedToken = do
  offset <- getOffset
  token <- pToken
  return LocatedToken {..}

-- | Parse all tokens
pTokens :: Parser [LocatedToken]
pTokens = space *> manyTill pLocatedToken eof

-- | Taype lexer
lex :: (MonadError Err m) => FilePath -> Text -> m [LocatedToken]
lex file code = liftEither $ first renderLexerError (parse pTokens file code)

renderLexerError :: ParseErrorBundle Text Void -> Err
renderLexerError ParseErrorBundle {bundleErrors = err :| _} =
  Err
    { errLoc = errorOffset err,
      errMsg = showError err,
      errCategory = "Lexing Error",
      errClass = ErrorC
    }
  where
    showError (TrivialError _ u _) = maybe "Unknown error" showUnexpected u
    showError (FancyError _ _) = "Unknown error"
    showUnexpected = ("Unexpected" <+>) . showErrorItem
    showErrorItem (Tokens ts) = pretty (showTokens proxy ts)
    showErrorItem (Label lab) = pretty $ toList lab
    showErrorItem EndOfInput = "end of input"
    proxy = Proxy :: Proxy Text

printTokens :: (MonadIO m) => FilePath -> Text -> [LocatedToken] -> m ()
printTokens file code tokens = mapM_ go positions
  where
    go (LocatedToken {..}, SourcePos {..}) =
      putTextLn $
        showLocation file (unPos sourceLine) (unPos sourceColumn)
          <> ": "
          <> show token
    (positions, _) = attachSourcePos offset tokens $ initPosState file code

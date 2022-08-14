{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Lexer for taype.
module Taype.Lexer (Token (..), LocatedToken (..), lex) where

import Data.Char
import qualified Data.Text as T
import Text.Megaparsec hiding (Token, token)
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

-- | Taype tokens
data Token
  = Lambda
  | Underscore
  | Arrow
  | Equals
  | Colon
  | Bar
  | Comma
  | OpenAngle
  | CloseAngle
  | OpenAttr
  | CloseBrace
  | OpenParen
  | OpenOParen
  | CloseParen
  | TUnit
  | TBool
  | OBool
  | BLit Bool
  | TInt
  | OInt
  | ILit Int
  | Data
  | Obliv
  | Fn
  | Let
  | In
  | If
  | OIf
  | Then
  | Else
  | Mux
  | Case
  | OCase
  | Of
  | OInj Bool
  | Ident Text
  | Infix Text
  deriving stock (Eq, Show)

-- | Token with location information
data LocatedToken = LocatedToken {token :: Token, offset :: Int}
  deriving stock (Eq, Show)

type Parser = Parsec Void Text

space :: Parser ()
space = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

-- | The main token parser
pToken :: Parser Token
pToken =
  choice
    [ choice
        [ Infix <$> symbol "<=",
          Infix <$> symbol "~<=",
          Infix <$> symbol "==",
          Infix <$> symbol "~=",
          Infix <$> symbol "+",
          Infix <$> symbol "-",
          Infix <$> symbol "~+",
          Infix <$> symbol "~-",
          Infix <$> symbol "*",
          Infix <$> symbol "~*"
        ]
        <?> "infix",
      choice
        [ Data <$ symbol "data",
          Obliv <$ symbol "obliv",
          Fn <$ symbol "fn",
          Let <$ symbol "let",
          In <$ symbol "in",
          If <$ symbol "if",
          Then <$ symbol "then",
          Else <$ symbol "else",
          Mux <$ symbol "mux",
          Case <$ symbol "case",
          OCase <$ symbol "~case",
          Of <$ symbol "of",
          OInj True <$ symbol "~inl",
          OInj False <$ symbol "~inr"
        ]
        <?> "keyword",
      choice
        [ TUnit <$ symbol "Unit",
          TBool <$ symbol "Bool",
          OBool <$ symbol "~Bool",
          TInt <$ symbol "Int",
          OInt <$ symbol "~Int"
        ]
        <?> "built-in type",
      choice
        [ BLit True <$ symbol "True",
          BLit False <$ symbol "False",
          ILit <$> lexeme L.decimal
        ]
        <?> "literal",
      Lambda <$ symbol "\\",
      Arrow <$ symbol "->",
      Equals <$ symbol "=",
      Colon <$ symbol ":",
      Bar <$ symbol "|",
      Comma <$ symbol ",",
      OpenAngle <$ symbol "<",
      CloseAngle <$ symbol ">",
      OpenAttr <$ symbol "#[",
      CloseBrace <$ symbol "]",
      OpenParen <$ symbol "(",
      OpenOParen <$ symbol "~(",
      CloseParen <$ symbol ")",
      -- Identifier parsing has to be the last one
      pIdent <?> "Identifier"
    ]

isIdent0 :: Char -> Bool
isIdent0 c = isLetter c || c == '_'

isIdent :: Char -> Bool
isIdent c = isAlphaNum c || c == '_' || c == '\''

pIdent :: Parser Token
pIdent = lexeme $ do
  mayObliv <- option "" $ symbol "~"
  x <- satisfy isIdent0
  xs <- takeWhileP Nothing isIdent
  let ident = mayObliv <> T.cons x xs
  return $ if ident == "_" then Underscore else Ident ident

-- | Parse a token with offset
pLocatedToken :: Parser LocatedToken
pLocatedToken = do
  offset <- getOffset
  token <- pToken
  return LocatedToken {..}

-- | Parse all tokens
pTokens :: Parser [LocatedToken]
pTokens = space *> manyTill pLocatedToken eof

-- | Taype lexer
lex :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [LocatedToken]
lex = parse pTokens

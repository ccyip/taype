{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Lexer for taype.
module Taype.Lexer (Token (..), lex) where

import Data.Char
import qualified Data.Text as T
import Text.Megaparsec hiding (Token)
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

-- | Taype tokens
data Token
  = Lambda
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
  | -- Precedence: BinOp1 < BinOp2 < BinOp3
    Infix1 Text
  | Infix2 Text
  | Infix3 Text
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
    [ Lambda <$ symbol "\\",
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
      choice
        [ Infix1 <$> symbol "<=",
          Infix1 <$> symbol "==",
          Infix2 <$> symbol "+",
          Infix2 <$> symbol "-",
          Infix2 <$> symbol "~+",
          Infix3 <$> symbol "*",
          Infix3 <$> symbol "~*"
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
  return $ Ident $ mayObliv <> T.cons x xs

pTokens :: Parser [Token]
pTokens = space *> manyTill pToken eof

-- | Taype lexer
lex :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [Token]
lex = parse pTokens
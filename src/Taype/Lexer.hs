{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
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
module Taype.Lexer
  ( Token (..),
    LocatedToken (..),
    lex,
    printTokens,
  )
where

import Data.Char
import qualified Data.Text as T
import Taype.Error
import Text.Megaparsec hiding (Token, token, tokens)
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
  | LAngle
  | RAngle
  | LAttr
  | RBrace
  | LParen
  | LOParen
  | RParen
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
  | End
  | Tape
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
    [ pIdent <?> "identifier",
      Arrow <$ symbol "->",
      choice
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
          End <$ symbol "end",
          OInj True <$ symbol "~inl",
          OInj False <$ symbol "~inr",
          Tape <$ symbol "tape"
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
      Equals <$ symbol "=",
      Colon <$ symbol ":",
      Bar <$ symbol "|",
      Comma <$ symbol ",",
      Underscore <$ symbol "_",
      LAngle <$ symbol "<",
      RAngle <$ symbol ">",
      LAttr <$ symbol "#[",
      RBrace <$ symbol "]",
      LParen <$ symbol "(",
      LOParen <$ symbol "~(",
      RParen <$ symbol ")"
    ]

isIdent0 :: Char -> Bool
isIdent0 c = isLetter c || c == '_'

isIdent :: Char -> Bool
isIdent c = isAlphaNum c || c == '_' || c == '\''

pIdent :: Parser Token
pIdent = lexeme . try $ do
  mayObliv <- option "" $ symbol "~"
  x <- satisfy isIdent0
  xs <- takeWhileP Nothing isIdent
  let ident = mayObliv <> T.cons x xs
  guard (ident `notElem` reserved)
  return $ Ident ident

-- | Reserved tokens that cannot be used for identifier
reserved :: [Text]
reserved =
  [ "_",
    "data",
    "obliv",
    "fn",
    "let",
    "in",
    "if",
    "then",
    "else",
    "mux",
    "case",
    "~case",
    "of",
    "end",
    "~inl",
    "~inr",
    "tape",
    "Unit",
    "Bool",
    "~Bool",
    "Int",
    "~Int",
    "True",
    "False"
  ]

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
lex :: FilePath -> Text -> Either LocatedError [LocatedToken]
lex = first renderLexerError <<$>> parse pTokens

renderLexerError :: ParseErrorBundle Text Void -> LocatedError
renderLexerError ParseErrorBundle {bundleErrors = err :| _} =
  LocatedError
    { errLoc = errorOffset err,
      errMsg = showError err,
      errCategory = "Lexing Error"
    }
  where
    showError (TrivialError _ u _) = maybe "unknown error" showUnexpected u
    showError (FancyError _ _) = "unknown error"
    showUnexpected = ("unexpected " <>) . showErrorItem
    showErrorItem (Tokens ts) = toText (showTokens proxy ts)
    showErrorItem (Label lab) = toText $ toList lab
    showErrorItem EndOfInput = "end of input"
    proxy = Proxy :: Proxy Text

printTokens :: FilePath -> Text -> [LocatedToken] -> IO ()
printTokens file code tokens = mapM_ go positions
  where
    go (LocatedToken {..}, SourcePos {..}) =
      putTextLn $
        showLocation file (unPos sourceLine) (unPos sourceColumn) <> ": "
          <> show token
    (positions, _) = attachSourcePos offset tokens $ initPosState file code

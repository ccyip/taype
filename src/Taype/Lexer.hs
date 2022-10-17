{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
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
-- Lexer for the taype language.
module Taype.Lexer
  ( Token (..),
    LocatedToken (..),
    lex,
    printTokens,
  )
where

import Control.Monad.Error.Class
import Data.Char
import qualified Data.Text as T
import Taype.Common
import Taype.Cute hiding (space)
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
      choice ((Infix <$>) . symbol <$> infixes <> oblivInfixes) <?> "infix",
      choice
        [ TUnit <$ symbol "unit",
          TBool <$ symbol "bool",
          OBool <$ symbol (oblivName "bool"),
          TInt <$ symbol "int",
          OInt <$ symbol (oblivName "int")
        ]
        <?> "built-in type",
      choice
        [ Data <$ symbol "data",
          Obliv <$ symbol "obliv",
          Fn <$ symbol "fn",
          Let <$ symbol "let",
          In <$ symbol "in",
          If <$ symbol "if",
          OIf <$ symbol (oblivName "if"),
          Then <$ symbol "then",
          Else <$ symbol "else",
          Mux <$ symbol "mux",
          Case <$ symbol "case",
          OCase <$ symbol (oblivName "case"),
          Of <$ symbol "of",
          End <$ symbol "end",
          OInj True <$ symbol (oblivName "inl"),
          OInj False <$ symbol (oblivName "inr"),
          Tape <$ symbol "tape"
        ]
        <?> "keyword",
      choice
        [ BLit True <$ symbol "True",
          BLit False <$ symbol "False",
          ILit <$> pILit
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
      LOParen <$ symbol (oblivName "("),
      RParen <$ symbol ")"
    ]

isIdent0 :: Char -> Bool
isIdent0 c = isLetter c || c == '_'

isIdent :: Char -> Bool
isIdent c = isAlphaNum c || c == '_' || c == '\''

pIdent :: Parser Token
pIdent = lexeme . try $ do
  mayObliv <- option "" $ symbol oblivAccent
  x <- satisfy isIdent0
  xs <- takeWhileP Nothing isIdent
  let ident = mayObliv <> T.cons x xs
  guard (ident `notElem` reserved)
  return $ Ident ident

pILit :: Parser Int
pILit =
  lexeme $
    choice
      [ L.decimal,
        try $ between (symbol "(") (symbol ")") $
          L.signed mempty L.decimal
      ]

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
    "~if",
    "then",
    "else",
    "mux",
    "case",
    oblivName "case",
    "of",
    "end",
    oblivName "inl",
    oblivName "inr",
    "tape",
    "unit",
    "bool",
    oblivName "bool",
    "int",
    oblivName "int",
    "True",
    "False"
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
lex :: MonadError Err m => FilePath -> Text -> m [LocatedToken]
lex file code = liftEither $ first renderLexerError (parse pTokens file code)

renderLexerError :: ParseErrorBundle Text Void -> Err
renderLexerError ParseErrorBundle {bundleErrors = err :| _} =
  Err
    { errLoc = errorOffset err,
      errMsg = showError err,
      errCategory = "Lexing Error"
    }
  where
    showError (TrivialError _ u _) = maybe "Unknown error" showUnexpected u
    showError (FancyError _ _) = "Unknown error"
    showUnexpected = ("Unexpected" <+>) . showErrorItem
    showErrorItem (Tokens ts) = pretty (showTokens proxy ts)
    showErrorItem (Label lab) = pretty $ toList lab
    showErrorItem EndOfInput = "end of input"
    proxy = Proxy :: Proxy Text

printTokens :: MonadIO m => FilePath -> Text -> [LocatedToken] -> m ()
printTokens file code tokens = mapM_ go positions
  where
    go (LocatedToken {..}, SourcePos {..}) =
      putTextLn $
        showLocation file (unPos sourceLine) (unPos sourceColumn)
          <> ": "
          <> show token
    (positions, _) = attachSourcePos offset tokens $ initPosState file code

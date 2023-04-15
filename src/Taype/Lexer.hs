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
  | OInj Bool
  | OProj OProjKind
  | Ident Text
  | Infix Text
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
          Fn LeakyL <$ symbol "fn'",
          Fn SafeL <$ symbol "fn",
          Let <$ symbol "let",
          In <$ symbol "in",
          If <$ symbol "if",
          OIf <$ symbol (oblivName "if"),
          Then <$ symbol "then",
          Else <$ symbol "else",
          Match <$ symbol "match",
          OMatch <$ symbol (oblivName "match"),
          With <$ symbol "with",
          End <$ symbol "end",
          OInj True <$ symbol (oblivName "inl"),
          OInj False <$ symbol (oblivName "inr"),
          OProj TagP <$ symbol (oblivName "prt"),
          OProj LeftP <$ symbol (oblivName "prl"),
          OProj RightP <$ symbol (oblivName "prr")
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
      DoubleColon <$ symbol "::",
      Colon <$ symbol ":",
      Bar <$ symbol "|",
      Comma <$ symbol ",",
      Underscore <$ symbol "_",
      LParen <$ symbol "(",
      LOParen <$ symbol (oblivName "("),
      LPParen <$ symbol (psiName "("),
      RParen <$ symbol ")",
      Psi <$ symbol psiAccent
    ]

isIdent0 :: Char -> Bool
isIdent0 c = isLetter c || c == '_'

isIdent :: Char -> Bool
isIdent c = isAlphaNum c || c == '_' || c == '\''

pIdentComp :: Parser Text
pIdentComp = do
  accent <- option "" $ symbol oblivAccent
  x <- satisfy isIdent0
  xs <- takeWhileP Nothing isIdent
  return $ accent <> T.cons x xs

pIdent :: Parser Token
pIdent = lexeme . try $ do
  comps <- sepBy1 pIdentComp $ single '#'
  let ident = T.intercalate "#" comps
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

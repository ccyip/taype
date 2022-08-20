-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Top-level functions.
module Taype
  ( test,
  )
where

import Prettyprinter.Render.Text
import Taype.Syntax
import Taype.Lexer (lex)
import Taype.Parser (parse)
import Taype.Environment
import Taype.Error
import Taype.Cute

test :: FilePath -> IO ()
test file = do
  content <- readFileBS file
  let code = decodeUtf8 content
  case process file code of
    Left err -> putTextLn $ renderError file code err
    Right (defs, ctx) -> putDoc $ prettyDefs defs ctx

process :: FilePath -> Text -> Either LocatedError ([Text], GCtx a)
process file code = do
  tokens <- lex file code
  parse tokens

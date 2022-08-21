{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Top-level functions.
module Taype
  ( run,
  )
where

import Prettyprinter.Render.Text
import Taype.Cute
import Taype.Environment
import Taype.Error
import Taype.Lexer (lex, printTokens)
import Taype.Parser (parse)

run :: Options -> IO ()
run options@Options {optFile = file} = do
  content <- readFileBS file
  let code = decodeUtf8 content
  result <- runExceptT $ process file code options
  whenLeft_ result $ putTextLn . renderError file code

process :: FilePath -> Text -> Options -> ExceptT LocatedError IO ()
process file code options@Options {..} = do
  tokens <- hoistEither $ lex file code
  when optPrintTokens $ printTokens file code tokens >> putStr "\n"
  (defs, gctx) <- hoistEither $ parse tokens
  -- Always print out the source code for now
  lift $ putDoc $ cuteDefs defs Env {..}

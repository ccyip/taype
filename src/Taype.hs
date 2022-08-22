{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
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
  ( main,
  )
where

import Bound
import Options.Applicative
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter.Util (putDocW)
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

process :: FilePath -> Text -> Options -> ExceptT Err IO ()
process file code options@Options {..} = do
  tokens <- lex file code
  when optPrintTokens $ printTokens file code tokens >> putStr "\n"
  (defs, gctx) <- parse tokens
  -- 'gctx' needs to be closed again because the pretty printer instantiates the
  -- phantom type variable with 'Text'
  when optPrintSource $ printDoc $ cuteDefs options (close gctx) defs
  where
    printDoc = lift . maybe putDoc putDocW optWidth
    close gctx = fromMaybe (oops "global context is not closed") $ closed gctx

main :: IO ()
main = run =<< execParser (info (opts <**> helper) helpMod)
  where
    helpMod =
      fullDesc <> header "taype - a programming language with data types and tape"

opts :: Parser Options
opts = do
  optFile <-
    strArgument $
      metavar "FILE" <> help "Taype source file"
  optInternalNames <-
    switch $
      long "internal-names" <> short 'i'
        <> help "Whether to print the internal names for variables"
  optNamePrefix <-
    strOption $
      long "prefix" <> short 'p' <> metavar "PREFIX"
        <> value "$"
        <> showDefault
        <> help "Prefix to the internal names"
  optPrintLabels <-
    switch $
      long "print-labels" <> short 'l'
        <> help "Whether to print the leakage labels"
  optPrintTokens <-
    switch $
      long "print-tokens" <> short 't'
        <> help "Whether to print tokens (for internal debugging)"
  optPrintSource <-
    switch $
      long "print-source" <> short 's'
        <> help "Whether to print the source code (for internal debugging)"
  optWidth <-
    optional $
      option auto $
        long "width" <> short 'w'
          <> help "Window width (for debugging pretty printer)"
  return Options {..}

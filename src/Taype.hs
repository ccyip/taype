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
-- Entry point of the taype language type checker and compiler.
module Taype
  ( main,
  )
where

import Options.Applicative
import Taype.Common
import Taype.Cute
import Taype.Environment
import Taype.Error
import Taype.Lexer
import Taype.Parser
import Taype.Syntax
import Taype.TypeChecker

run :: Options -> IO ()
run options@Options {optFile = file} = do
  content <- readFileBS file
  let code = decodeUtf8 content
      opt = options {optCode = code}
  result <- runExceptT $ process opt
  whenLeft_ result $ printDoc opt . runCuteM opt . cute

process :: Options -> ExceptT Err IO ()
process options@Options {optFile = file, optCode = code, ..} = do
  tokens <- lex file code
  when optPrintTokens $ printTokens file code tokens >> putStr "\n"
  namedDefs <- parse tokens
  let names = fst <$> namedDefs
      defs = closeDefs namedDefs
  when optPrintSource $ printDefs (fromList defs) names
  gctx <- checkDefs options defs
  when optPrintCore $ printDefs gctx names
  where
    printDefs gctx defs =
      printDoc options $ cuteDefs options gctx defs

main :: IO ()
main = run =<< execParser (info (opts <**> helper) helpMod)
  where
    helpMod =
      fullDesc
        <> header "taype - a programming language with data types and tape"

opts :: Parser Options
opts = do
  optFile <-
    strArgument $
      metavar "FILE" <> help "Taype source file"
  optInternalNames <-
    switch $
      long "internal-names" <> short 'i'
        <> help "Whether to print the internal names for variables"
  optNoFlattenLets <-
    switch $
      long "no-flatten-lets"
        <> help "Do not flatten let bindings"
  optPrintCore <-
    switch $
      long "print-core" <> short 'c'
        <> help "Whether to print the generated core taype programs"
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
  return Options {optCode = "", ..}

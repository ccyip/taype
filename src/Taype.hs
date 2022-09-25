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

import qualified Oil.Syntax as Oil (cuteDefs)
import qualified Oil.ToOCaml as Oil (toOCaml)
import Oil.Translation (toOilDefs)
import qualified Oil.Translation as Oil (prelude)
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
      srcDefs = closeDefs namedDefs
  when optPrintSource $ printTaypeDefs srcDefs
  gctx <- checkDefs options srcDefs
  let defs = defsFromGCtx (fromClosed gctx) names
  when optPrintCore $ printTaypeDefs defs
  let oilDefs = toOilDefs options gctx defs
  when optPrintPrelude $ printOilDefs Oil.prelude
  when optPrintOil $ printOilDefs oilDefs
  let mlDoc = Oil.toOCaml options oilDefs
  printDoc options mlDoc
  where
    printTaypeDefs defs =
      printDoc options $ cuteDefs options defs
    printOilDefs defs =
      printDoc options $ Oil.cuteDefs options defs

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
      long "internal-names"
        <> short 'i'
        <> help "Whether to use the internal names for variables"
  optNoFlattenLets <-
    switch $
      long "no-flatten-lets"
        <> help "Do not flatten let bindings"
  optPrintCore <-
    switch $
      long "print-core"
        <> short 'c'
        <> help "Whether to print the generated core taype programs"
  optPrintPrelude <-
    switch $
      long "print-prelude"
        <> short 'p'
        <> help "Whether to print the OIL prelude"
  optPrintOil <-
    switch $
      long "print-oil"
        <> short 'o'
        <> help "Whether to print the generated OIL programs"
  optNamePrefix <-
    strOption $
      long "prefix"
        <> metavar "PREFIX"
        <> value "$"
        <> showDefault
        <> help "Prefix to the internal names (only affects printing)"
  optPrintLabels <-
    switch $
      long "print-labels"
        <> short 'l'
        <> help "Whether to print the leakage labels"
  optPrintTokens <-
    switch $
      long "print-tokens"
        <> short 't'
        <> help "Whether to print tokens (for internal debugging)"
  optPrintSource <-
    switch $
      long "print-source"
        <> short 's'
        <> help "Whether to print the source code (for internal debugging)"
  optNoReadableOil <-
    switch $
      long "no-readable-oil"
        <> help "Do not make the generated OIL programs more readable"
  optWidth <-
    optional $
      option auto $
        long "width"
          <> short 'w'
          <> help "Window width (for debugging pretty printer)"
  return Options {optCode = "", ..}

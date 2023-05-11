{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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

import Oil.Syntax qualified as Oil (cuteProgramDoc)
import Oil.ToOCaml qualified as Oil (toOCaml)
import Oil.Translation (toOilProgram)
import Options.Applicative
import System.FilePath
import Taype.Common
import Taype.Cute
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
  whenLeft_ result $ \err -> do
    printDoc opt $ runCuteM opt $ cute err
    exitFailure

process :: Options -> ExceptT Err IO ()
process options@Options {optFile = file, optCode = code, ..} = do
  tokens <- lex file code
  when optPrintTokens $ printTokens file code tokens >> putStr "\n"
  defs <- parse tokens
  let srcDefs :: Defs a
      srcDefs = closeDefs defs
      srcDoc = cuteDefsDoc options srcDefs
  when optPrintSource $ printDoc options srcDoc
  (gctx, coreDefs0) <- checkDefs options srcDefs
  processCore 0 coreDefs0
  -- Stage 1 derives lift proprocessor, which is a placeholder for now.
  let coreDefs1 = coreDefs0
  processCore 1 coreDefs1
  -- Stage 2 elaborates all proprocessors.
  coreDefs2 <- elabPpxDefs options gctx coreDefs1
  processCore 2 coreDefs2
  prog <- lift $ toOilProgram options coreDefs2
  let oilDoc = Oil.cuteProgramDoc options prog
  when optPrintOil $ printDoc options oilDoc
  printToFile "oil" oilDoc
  let mlDoc = Oil.toOCaml options prog
  when optPrintOCaml $ printDoc options mlDoc
  printToFile "ml" mlDoc
  where
    printToFile ext doc =
      unless optNoFiles $ printDocToFile (file -<.> ext) doc
    processCore stage coreDefs = do
      let coreDefs' = if optReadable then readableDefs coreDefs else coreDefs
          coreDoc = cuteDefsDoc options (fromClosedDefs coreDefs')
      when (optPrintCore && optStage == stage) $ printDoc options coreDoc
      printToFile ("stage" <> show stage <> ".tpc") coreDoc

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
      metavar "FILE"
        <> value ""
        <> help "Taype source file"
  optInternalNames <-
    switch $
      long "internal-names"
        <> short 'i'
        <> help "Whether to print the internal names for variables"
  optNoFlattenLets <-
    switch $
      long "no-flatten-lets"
        <> help "Do not flatten let bindings"
  optNoFiles <-
    switch $
      long "no-files"
        <> short 'n'
        <> help "Do not generate files"
  optQuiet <-
    switch $
      long "quiet"
        <> short 'q'
        <> help "No warnings"
  optFlagNoOptimization <-
    switch $
      long "fno-opt"
        <> help "Disable all optimization"
  optFlagNoSimplify <-
    switch $
      long "fno-simplify"
        <> help "Disable simplifier"
  optFlagNoInline <-
    switch $
      long "fno-inline"
        <> help "Disable inlining any OADT instances"
  optFlagNoMemo <-
    switch $
      long "fno-memo"
        <> help "Disable memoization optimization"
  optFlagNoGuardReshape <-
    switch $
      long "fno-guard-reshape"
        <> help "Disable guarding reshape instances"
  optPrintCore <-
    switch $
      long "print-core"
        <> help "Whether to print the generated core taype programs"
  optStage <-
    option auto $
      long "stage"
        <> value 0
        <> help "Which stage of core taype programs to print"
  optPrintOil <-
    switch $
      long "print-oil"
        <> help "Whether to print the generated OIL programs"
  optPrintOCaml <-
    switch $
      long "print-ocaml"
        <> help "Whether to print the generated OIL programs"
  optNamePrefix <-
    strOption $
      long "prefix"
        <> metavar "PREFIX"
        <> value "$"
        <> showDefault
        <> help "Prefix to the internal names (only affects printing)"
  optPrintTokens <-
    switch $
      long "print-tokens"
        <> help "Whether to print tokens (for internal debugging)"
  optPrintSource <-
    switch $
      long "print-source"
        <> help "Whether to print the source code (for internal debugging)"
  optReadable <-
    switch $
      long "readable"
        <> help "Make the generated programs more readable (for debugging)"
  optWidth <-
    optional $
      option auto $
        long "width"
          <> short 'w'
          <> help "Window width (for debugging pretty printer)"
  return
    Options
      { optCode = "",
        optFlagNoSimplify = optFlagNoSimplify || optFlagNoOptimization,
        optFlagNoInline = optFlagNoInline || optFlagNoOptimization,
        optFlagNoMemo = optFlagNoMemo || optFlagNoOptimization,
        optFlagNoGuardReshape = optFlagNoGuardReshape || optFlagNoOptimization,
        ..
      }

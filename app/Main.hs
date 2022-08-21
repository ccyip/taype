{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Options.Applicative
import Taype
import Taype.Environment

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
  return Options {..}

main :: IO ()
main = run =<< execParser (info (opts <**> helper) helpMod)
  where
    helpMod =
      fullDesc <> header "taype - a programming language with data types and tape"

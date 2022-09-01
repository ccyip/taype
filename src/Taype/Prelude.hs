{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Common utilities.
module Taype.Prelude
  ( -- * Common types
    Doc,
    Options (..),

    -- * Common functions
    oops,
  )
where

import qualified Prettyprinter as PP

-- | Document type for all sorts of printing
type Doc = PP.Doc ()

-- | Command line options
data Options = Options
  { optFile :: FilePath,
    optCode :: Text,
    optInternalNames :: Bool,
    optNamePrefix :: Text,
    optPrintLabels :: Bool,
    optPrintTokens :: Bool,
    optPrintSource :: Bool,
    optWidth :: Maybe Int
  }
  deriving stock (Eq, Show)

oops :: Text -> a
oops msg = error $ "Oops! This should not happen:\n" <> msg

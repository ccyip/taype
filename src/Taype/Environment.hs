{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Environment including options, typing context, locations, etc
module Taype.Environment
  ( Env (..),
    Options (..),
    defaultOptions,
    GCtx,
    initGCtx,
  )
where

import Taype.Syntax

data Env a = Env {options :: Options, gctx :: GCtx a}

data Options = Options
  { optPrintTokens :: Bool,
    optPrintLabels :: Bool,
    optInternalNames :: Bool,
    optNamePrefix :: Text
  }

defaultOptions :: Options
defaultOptions =
  Options
    { optPrintTokens = False,
      optPrintLabels = False,
      optInternalNames = False,
      optNamePrefix = "$"
    }

type GCtx a = HashMap Text (Def a)

initGCtx :: GCtx a
initGCtx = mempty

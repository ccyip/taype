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
    GCtx,
  )
where

import Taype.Syntax

data Env a = Env {options :: Options, gctx :: GCtx a}

data Options = Options
  { optPrintTokens :: Bool,
    optPrintLabels :: Bool,
    optInternalNames :: Bool
  }

type GCtx a = HashMap Text (NamedDef a)

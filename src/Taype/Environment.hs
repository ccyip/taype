{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Environment including options, typing context, locations, etc
module Taype.Environment
  ( -- * Environment
    Env (..),

    -- * Commandline options
    Options (..),

    -- * Global context
    GCtx,
    preludeGCtx,

    -- * Local context
    Ctx,

    -- * Type checking monad
    TcM,
    runTcM,

    -- * Manipulating environment
    getLabel,
    withLabel,
  )
where

import Taype.Error
import Taype.Name
import Taype.Syntax

data Env = Env
  { options :: Options,
    -- Global definition context. Function types must be in core Taype ANF and
    -- well-kinded before type checking
    gctx :: GCtx Name,
    -- Local typing context. Every type must be in core Taype ANF and
    -- well-kinded
    ctx :: Ctx Name,
    -- Default label for inference
    label :: Label
  }

data Options = Options
  { optFile :: FilePath,
    optInternalNames :: Bool,
    optNamePrefix :: Text,
    optPrintLabels :: Bool,
    optPrintTokens :: Bool,
    optPrintSource :: Bool,
    optWidth :: Maybe Int
  }
  deriving stock (Eq, Show)

type GCtx a = HashMap Text (Def a)

preludeGCtx :: GCtx a
preludeGCtx = mempty

type Ctx a = [(a, (Expr a, Label))]

-- | The type checking monad
type TcM = FreshT (ReaderT Env (ExceptT Err IO))

runTcM :: Env -> TcM a -> ExceptT Err IO a
runTcM env m = runReaderT (runFreshT m) env

getLabel ::  MonadReader Env m => m Label
getLabel = do
  Env {..} <- ask
  return label

withLabel :: MonadReader Env m => Label -> m a -> m a
withLabel l = local (\Env {..} -> Env {label = l, ..})

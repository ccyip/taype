{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

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
    lookupDef,
    lookupTy,
    extendCtx,
    extendCtx1,
    getLabel,
    withLabel,
  )
where

import Data.HashMap.Strict ((!?))
import Data.List (lookup)
import Taype.Error
import Taype.Name
import Taype.Syntax

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Global definition context
    --
    -- Function types must be well-kinded and in core Taype ANF before type
    -- checking.
    gctx :: GCtx Name,
    -- | Local typing context
    --
    -- Every type must be well-kinded and in core Taype ANF.
    ctx :: Ctx Name,
    -- | Binder context, used for pretty printing
    bctx :: BCtx Name,
    -- | Default label for inference
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

type Ctx a = [(a, (Ty a, Label))]

type BCtx a = [(a, Binder)]

-- | The initial context with builtin functions
preludeGCtx :: GCtx a
preludeGCtx = mempty

-- | The type checking monad
type TcM = FreshT (ReaderT Env (ExceptT Err IO))

runTcM :: Env -> TcM a -> ExceptT Err IO a
runTcM env m = runReaderT (runFreshT m) env

-- | Look up a definition in the global context.
lookupDef :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupDef x = do
  Env {..} <- ask
  return $ gctx !? x

-- | Look up a type and its label in the typing context.
lookupTy :: MonadReader Env m => Name -> m (Maybe (Ty Name, Label))
lookupTy x = do
  Env {..} <- ask
  return $ lookup x ctx

-- | Extend the typing context.
--
-- To maintain the invariant, the given types have to be well-kinded and in core
-- Taype ANF.
extendCtx ::
  MonadReader Env m => [(Name, Ty Name, Label, Maybe Binder)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {..} =
      Env
        { ctx = (ctx1 <$> xs) <> ctx,
          bctx = mapMaybe bctx1 xs <> bctx,
          ..
        }
    ctx1 (x, t, l, _) = (x, (t, l))
    bctx1 (x, _, _, mb) = (x,) <$> mb

-- | Extend the typing context with one entry.
extendCtx1 ::
  MonadReader Env m => Name -> Ty Name -> Label -> Maybe Binder -> m a -> m a
extendCtx1 x t l mb = extendCtx [(x, t, l, mb)]

getLabel :: MonadReader Env m => m Label
getLabel = do
  Env {..} <- ask
  return label

withLabel :: MonadReader Env m => Label -> m a -> m a
withLabel l = local (\Env {..} -> Env {label = l, ..})

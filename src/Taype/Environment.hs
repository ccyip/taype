{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
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
    initEnv,

    -- * Commandline options
    Options (..),

    -- * Global context
    GCtx,
    preludeGCtx,

    -- * Local context
    Ctx,

    -- * Definition checking monad
    DcM,
    runDcM,

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
    getLoc,
    withLoc,
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
    -- Function types, constructor and OADT type arguments must be well-kinded
    -- and in core Taype ANF before type checking. The labels of function
    -- definitions are also elaborated.
    gctx :: GCtx Name,
    -- | Local typing context
    --
    -- Every type must be well-kinded and in core Taype ANF.
    ctx :: Ctx Name,
    -- | Binder context, used for pretty printing
    bctx :: BCtx Name,
    -- | Location of the current expression
    loc :: Int,
    -- | Default label for inference
    label :: Label
  }

-- | Make an initial environment.
--
-- Initially label does not matter because it should be replaced according to
-- the context.
initEnv :: Options -> GCtx Name -> Env
initEnv options gctx =
  Env
    { ctx = [],
      bctx = [],
      loc = -1,
      label = LeakyL,
      ..
    }

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

type GCtx a = HashMap Text (Def a)

type Ctx a = [(a, (Ty a, Label))]

type BCtx a = [(a, Binder)]

-- | The definition checking monad
type DcM = ReaderT Options (ExceptT Err IO)

runDcM :: Options -> DcM a -> ExceptT Err IO a
runDcM = usingReaderT

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

getLoc :: MonadReader Env m => m Int
getLoc = do
  Env {..} <- ask
  return loc

withLoc :: MonadReader Env m => Int -> m a -> m a
withLoc l = local (\Env {..} -> Env {loc = l, ..})

-- | The initial context with builtin functions
preludeGCtx :: GCtx a
preludeGCtx =
  fromList $
    builtin
      <$> [ ("+", [TInt, TInt], TInt, JoinStrategy),
            ("~+", [OInt, OInt], OInt, SafeStrategy),
            ("-", [TInt, TInt], TInt, JoinStrategy),
            ("~-", [OInt, OInt], OInt, SafeStrategy),
            ("==", [TInt, TInt], TBool, JoinStrategy),
            ("~=", [OInt, OInt], OBool, SafeStrategy),
            ("<=", [TInt, TInt], TBool, JoinStrategy),
            ("~<=", [OInt, OInt], OBool, SafeStrategy),
            ("s_bool", [TBool], OBool, JoinStrategy),
            ("s_int", [TInt], OInt, JoinStrategy),
            ("r_int", [OInt], TInt, LeakyStrategy)
          ]

builtin :: (Text, [Ty a], Ty a, LabelPolyStrategy) -> (Text, Def a)
builtin (name, paraTypes, resType, strategy) = (name, BuiltinDef {..})

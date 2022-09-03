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
-- Environments and contexts.
module Taype.Environment
  ( -- * Environment
    Env (..),
    initEnv,

    -- * Contexts
    GCtx,
    TCtx,
    BCtx,

    -- * Manipulating environment
    lookupDef,
    lookupTy,
    extendCtx,
    extendCtx1,
    withLabel,
    withLoc,
    mayWithLoc,
    withCur,

    -- * Prelude context
    preludeGCtx,
  )
where

import Data.HashMap.Strict ((!?))
import Data.List (lookup)
import Taype.Prelude
import Taype.Name
import Taype.Syntax

----------------------------------------------------------------
-- Environment

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Global context
    --
    -- Function types, constructor arguments and OADT type arguments must be
    -- well-kinded and in (fully-annotated) core taype ANF before type checking.
    gctx :: GCtx Name,
    -- | Local typing context
    --
    -- Every type must be well-kinded and in (fully-annotated) core taype ANF.
    tctx :: TCtx Name,
    -- | Binder context, used for pretty printing
    bctx :: BCtx Name,
    -- | Current expression for error reporting
    cur :: Expr Name,
    -- | Location of the current expression for error reporting
    loc :: Int,
    -- | Default label for inference
    label :: Label
  }

-- | Make an initial environment.
--
-- Some fields are intantiated arbitrarily, because they will be replaced later
-- according to the context.
initEnv :: Options -> GCtx Name -> Env
initEnv options gctx =
  Env
    { tctx = [],
      bctx = [],
      loc = -1,
      cur = V 0,
      label = LeakyL,
      ..
    }

----------------------------------------------------------------
-- Contexts

type GCtx a = HashMap Text (Def a)

type TCtx a = [(a, (Ty a, Label))]

type BCtx a = [(a, Binder)]

----------------------------------------------------------------
-- Manipulating environment

-- | Look up a definition in the global context.
lookupDef :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupDef x = do
  Env {..} <- ask
  return $ gctx !? x

-- | Look up a type and its label in the typing context.
lookupTy :: MonadReader Env m => Name -> m (Maybe (Ty Name, Label))
lookupTy x = do
  Env {..} <- ask
  return $ lookup x tctx

-- | Extend the typing context.
--
-- To maintain the invariant, the given types have to be well-kinded and in core
-- taype ANF.
extendCtx ::
  MonadReader Env m => [(Name, Ty Name, Label, Maybe Binder)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {..} =
      Env
        { tctx = (ctx1 <$> xs) <> tctx,
          bctx = mapMaybe bctx1 xs <> bctx,
          ..
        }
    ctx1 (x, t, l, _) = (x, (t, l))
    bctx1 (x, _, _, mb) = (x,) <$> mb

-- | Extend the typing context with one entry.
extendCtx1 ::
  MonadReader Env m => Name -> Ty Name -> Label -> Maybe Binder -> m a -> m a
extendCtx1 x t l mb = extendCtx [(x, t, l, mb)]

withLabel :: MonadReader Env m => Label -> m a -> m a
withLabel l = local (\Env {..} -> Env {label = l, ..})

withLoc :: MonadReader Env m => Int -> m a -> m a
withLoc l = local (\Env {..} -> Env {loc = l, ..})

mayWithLoc :: MonadReader Env m => Maybe Int -> m a -> m a
mayWithLoc (Just l) = withLoc l
mayWithLoc _ = id

withCur :: MonadReader Env m => Expr Name -> m a -> m a
withCur e = local (\Env {..} -> Env {cur = e, ..})

----------------------------------------------------------------
-- Prelude context

-- | The prelude context includes builtin functions.
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

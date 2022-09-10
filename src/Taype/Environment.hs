{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
    TCtx (..),
    BCtx,

    -- * Manipulating environment
    lookupGSig,
    lookupGDef,
    lookupTy,
    extendCtx,
    extendCtx1,
    withLabel,
    withLoc,
    mayWithLoc,
    withCur,

    -- * Prelude context
    preludeGCtx,

    -- * Pretty printer
    cuteDefs,
  )
where

import Data.HashMap.Strict ((!?))
import Data.List (lookup)
import Relude.Extra.Bifunctor
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Name
import Taype.Prelude
import Taype.Syntax

----------------------------------------------------------------
-- Environment

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Global signature context
    --
    -- We reuse the same 'GCtx' data as in 'gdctx', but only use the signature
    -- part.
    gsctx :: GCtx Name,
    -- | Global definition context
    --
    -- We reuse the same 'GCtx' data as in 'gtctx', but only use the definition
    -- part.
    gdctx :: GCtx Name,
    -- | Local typing context
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
-- Some fields are intantiated arbitrarily, because they will be replaced later.
initEnv :: Options -> GCtx Name -> GCtx Name -> Env
initEnv options gsctx gdctx =
  Env
    { tctx = TCtx [],
      bctx = [],
      loc = -1,
      cur = V 0,
      label = LeakyL,
      ..
    }

----------------------------------------------------------------
-- Contexts

type GCtx a = HashMap Text (Def a)

newtype TCtx a = TCtx {unTCtx :: [(a, (Ty a, Label))]}

instance Functor TCtx where
  fmap f (TCtx tctx) = TCtx $ bimapF f (first (f <$>)) tctx

type BCtx a = [(a, Binder)]

----------------------------------------------------------------
-- Manipulating environment

-- | Look up a definition in the global typing context.
lookupGSig :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupGSig x = do
  Env {..} <- ask
  return $ gsctx !? x

-- | Look up a definition in the global definition context.
lookupGDef :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupGDef x = do
  Env {..} <- ask
  return $ gdctx !? x

-- | Look up a type and its label in the typing context.
lookupTy :: MonadReader Env m => Name -> m (Maybe (Ty Name, Label))
lookupTy x = do
  TCtx tctx <- asks tctx
  return $ lookup x tctx

-- | Extend the typing context.
--
-- To maintain the invariant, the given types have to be well-kinded and in core
-- taype ANF.
extendCtx ::
  MonadReader Env m => [(Name, Ty Name, Label, Maybe Binder)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {tctx = TCtx tctx, ..} =
      Env
        { tctx = TCtx $ (ctx1 <$> xs) <> tctx,
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

----------------------------------------------------------------
-- Pretty printer

instance Cute (TCtx Text) where
  cute (TCtx tctx) = do
    docs <- mapM go tctx
    return $
      hang $
        "Typing context" <> colon <> hardline
          <> if null tctx then "<empty>" else sepWith hardline docs
    where
      go (x, (t, l)) = cuteBinder x (Just l) (Just t)

-- | Pretty printer for taype definitions
cuteDefs :: Options -> GCtx Text -> [Text] -> Doc
cuteDefs options gctx =
  foldMap $ \name -> go name <> hardline <> hardline
  where
    go name =
      cuteDef options name $
        fromMaybe (oops "definition not in context") (gctx !? name)

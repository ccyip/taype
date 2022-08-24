{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Utilities about naming, such as fresh name generator.
module Taype.Name
  ( Name,

    -- * Fresh name generator
    FreshT,
    MonadFresh,
    runFreshT,
    FreshM,
    runFreshM,
    fresh,
    freshWith,

    -- * Specialized locally nameless abstraction and instantiation
    abstract1By,
    abstract2By,
    abstractManyBy,
    instantiate1By,
    instantiate2By,
    instantiateManyBy,
    instantiate1Name,
    instantiate2Names,
    instantiateNames,
  )
where

import Bound
import Data.List (findIndex)
import Taype.Error

-- | Names are integers
type Name = Int

-- | Fresh name monad transformer is just state monad transformer
type FreshT = StateT Name

type MonadFresh = MonadState Name

runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = evalStateT m 0

-- | Fresh name monad
type FreshM = FreshT Identity

runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshT

-- | Generate a fresh name as integer
fresh :: MonadFresh m => m Int
fresh = do
  n <- get
  put (n + 1)
  return n

-- | Generate a fresh name given a transform function
freshWith :: MonadFresh m => (Int -> Text) -> m Text
freshWith to = to <$> fresh

abstract1By :: Monad f => (a -> b -> Bool) -> b -> f a -> Scope () f a
abstract1By eq b = abstract $ \a ->
  if eq a b
    then Just ()
    else Nothing

abstract2By :: Monad f => (a -> b -> Bool) -> b -> b -> f a -> Scope Bool f a
abstract2By eq left right = abstract $ \a ->
  if
      | eq a left -> Just True
      | eq a right -> Just False
      | otherwise -> Nothing

abstractManyBy :: Monad f => (a -> b -> Bool) -> [b] -> f a -> Scope Int f a
abstractManyBy eq bs = abstract $ \a -> findIndex (eq a) bs

instantiate1By :: Monad f => (b -> f a) -> b -> Scope n f a -> f a
instantiate1By proj = instantiate . const . proj

instantiate2By :: Monad f => (b -> f a) -> b -> b -> Scope Bool f a -> f a
instantiate2By proj left right = instantiate $ \i ->
  proj $ if i then left else right

instantiateManyBy :: Monad f => (b -> f a) -> [b] -> Scope Int f a -> f a
instantiateManyBy proj bs = instantiate $ \i ->
  case bs !!? i of
    Just b -> proj b
    Nothing -> oops "Out-of-bound instantiation"

instantiate1Name :: Monad f => a -> Scope n f a -> f a
instantiate1Name = instantiate1By return

instantiate2Names :: Monad f => a -> a -> Scope Bool f a -> f a
instantiate2Names = instantiate2By return

instantiateNames :: Monad f => [a] -> Scope Int f a -> f a
instantiateNames = instantiateManyBy return

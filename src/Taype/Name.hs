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
    freshes,
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
    abstract2,
    abstractMany,
    instantiate2,
    instantiateMany,

    -- * Unbound-style functions
    unbind1By,
    unbind2By,
    unbindManyBy,
    unbind1,
    unbind2,
    unbindMany,
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

-- | Generate a fresh name
fresh :: MonadFresh m => m Name
fresh = do
  n <- get
  put (n + 1)
  return n

-- | Generate many fresh names
freshes :: MonadFresh m => Int -> m [Name]
freshes k = do
  n <- get
  put (n + k)
  return [n .. n + k - 1]

-- | Generate a fresh name given a transform function
freshWith :: MonadFresh m => (Name -> Text) -> m Text
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

abstract2 :: (Monad f, Eq a) => a -> a -> f a -> Scope Bool f a
abstract2 = abstract2By (==)

abstractMany :: (Monad f, Eq a) => [a] -> f a -> Scope Int f a
abstractMany = abstractManyBy (==)

instantiate2 :: Monad f => f a -> f a -> Scope Bool f a -> f a
instantiate2 = instantiate2By id

instantiateMany :: Monad f => [ f a ] -> Scope Int f a -> f a
instantiateMany = instantiateManyBy id

unbind1By :: (Monad m, Monad f) => m a -> Scope n f a -> m (a, f a)
unbind1By gen bnd = do
  x <- gen
  return (x, instantiate1Name x bnd)

unbind2By ::
  (Monad m, Monad f) => m a -> m a -> Scope Bool f a -> m (a, a, f a)
unbind2By gen1 gen2 bnd = do
  x1 <- gen1
  x2 <- gen2
  return (x1, x2, instantiate2Names x1 x2 bnd)

unbindManyBy :: (Monad m, Monad f) => m [a] -> Scope Int f a -> m ([a], f a)
unbindManyBy gen bnd = do
  xs <- gen
  return (xs, instantiateNames xs bnd)

unbind1 :: (MonadFresh m, Monad f) => Scope n f Name -> m (Name, f Name)
unbind1 = unbind1By fresh

unbind2 :: (MonadFresh m, Monad f) => Scope Bool f Name -> m (Name, Name, f Name)
unbind2 = unbind2By fresh fresh

unbindMany ::
  (MonadFresh m, Monad f) => Int -> Scope Int f Name -> m ([Name], f Name)
unbindMany = unbindManyBy . freshes

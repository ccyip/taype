{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Naming related utilities.
module Taype.Name
  ( Name,

    -- * Fresh name generator
    FreshT (..),
    MonadFresh (..),
    runFreshT,
    contFreshT,
    FreshM,
    runFreshM,
    contFreshM,
    fresh,
    freshes,
    badName,

    -- * Specialized locally nameless abstraction and instantiation
    ScopeOps (..),
    abstract_,
    instantiate_,
    instantiateName,

    -- * Unbound-style functions
    unbindBy,
    unbind1,
    unbind2,
    unbindMany,
    unbind1With,
    unbind2With,
    unbindManyWith,
  )
where

import Bound
import Control.Monad.Except
import Control.Monad.Writer
import Data.List (findIndex)
import Taype.Prelude

-- | Names are integers.
type Name = Int

----------------------------------------------------------------
-- Fresh name generator

-- | Fresh name class is similar to 'MonadState' class.
class Monad m => MonadFresh m where
  getFresh :: m Name
  putFresh :: Name -> m ()

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
  getFresh = lift getFresh
  putFresh = lift . putFresh

-- | Fresh name monad transformer is just state monad transformer.
newtype FreshT m a = FreshT {unFreshT :: StateT Name m a}
  deriving newtype
    ( Functor,
      Applicative,
      Monad,
      MonadFail,
      MonadIO,
      MonadTrans,
      MonadReader r,
      MonadWriter w,
      MonadError e
    )

instance Monad m => MonadFresh (FreshT m) where
  getFresh = FreshT get
  putFresh n = FreshT $ put n

instance MonadState s m => MonadState s (FreshT m) where
  get = lift get
  put = lift . put

runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = contFreshT m 0

contFreshT :: Monad m => FreshT m a -> Int -> m a
contFreshT (FreshT m) = evalStateT m

-- | Fresh name monad
type FreshM = FreshT Identity

runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshT

contFreshM :: FreshM a -> Int -> a
contFreshM m = runIdentity . contFreshT m

-- | Generate a fresh name.
fresh :: MonadFresh m => m Name
fresh = do
  n <- getFresh
  putFresh (n + 1)
  return n

-- | Generate many fresh names.
freshes :: MonadFresh m => Int -> m [Name]
freshes k = do
  n <- getFresh
  putFresh (n + k)
  return [n .. n + k - 1]

-- | A name that never gets generated.
badName :: Name
badName = -1

----------------------------------------------------------------
-- Specialized locally nameless abstraction and instantiation

class ScopeOps s b b' | s b -> b' where
  abstractBy :: Monad f => (a -> b -> Bool) -> b' -> f a -> Scope s f a
  instantiateBy :: Monad f => (b -> f a) -> b' -> Scope s f a -> f a

-- | Abstract and instantiate for one bound variable.
instance ScopeOps () b b where
  abstractBy eq b = abstract $ \a ->
    if eq a b
      then Just ()
      else Nothing
  instantiateBy proj = instantiate . const . proj

-- | Abstract and instantiate for two bound variables.
instance ScopeOps Bool b (b, b) where
  abstractBy eq (left, right) = abstract $ \a ->
    if
        | eq a left -> Just True
        | eq a right -> Just False
        | otherwise -> Nothing
  instantiateBy proj (left, right) = instantiate $ \i ->
    proj $ if i then left else right

-- | Abstract and instantiate for many bound variables.
instance ScopeOps Int b [b] where
  abstractBy eq bs = abstract $ \a -> findIndex (eq a) bs
  instantiateBy proj bs = instantiate $ \i ->
    case bs !!? i of
      Just b -> proj b
      Nothing -> oops "Out-of-bound instantiation"

abstract_ :: (ScopeOps s a b', Monad f, Eq a) => b' -> f a -> Scope s f a
abstract_ = abstractBy (==)

instantiate_ :: (ScopeOps s (f a) b', Monad f) => b' -> Scope s f a -> f a
instantiate_ = instantiateBy id

instantiateName :: (ScopeOps s a b', Monad f) => b' -> Scope s f a -> f a
instantiateName = instantiateBy return

----------------------------------------------------------------
-- Unbound-style functions

unbindBy ::
  (ScopeOps s a b', Monad m, Monad f) => m b' -> Scope s f a -> m (b', f a)
unbindBy gen bnd = do
  x <- gen
  return (x, instantiateName x bnd)

unbind1 :: (MonadFresh m, Monad f) => Scope () f Name -> m (Name, f Name)
unbind1 = unbindBy fresh

unbind2 ::
  (MonadFresh m, Monad f) =>
  Scope Bool f Name ->
  m ((Name, Name), f Name)
unbind2 = unbindBy $ (,) <$> fresh <*> fresh

unbindMany ::
  (MonadFresh m, Monad f) => Int -> Scope Int f Name -> m ([Name], f Name)
unbindMany = unbindBy . freshes

unbindWithBy ::
  (ScopeOps s Name b', MonadFresh m, Monad f) =>
  (Scope s f Name -> m (b', f Name)) ->
  Scope s f Name ->
  Scope s f Name ->
  m (b', f Name, f Name)
unbindWithBy ub bnd bnd' = do
  (x, body) <- ub bnd
  let body' = instantiateName x bnd'
  return (x, body, body')

unbind1With ::
  (MonadFresh m, Monad f) =>
  Scope () f Name ->
  Scope () f Name ->
  m (Name, f Name, f Name)
unbind1With = unbindWithBy unbind1

unbind2With ::
  (MonadFresh m, Monad f) =>
  Scope Bool f Name ->
  Scope Bool f Name ->
  m ((Name, Name), f Name, f Name)
unbind2With = unbindWithBy unbind2

unbindManyWith ::
  (MonadFresh m, Monad f) =>
  Int ->
  Scope Int f Name ->
  Scope Int f Name ->
  m ([Name], f Name, f Name)
unbindManyWith n = unbindWithBy $ unbindMany n

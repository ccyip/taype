{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Fresh name generator.
module Taype.Fresh
  ( Name,
    FreshT,
    runFreshT,
    Fresh,
    runFresh,
    fresh,
    freshWith,
    freshName,
  )
where

-- | Names are integers
type Name = Int

-- | Fresh name monad transformer is just state monad transformer
type FreshT m a = StateT Name m a

runFreshT :: Monad m => FreshT m a -> m a
runFreshT m = evalStateT m 0

-- | Fresh name monad
type Fresh a = FreshT Identity a

runFresh :: Fresh a -> a
runFresh = runIdentity . runFreshT

-- | Generate a fresh name as integer
fresh :: Monad m => FreshT m Int
fresh = do
  n <- get
  put (n + 1)
  return n

-- | Generate a fresh name with a string prefix
freshWith :: Monad m => Text -> FreshT m Text
freshWith prefix = do
  n <- fresh
  return $ prefix <> show n

-- | Generate a fresh name with prefix \"$\"
freshName :: Monad m => FreshT m Text
freshName = freshWith "$"
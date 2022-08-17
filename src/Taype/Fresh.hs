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
    freshes,
    freshesWith,
    freshNames,
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

-- | Generate a fresh name given a transform function
freshWith :: Monad m => (Int -> Text) -> FreshT m Text
freshWith to = to <$> fresh

-- | Generate a fresh name
freshName :: Monad m => FreshT m Text
freshName = freshWith toName

-- | Generate some fresh integers
freshes :: Monad m => Int -> FreshT m [Int]
freshes k = do
  n <- get
  put (n + k)
  return $ take k [n ..]

-- | Generate some fresh names given a transform function
freshesWith :: Monad m => (Int -> Text) -> Int -> FreshT m [Text]
freshesWith to k = to <<$>> freshes k

-- | Generate some fresh names
freshNames :: Monad m => Int -> FreshT m [Text]
freshNames = freshesWith toName

toName :: Int -> Text
toName n = "$" <> show n

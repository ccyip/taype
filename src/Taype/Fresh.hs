{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
    MonadFresh,
    runFreshT,
    FreshM,
    runFreshM,
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

-- | Generate a fresh name
freshName :: MonadFresh m => m Text
freshName = freshWith toName

-- | Generate some fresh integers
freshes :: MonadFresh m => Int -> m [Int]
freshes k = do
  n <- get
  put (n + k)
  return $ take k [n ..]

-- | Generate some fresh names given a transform function
freshesWith :: MonadFresh m => (Int -> Text) -> Int -> m [Text]
freshesWith to k = to <<$>> freshes k

-- | Generate some fresh names
freshNames :: MonadFresh m => Int -> m [Text]
freshNames = freshesWith toName

toName :: Int -> Text
toName n = "$" <> show n

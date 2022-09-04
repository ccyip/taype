{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Common utilities.
--
-- Some of the functions are taken from the package extra.
module Taype.Prelude
  ( -- * Common types
    Doc,
    Options (..),

    -- * Common functions
    oops,
    curry3,
    uncurry3,
    firstM,
    secondM,
    mustClosed,
    findAndDel,
  )
where

import Bound
import qualified Prettyprinter as PP

-- | Document type for all sorts of printing
type Doc = PP.Doc ()

-- | Command line options
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

oops :: Text -> a
oops msg = error $ "Oops! This should not happen:\n" <> msg

curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f a b c = f (a, b, c)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f ~(a, b, c) = f a b c

firstM :: Functor m => (a -> m a') -> (a, b) -> m (a', b)
firstM f ~(a, b) = (,b) <$> f a

secondM :: Functor m => (b -> m b') -> (a, b) -> m (a, b')
secondM f ~(a, b) = (a,) <$> f b

mustClosed :: Traversable f => Text -> f a -> f b
mustClosed what a = fromMaybe (oops (what <> " is not closed")) $ closed a

findAndDel :: (a -> Bool) -> [a] -> Maybe (a, [a])
findAndDel _ [] = Nothing
findAndDel p (x : xs)
  | p x = Just (x, xs)
  | otherwise = second (x :) <$> findAndDel p xs

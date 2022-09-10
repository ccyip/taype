{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- General-purpose functions that are not in the standard library.
--
-- Some of the functions are taken from the package extra.
module Taype.Prelude
  ( oops,
    curry3,
    uncurry3,
    firstM,
    secondM,
    findAndDel,
  )
where

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

findAndDel :: (a -> Bool) -> [a] -> Maybe (a, [a])
findAndDel _ [] = Nothing
findAndDel p (x : xs)
  | p x = Just (x, xs)
  | otherwise = second (x :) <$> findAndDel p xs

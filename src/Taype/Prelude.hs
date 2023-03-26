{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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
    curry4,
    uncurry4,
    firstM,
    secondM,
    findAndDel,
    snoc,
    flip2,
  )
where

oops :: Text -> a
oops msg = error $ "Oops! This should not happen:\n" <> msg

curry3 :: ((x1, x2, x3) -> r) -> x1 -> x2 -> x3 -> r
curry3 f x1 x2 x3 = f (x1, x2, x3)

uncurry3 :: (x1 -> x2 -> x3 -> r) -> (x1, x2, x3) -> r
uncurry3 f ~(x1, x2, x3) = f x1 x2 x3

curry4 :: ((x1, x2, x3, x4) -> r) -> x1 -> x2 -> x3 -> x4 -> r
curry4 f x1 x2 x3 x4 = f (x1, x2, x3, x4)

uncurry4 :: (x1 -> x2 -> x3 -> x4 -> r) -> (x1, x2, x3, x4) -> r
uncurry4 f ~(x1, x2, x3, x4) = f x1 x2 x3 x4

firstM :: Functor m => (a -> m a') -> (a, b) -> m (a', b)
firstM f ~(a, b) = (,b) <$> f a

secondM :: Functor m => (b -> m b') -> (a, b) -> m (a, b')
secondM f ~(a, b) = (a,) <$> f b

findAndDel :: (a -> Bool) -> [a] -> Maybe (a, [a])
findAndDel _ [] = Nothing
findAndDel p (x : xs)
  | p x = Just (x, xs)
  | otherwise = second (x :) <$> findAndDel p xs

snoc :: [a] -> a -> [a]
snoc xs x = xs <> [x]

flip2 :: (c -> a -> b -> d) -> a -> b -> c -> d
flip2 f a b c = f c a b

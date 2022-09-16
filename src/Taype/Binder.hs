{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Binders mostly used for user interfacing.
module Taype.Binder
  ( Binder,
    BinderM (..),
    toBinder,
    fromBinder,
    isBinderName,
    binderNameEq,
    findDupBinderName,
    abstractBinder,
    instantiateBinder,
  )
where

import Bound
import Data.List (groupBy)
import Taype.Name
import Taype.Prelude

-- | A binder is either a name, or anonymous, i.e. \"_\", with location.
type Binder = BinderM Text

-- | Generalized binders
data BinderM a = Named Int a | Anon
  deriving stock (Eq, Show)

instance IsString a => IsString (BinderM a) where
  fromString = toBinder . fromString

instance ToText a => ToText (BinderM a) where
  toText (Named _ a) = toText a
  toText Anon = "_"

toBinder :: a -> BinderM a
toBinder = Named (-1)

fromBinder :: BinderM a -> a
fromBinder (Named _ name) = name
fromBinder Anon = oops "Instantiating an anonymous binder"

-- | Check if the binder has a particular name.
isBinderName :: Eq a => a -> BinderM a -> Bool
isBinderName x (Named _ y) = x == y
isBinderName _ Anon = False

-- | Check if two binders have the same name. Two anonymous binders NEVER have
-- the same name.
binderNameEq :: Eq a => BinderM a -> BinderM a -> Bool
binderNameEq (Named _ x) (Named _ y) = x == y
binderNameEq _ _ = False

-- | Return 'Nothing' if the list of binders do not has duplicate names, or
-- 'Just' the duplicate binder.
findDupBinderName :: Eq a => [BinderM a] -> Maybe (BinderM a)
findDupBinderName binders = find ((> 1) . length) groups >>= viaNonEmpty head
  where
    groups = groupBy binderNameEq binders

abstractBinder ::
  (ScopeOps s (BinderM a) b', Monad f, Eq a) => b' -> f a -> Scope s f a
abstractBinder = abstractBy isBinderName

instantiateBinder ::
  (ScopeOps s (BinderM a) b', Monad f) => b' -> Scope s f a -> f a
instantiateBinder = instantiateBy $ return . fromBinder

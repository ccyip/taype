{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Uniplate-style infrastructure that works with the bound library and fresh
-- name generator. Some of the functions are taken or modified from the uniplate
-- library.
module Taype.Plate
  ( PlateM,
    plateM,
    BiplateM,
    biplateM,
    transformM,
    transformBiM,
  )
where

import Taype.Name

class PlateM on where
  plateM :: MonadFresh m => (on -> m on) -> on -> m on

class PlateM to => BiplateM from to where
  biplateM :: MonadFresh m => (to -> m to) -> from -> m from

transformM :: (MonadFresh m, PlateM on) => (on -> m on) -> on -> m on
transformM f = go
  where
    go x = plateM go x >>= f

transformBiM ::
  (MonadFresh m, BiplateM from to) =>
  (to -> m to) ->
  from ->
  m from
transformBiM f = biplateM (transformM f)
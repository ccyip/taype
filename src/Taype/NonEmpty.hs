-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Extra functions for 'NonEmpty'.
module Taype.NonEmpty
  ( module Data.List.NonEmpty,
    unzip3,
    unzip4,
    zipWith3,
    zipWithM,
    zipWithM_,
    zipWith3M,
    zipWith3M_,
  )
where

import qualified Data.List as L
import Data.List.NonEmpty hiding ((:|))
import qualified Data.List.NonEmpty as NE
import Prelude hiding (unzip3, zipWithM, zipWithM_)

unzip3 ::
  NonEmpty (a, b, c) ->
  (NonEmpty a, NonEmpty b, NonEmpty c)
unzip3 ~((a, b, c) :| xs) =
  let (as, bs, cs) = L.unzip3 xs
   in (a :| as, b :| bs, c :| cs)

unzip4 ::
  NonEmpty (a, b, c, d) ->
  (NonEmpty a, NonEmpty b, NonEmpty c, NonEmpty d)
unzip4 ~((a, b, c, d) :| xs) =
  let (as, bs, cs, ds) = L.unzip4 xs
   in (a :| as, b :| bs, c :| cs, d :| ds)

zipWith3 ::
  (a -> b -> c -> d) ->
  NonEmpty a ->
  NonEmpty b ->
  NonEmpty c ->
  NonEmpty d
zipWith3 f ~(a :| as) ~(b :| bs) ~(c :| cs) = f a b c :| L.zipWith3 f as bs cs

zipWithM ::
  Applicative m =>
  (a -> b -> m c) ->
  NonEmpty a ->
  NonEmpty b ->
  m (NonEmpty c)
zipWithM f as bs = sequenceA $ NE.zipWith f as bs

zipWithM_ ::
  Applicative m =>
  (a -> b -> m c) ->
  NonEmpty a ->
  NonEmpty b ->
  m ()
zipWithM_ f as bs = sequenceA_ $ NE.zipWith f as bs

zipWith3M ::
  Applicative m =>
  (a -> b -> c -> m d) ->
  NonEmpty a ->
  NonEmpty b ->
  NonEmpty c ->
  m (NonEmpty d)
zipWith3M f as bs cs = sequenceA $ zipWith3 f as bs cs

zipWith3M_ ::
  Applicative m =>
  (a -> b -> c -> m d) ->
  NonEmpty a ->
  NonEmpty b ->
  NonEmpty c ->
  m ()
zipWith3M_ f as bs cs = sequenceA_ $ zipWith3 f as bs cs

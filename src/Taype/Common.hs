{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Common data types and utilities.
module Taype.Common
  ( Options (..),
    Label (..),
    AppKind (..),
    CaseAlt (..),
    caseAlt_,
    mustClosed,

    -- * Common names
    oblivAccent,
    oblivName,
    leakyAccent,
    leakyName,
    infixes,
    oblivInfixes,
    leakyInfixes,
    allInfixes,
    isInfix,
  )
where

import Algebra.Lattice
import Bound
import Data.Functor.Classes
import Prettyprinter (Pretty)
import qualified Prettyprinter as PP
import Taype.Binder
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Text.Show

-- | Command line options
data Options = Options
  { optFile :: FilePath,
    optCode :: Text,
    optInternalNames :: Bool,
    optNoFlattenLets :: Bool,
    optNamePrefix :: Text,
    optPrintCore :: Bool,
    optPrintLabels :: Bool,
    optPrintTokens :: Bool,
    optPrintSource :: Bool,
    optWidth :: Maybe Int
  }
  deriving stock (Eq, Show)

-- | A leakage label is isomorphic to a Boolean.
data Label = SafeL | LeakyL
  deriving stock (Eq, Ord)

instance Show Label where
  show SafeL = "safe"
  show LeakyL = "leaky"

instance Pretty Label where
  pretty SafeL = "⊥"
  pretty LeakyL = "⊤"

-- | Labels form a security lattice.
instance Lattice Label where
  SafeL \/ l = l
  LeakyL \/ _ = LeakyL
  SafeL /\ _ = SafeL
  LeakyL /\ l = l

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | TypeApp
  deriving stock (Eq, Show)

-- | Case alternatives
data CaseAlt f a = CaseAlt
  { ctor :: Text,
    binders :: [Maybe Binder],
    bnd :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

instance Bound CaseAlt where
  CaseAlt {..} >>>= f = CaseAlt {bnd = bnd >>>= f, ..}

instance (Eq1 f, Monad f) => Eq1 (CaseAlt f) where
  liftEq
    eq
    CaseAlt {ctor, bnd}
    CaseAlt {ctor = ctor', bnd = bnd'} =
      ctor == ctor' && liftEq eq bnd bnd'

instance (Eq1 f, Monad f, Eq a) => Eq (CaseAlt f a) where (==) = eq1

instance (Monad f, PlateM (f Name)) => BiplateM (CaseAlt f Name) (f Name) where
  biplateM f CaseAlt {..} = do
    (xs, body) <- unbindMany (length binders) bnd
    body' <- f body
    return CaseAlt {bnd = abstract_ xs body', ..}

-- | Smart constructor for 'CaseAlt'
caseAlt_ :: (Monad f, a ~ Text) => Text -> [BinderM a] -> f a -> CaseAlt f a
caseAlt_ ctor binders body =
  CaseAlt
    { binders = Just <$> binders,
      bnd = abstractBinder binders body,
      ..
    }

mustClosed :: Traversable f => Text -> f a -> f b
mustClosed what a = fromMaybe (oops (what <> " is not closed")) $ closed a

----------------------------------------------------------------
-- Common names

-- | Oblivious accent
oblivAccent :: Text
oblivAccent = "`"

oblivName :: Text -> Text
oblivName = (oblivAccent <>)

-- | Leaky accent
leakyAccent :: Text
leakyAccent = "~"

leakyName :: Text -> Text
leakyName = (leakyAccent <>)

-- | The infix operators
infixes :: [Text]
infixes = ["<=", "==", "+", "-", "*"]

-- | The oblivious infix operators
oblivInfixes :: [Text]
oblivInfixes = oblivName <$> infixes

-- | The leaky infix operators
leakyInfixes :: [Text]
leakyInfixes = leakyName <$> infixes

-- | All infix operators
allInfixes :: [Text]
allInfixes = infixes <> oblivInfixes <> leakyInfixes

isInfix :: Text -> Bool
isInfix = (`elem` allInfixes)

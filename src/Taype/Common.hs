{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Common data types and utilities.
module Taype.Common
  ( Options (..),
    HasOptions (..),
    LLabel (..),
    OLabel (..),
    PairKind (..),
    OProjKind (..),
    AppKind (..),
    MatchAlt (..),
    caseAlt_,
    fromClosed,

    -- * Common names
    oblivAccent,
    oblivName,
    sectionName,
    retractionName,
    internalPrefix,
    internalName,
    unsafePrefix,
    unsafeName,
    privPrefix,
    privName,
    infixes,
    oblivInfixes,
    allInfixes,
    isInfix,
    accentOfOLabel,
    accentOfPairKind,
  )
where

import Algebra.Lattice
import Bound
import Data.Functor.Classes
import Data.Maybe (fromJust)
import Prettyprinter
import Taype.Binder
import Taype.Name
import Taype.Plate
import Text.Show qualified

-- | Command line options
data Options = Options
  { optFile :: FilePath,
    optCode :: Text,
    optInternalNames :: Bool,
    optNoFlattenLets :: Bool,
    optNamePrefix :: Text,
    optNoFiles :: Bool,
    optFlagNoOptimization :: Bool,
    optFlagNoSimplify :: Bool,
    optFlagNoTupling :: Bool,
    optPrintCore :: Bool,
    optPrintPrelude :: Bool,
    optPrintOil :: Bool,
    optPrintOCaml :: Bool,
    optPrintTokens :: Bool,
    optPrintSource :: Bool,
    optReadable :: Bool,
    optWidth :: Maybe Int
  }
  deriving stock (Eq, Show)

-- | We can project 'Options' from a.
--
-- We may use 'HasField' from Haskell, but don't bother.
class HasOptions a where
  getOptions :: a -> Options

-- | A leakage label is isomorphic to a Boolean.
data LLabel = SafeL | LeakyL
  deriving stock (Eq, Ord)

instance Show LLabel where
  show SafeL = "safe"
  show LeakyL = "leaky"

instance Pretty LLabel where
  pretty SafeL = "⊥"
  pretty LeakyL = "⊤"

-- | Labels form a security lattice.
instance Lattice LLabel where
  SafeL \/ l = l
  LeakyL \/ _ = LeakyL
  SafeL /\ _ = SafeL
  LeakyL /\ l = l

-- | An oblivious label is isomorphic to a Boolean.
data OLabel = PublicL | OblivL
  deriving stock (Eq, Ord, Show)

-- | Product kinds
data PairKind = PublicP | OblivP
  deriving stock (Eq, Ord, Show)

-- | Oblivious sum projection kinds
data OProjKind = TagP | LeftP | RightP
  deriving stock (Eq, Ord, Show)

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | TypeApp
  deriving stock (Eq, Show)

-- | Match alternatives
data MatchAlt f a = MatchAlt
  { ctor :: Text,
    binders :: [Maybe Binder],
    bnd :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

instance Bound MatchAlt where
  MatchAlt {..} >>>= f = MatchAlt {bnd = bnd >>>= f, ..}

instance (Eq1 f, Monad f) => Eq1 (MatchAlt f) where
  liftEq
    eq
    MatchAlt {ctor, bnd}
    MatchAlt {ctor = ctor', bnd = bnd'} =
      ctor == ctor' && liftEq eq bnd bnd'

instance (Eq1 f, Monad f, Eq a) => Eq (MatchAlt f a) where (==) = eq1

instance (Monad f, PlateM (f Name)) => BiplateM (MatchAlt f Name) (f Name) where
  biplateM f MatchAlt {..} = do
    (xs, body) <- unbindMany (length binders) bnd
    body' <- f body
    return MatchAlt {bnd = abstract_ xs body', ..}

-- | Smart constructor for 'MatchAlt'
caseAlt_ :: (Monad f, a ~ Text) => Text -> [BinderM a] -> f a -> MatchAlt f a
caseAlt_ ctor binders body =
  MatchAlt
    { binders = Just <$> binders,
      bnd = abstractBinder binders body,
      ..
    }

fromClosed :: Traversable f => f a -> f b
fromClosed a = fromJust $ closed a

----------------------------------------------------------------
-- Common names

-- | Oblivious accent
oblivAccent :: Text
oblivAccent = "~"

oblivName :: Text -> Text
oblivName = (oblivAccent <>)

-- | Section name
sectionName :: Text -> Text
sectionName = (<> "#s")

-- | Retraction name
retractionName :: Text -> Text
retractionName = (<> "#r")

-- | Internal name
internalPrefix :: Text
internalPrefix = "$"

internalName :: Text -> Text
internalName = (internalPrefix <>)

-- | Unsafe name
unsafePrefix :: Text
unsafePrefix = "unsafe!"

unsafeName :: Text -> Text
unsafeName = (unsafePrefix <>)

-- | Private name
privPrefix :: Text
privPrefix = "private!"

privName :: Text -> Text
privName = (privPrefix <>)

-- | The infix operators
infixes :: [Text]
infixes = ["<=", "==", "+", "-", "*", "/", "&&", "||"]

-- | The oblivious infix operators
oblivInfixes :: [Text]
oblivInfixes = oblivName <$> infixes

-- | All infix operators
allInfixes :: [Text]
allInfixes = infixes <> oblivInfixes

isInfix :: Text -> Bool
isInfix = (`elem` allInfixes)

accentOfOLabel :: OLabel -> Text
accentOfOLabel PublicL = ""
accentOfOLabel OblivL = oblivAccent

accentOfPairKind :: PairKind -> Text
accentOfPairKind PublicP = ""
accentOfPairKind OblivP = oblivAccent

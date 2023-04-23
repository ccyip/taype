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
    pairKindOfOLabel,
    olabelOfPairKind,
    OProjKind (..),
    AppKind (..),
    MatchAlt (..),
    matchAlt_,
    fromClosed,
    fromClosedDefs,

    -- * Common names
    commentDelim,
    oblivAccent,
    oblivName,
    ppxAccent,
    ppxName,
    psiAccent,
    psiName,
    instInfix,
    instName1,
    instName2,
    sectionInstName,
    sectionName,
    retractionInstName,
    retractionName,
    internalPrefix,
    internalName,
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
import Relude.Extra.Bifunctor
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
    optQuiet :: Bool,
    optFlagNoOptimization :: Bool,
    optFlagNoSimplify :: Bool,
    optFlagNoTupling :: Bool,
    optPrintCore :: Bool,
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
data PairKind = PublicP | OblivP | PsiP
  deriving stock (Eq, Ord, Show)

pairKindOfOLabel :: OLabel -> PairKind
pairKindOfOLabel PublicL = PublicP
pairKindOfOLabel OblivL = OblivP

olabelOfPairKind :: PairKind -> OLabel
olabelOfPairKind PublicP = PublicL
olabelOfPairKind OblivP = OblivL
olabelOfPairKind PsiP = PublicL

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
matchAlt_ :: (Monad f, a ~ Text) => Text -> [BinderM a] -> f a -> MatchAlt f a
matchAlt_ ctor binders body =
  MatchAlt
    { binders = Just <$> binders,
      bnd = abstractBinder binders body,
      ..
    }

fromClosed :: (Traversable f) => f a -> f b
fromClosed a = fromJust $ closed a

fromClosedDefs :: (Traversable f) => [(n, f a)] -> [(n, f b)]
fromClosedDefs = secondF fromClosed

----------------------------------------------------------------
-- Common names

commentDelim :: Text
commentDelim = "//"

-- | Oblivious accent
oblivAccent :: Text
oblivAccent = "~"

oblivName :: Text -> Text
oblivName = (oblivAccent <>)

-- | Ppx accent
ppxAccent :: Text
ppxAccent = "%"

ppxName :: Text -> Text
ppxName = (ppxAccent <>)

-- | Psi type accent
psiAccent :: Text
psiAccent = "#"

psiName :: Text -> Text
psiName = (psiAccent <>)

-- | OADT instance connector
instInfix :: Text
instInfix = "#"

-- | Make an OADT instance name
instName1 :: Text -> Text -> Text
instName1 x inst = x <> instInfix <> inst

-- | Make a binary OADT instance name
instName2 :: Text -> Text -> Text -> Text
instName2 x1 x2 inst = x1 <> instInfix <> x2 <> instInfix <> inst

-- | Section name
sectionInstName :: Text
sectionInstName = "s"

sectionName :: Text -> Text
sectionName x = instName1 x sectionInstName

-- | Retraction name
retractionInstName :: Text
retractionInstName = "r"

retractionName :: Text -> Text
retractionName x = instName1 x retractionInstName

-- | Internal name
internalPrefix :: Text
internalPrefix = "$"

internalName :: Text -> Text
internalName = (internalPrefix <>)

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
accentOfPairKind PsiP = psiAccent

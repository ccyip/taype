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
    HasOptions (..),
    Label (..),
    AppKind (..),
    Attribute (..),
    isSectionAttr,
    isRetractionAttr,
    CaseAlt (..),
    caseAlt_,
    fromClosed,

    -- * Common names
    oblivAccent,
    oblivName,
    leakyAccent,
    leakyName,
    sectionPrefix,
    sectionName,
    retractionPrefix,
    retractionName,
    internalPrefix,
    internalName,
    promPrefix,
    promName,
    lIfPrefix,
    lIfName,
    lCasePrefix,
    lCaseName,
    unsafePrefix,
    unsafeName,
    privPrefix,
    privName,
    projName,
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
import Data.Maybe (fromJust)
import Prettyprinter
import Taype.Binder
import Taype.Name
import Taype.Plate
import qualified Text.Show

-- | Command line options
data Options = Options
  { optFile :: FilePath,
    optCode :: Text,
    optInternalNames :: Bool,
    optNoFlattenLets :: Bool,
    optNamePrefix :: Text,
    optNoFiles :: Bool,
    optFlagNoEarlyTape :: Bool,
    optFlagNoTupling :: Bool,
    optGeneratePrelude :: Maybe FilePath,
    optPrintCore :: Bool,
    optPrintPrelude :: Bool,
    optPrintOil :: Bool,
    optPrintOCaml :: Bool,
    optPrintLabels :: Bool,
    optPrintTokens :: Bool,
    optPrintSource :: Bool,
    optReadableOil :: Bool,
    optWidth :: Maybe Int
  }
  deriving stock (Eq, Show)

-- | We can project 'Options' from a.
--
-- We may use 'HasField' from Haskell, but don't bother.
class HasOptions a where
  getOptions :: a -> Options

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

-- | Every function has an attribute that can be specified by the users. By
-- default the attribute is 'LeakyAttr'. Attributes are used for label inference
-- and oblivious program lifting.
data Attribute
  = SectionAttr {pubRef :: Text, oblivRef :: Text}
  | RetractionAttr {pubRef :: Text, oblivRef :: Text}
  | SafeAttr
  | LeakyAttr
  deriving stock (Eq)

instance Show Attribute where
  show SectionAttr {..} =
    "section(" <> show pubRef <> ", " <> show oblivRef <> ")"
  show RetractionAttr {..} =
    "retraction(" <> show pubRef <> ", " <> show oblivRef <> ")"
  show SafeAttr = "safe"
  show LeakyAttr = "leaky"

instance Pretty Attribute where
  pretty SectionAttr {..} =
    "section" <> prettySecRetArgs pubRef oblivRef
  pretty RetractionAttr {..} =
    "retraction" <> prettySecRetArgs pubRef oblivRef
  pretty SafeAttr = "safe"
  pretty LeakyAttr = "leaky"

prettySecRetArgs :: Text -> Text -> Doc a
prettySecRetArgs "" "" = ""
prettySecRetArgs pubRef oblivRef =
  parens (pretty pubRef <> comma <+> pretty oblivRef)

isSectionAttr :: Attribute -> Bool
isSectionAttr SectionAttr {} = True
isSectionAttr _ = False

isRetractionAttr :: Attribute -> Bool
isRetractionAttr RetractionAttr {} = True
isRetractionAttr _ = False

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

fromClosed :: Traversable f => f a -> f b
fromClosed a = fromJust $ closed a

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

-- | Section name
sectionPrefix :: Text
sectionPrefix = "s_"

sectionName :: Text -> Text
sectionName = (sectionPrefix <>)

-- | Retraction name
retractionPrefix :: Text
retractionPrefix = "r_"

retractionName :: Text -> Text
retractionName = (retractionPrefix <>)

-- | Internal name
internalPrefix :: Text
internalPrefix = "$"

internalName :: Text -> Text
internalName = (internalPrefix <>)

-- | Promotion
promPrefix :: Text
promPrefix = leakyName "prom#"

promName :: Text -> Text
promName = (promPrefix <>)

-- | Leaky if
lIfPrefix :: Text
lIfPrefix = leakyName "if#"

lIfName :: Text -> Text
lIfName = (lIfPrefix <>)

-- | Leaky case
lCasePrefix :: Text
lCasePrefix = leakyName "case#"

lCaseName :: Text -> Text
lCaseName = (lCasePrefix <>)

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

-- | Projection name
projName :: Bool -> Text
projName b = internalName $ if b then "pi0" else "pi1"

-- | The infix operators
infixes :: [Text]
infixes = ["<=", "==", "+", "-", "*", "/", "&&", "||"]

-- | The oblivious infix operators
oblivInfixes :: [Text]
oblivInfixes = oblivName <$> infixes

-- | The leaky infix operators
leakyInfixes :: [Text]
leakyInfixes = leakyName "->" : (leakyName <$> infixes)

-- | All infix operators
allInfixes :: [Text]
allInfixes = infixes <> oblivInfixes <> leakyInfixes

isInfix :: Text -> Bool
isInfix = (`elem` allInfixes)

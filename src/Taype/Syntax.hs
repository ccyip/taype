{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Syntax of the surface and core taype language.
module Taype.Syntax
  ( -- * Syntax
    Expr (..),
    Ty,
    Label (..),
    AppKind (..),
    CaseAlt (..),
    Kind (..),
    Def,
    DefB (..),
    getDefLoc,
    Attribute (..),
    LabelPolyStrategy (..),

    -- * Binders
    Binder,
    BinderM (..),
    fromBinder,
    isBinderName,
    binderNameEq,
    findDupBinderName,

    -- * Locally nameless abstraction and instantiation for binders
    abstract1Binder,
    abstract2Binders,
    abstractBinders,
    instantiate1Binder,
    instantiate2Binders,
    instantiateBinders,

    -- * Smart constructors
    lam_,
    lams_,
    pi_,
    app_,
    iapp_,
    tapp_,
    let_,
    lets_,
    ite_,
    oite_,
    case_,
    ocase_,
    pcase_,
    opcase_,

    -- * Other utilities
    mustClosed,
  )
where

import Bound
import Control.Monad
import Data.Deriving
import Data.Functor.Classes
import Data.List (groupBy)
import Prettyprinter
import Taype.Error
import Taype.Name
import qualified Text.Show

-- | Taype expression, including the surface and the core syntax
data Expr a
  = -- | Local variable
    V {name :: a}
  | -- | Global variable
    GV {ref :: Text}
  | -- | Dependent function type
    Pi
      { ty :: Ty a,
        label :: Maybe Label,
        binder :: Binder,
        bnd :: Scope () Ty a
      }
  | -- | Lambda abstraction
    Lam
      { mTy :: Maybe (Ty a),
        label :: Maybe Label,
        binder :: Binder,
        bnd :: Scope () Expr a
      }
  | -- | Application, including function application, type application, etc
    App
      { appKind :: Maybe AppKind,
        fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { mTy :: Maybe (Ty a),
        label :: Maybe Label,
        rhs :: Expr a,
        binder :: Binder,
        bnd :: Scope () Expr a
      }
  | -- | Unit type
    TUnit
  | -- | Unit value
    VUnit
  | -- | Boolean type
    TBool
  | -- | Oblivious Boolean type
    OBool
  | -- | Boolean literal
    BLit {bLit :: Bool}
  | -- | Integer type
    TInt
  | -- | Oblivious integer type
    OInt
  | -- | Integer literal
    ILit {iLit :: Int}
  | -- | (Dependent) if conditional
    Ite
      { mTy :: Maybe (Ty a),
        cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | (Dependent) case analysis.
    --  Do not support empty type, i.e. 'alts' must be non empty
    Case
      { mTy :: Maybe (Ty a),
        cond :: Expr a,
        alts :: NonEmpty (CaseAlt Expr a)
      }
  | -- | Oblivious and leaky if conditional
    OIte
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Product type
    Prod {left :: Ty a, right :: Ty a}
  | -- | Normal pair
    Pair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for product
    PCase
      { mTy :: Maybe (Ty a),
        cond :: Expr a,
        lBinder :: Binder,
        rBinder :: Binder,
        bnd2 :: Scope Bool Expr a
      }
  | -- | Oblivious product type
    OProd {left :: Ty a, right :: Ty a}
  | -- | Oblivious pair
    OPair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for oblivious product
    OPCase
      { cond :: Expr a,
        lBinder :: Binder,
        rBinder :: Binder,
        bnd2 :: Scope Bool Expr a
      }
  | -- | Oblivious sum type
    OSum {left :: Ty a, right :: Ty a}
  | -- | Oblivious injection
    OInj
      { mTy :: Maybe (Ty a),
        tag :: Bool,
        inj :: Expr a
      }
  | -- | (Leaky) case analysis for oblivious sum type
    OCase
      { mTy :: Maybe (Ty a),
        cond :: Expr a,
        lBinder :: Binder,
        lBnd :: Scope () Expr a,
        rBinder :: Binder,
        rBnd :: Scope () Expr a
      }
  | -- | Oblivious conditional, i.e. multiplexer
    Mux
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Ascription. Do not appear in core taype
    Asc {ty :: Ty a, expr :: Expr a}
  | -- | Label promotion. Do not appear in surface taype
    Promote {expr :: Expr a}
  | -- | Tape, the key operation in taype
    Tape {expr :: Expr a}
  | -- | Add location information
    Loc {loc :: Int, expr :: Expr a}
  deriving stock (Functor, Foldable, Traversable)

-- | A type in taype is also an expression
type Ty = Expr

-- | A leakage label is just a Boolean
data Label = SafeL | LeakyL
  deriving stock (Eq, Show)

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | InfixApp | TypeApp
  deriving stock (Eq, Show)

-- | Case alternatives
data CaseAlt f a = CaseAlt
  { ctor :: Text,
    binders :: [Binder],
    bnd :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

-- | Kinds
data Kind = AnyK | PublicK | OblivK | MixedK
  deriving stock (Eq)

instance Show Kind where
  show AnyK = "*@A"
  show PublicK = "*@P"
  show OblivK = "*@O"
  show MixedK = "*@M"

instance Pretty Kind where
  pretty = show

-- | A binder is either a name, or anonymous, i.e. \"_\", with location
type Binder = BinderM Text

-- | Generalized binders
data BinderM a = Named Int a | Anon
  deriving stock (Eq, Show)

instance IsString a => IsString (BinderM a) where
  fromString = Named (-1) . fromString

instance ToText a => ToText (BinderM a) where
  toText (Named _ a) = toText a
  toText Anon = "_"

-- | Global definition
type Def = DefB Expr

-- | Generalized global definition
data DefB f a
  = -- Function
    FunDef
      { loc :: Int,
        attr :: Attribute,
        ty :: f a,
        label :: Maybe Label,
        expr :: f a
      }
  | -- | Algebraic data type. Do not support empty type
    ADTDef {loc :: Int, ctors :: NonEmpty Text}
  | -- | Oblivious algebraic data type. Only support one argument for now
    OADTDef {loc :: Int, ty :: f a, binder :: Binder, bnd :: Scope () f a}
  | -- | Constructor
    CtorDef {loc :: Int, paraTypes :: [f a], dataType :: Text}
  | -- | Builtin operation
    BuiltinDef
      { paraTypes :: [f a],
        resType :: f a,
        strategy :: LabelPolyStrategy
      }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

getDefLoc :: DefB f a -> Int
getDefLoc = \case
  FunDef {..} -> loc
  ADTDef {..} -> loc
  OADTDef {..} -> loc
  CtorDef {..} -> loc
  BuiltinDef {} -> -1

data Attribute = SectionAttr | RetractionAttr | SafeAttr | LeakyAttr
  deriving stock (Eq)

instance Show Attribute where
  show SectionAttr = "section"
  show RetractionAttr = "retraction"
  show SafeAttr = "safe"
  show LeakyAttr = "leaky"

instance Pretty Attribute where
  pretty = show

data LabelPolyStrategy = JoinStrategy | TopStrategy
  deriving stock (Eq, Show)

instance Applicative Expr where
  pure = V
  (<*>) = ap

instance Monad Expr where
  V {..} >>= f = f name
  GV {..} >>= _ = GV {..}
  Pi {..} >>= f = Pi {ty = ty >>= f, bnd = bnd >>>= f, ..}
  Lam {..} >>= f = Lam {mTy = mTy <&> (>>= f), bnd = bnd >>>= f, ..}
  App {..} >>= f = App {fn = fn >>= f, args = args <&> (>>= f), ..}
  Let {..} >>= f =
    Let
      { mTy = mTy <&> (>>= f),
        rhs = rhs >>= f,
        bnd = bnd >>>= f,
        ..
      }
  TUnit >>= _ = TUnit
  VUnit >>= _ = VUnit
  TBool >>= _ = TBool
  OBool >>= _ = OBool
  BLit {..} >>= _ = BLit {..}
  TInt >>= _ = TInt
  OInt >>= _ = OInt
  ILit {..} >>= _ = ILit {..}
  Ite {..} >>= f =
    Ite
      { mTy = mTy <&> (>>= f),
        cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f
      }
  Case {..} >>= f =
    Case
      { mTy = mTy <&> (>>= f),
        cond = cond >>= f,
        alts = alts <&> (>>>= f),
        ..
      }
  OIte {..} >>= f =
    OIte
      { cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f,
        ..
      }
  Prod {..} >>= f = Prod {left = left >>= f, right = right >>= f, ..}
  Pair {..} >>= f = Pair {left = left >>= f, right = right >>= f, ..}
  PCase {..} >>= f =
    PCase
      { mTy = mTy <&> (>>= f),
        cond = cond >>= f,
        bnd2 = bnd2 >>>= f,
        ..
      }
  OProd {..} >>= f = OProd {left = left >>= f, right = right >>= f, ..}
  OPair {..} >>= f = OPair {left = left >>= f, right = right >>= f, ..}
  OPCase {..} >>= f =
    OPCase
      { cond = cond >>= f,
        bnd2 = bnd2 >>>= f,
        ..
      }
  OSum {..} >>= f = OSum {left = left >>= f, right = right >>= f, ..}
  OInj {..} >>= f = OInj {mTy = mTy <&> (>>= f), inj = inj >>= f, ..}
  OCase {..} >>= f =
    OCase
      { mTy = mTy <&> (>>= f),
        cond = cond >>= f,
        lBnd = lBnd >>>= f,
        rBnd = rBnd >>>= f,
        ..
      }
  Mux {..} >>= f =
    Mux
      { cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f,
        ..
      }
  Asc {..} >>= f = Asc {ty = ty >>= f, expr = expr >>= f, ..}
  Promote {..} >>= f = Promote {expr = expr >>= f, ..}
  Tape {..} >>= f = Tape {expr = expr >>= f, ..}
  Loc {..} >>= f = Loc {expr = expr >>= f, ..}

instance Bound CaseAlt where
  CaseAlt {..} >>>= f = CaseAlt {bnd = bnd >>>= f, ..}

instance Bound DefB where
  FunDef {..} >>>= f = FunDef {ty = ty >>= f, expr = expr >>= f, ..}
  ADTDef {..} >>>= _ = ADTDef {..}
  OADTDef {..} >>>= f = OADTDef {ty = ty >>= f, bnd = bnd >>>= f, ..}
  CtorDef {..} >>>= f = CtorDef {paraTypes = paraTypes <&> (>>= f), ..}
  BuiltinDef {..} >>>= f =
    BuiltinDef
      { paraTypes = paraTypes <&> (>>= f),
        resType = resType >>= f,
        ..
      }

instance (Eq1 f, Monad f) => Eq1 (CaseAlt f) where
  liftEq
    eq
    (CaseAlt {ctor, bnd})
    (CaseAlt {ctor = ctor', bnd = bnd'}) =
      ctor == ctor' && liftEq eq bnd bnd'

deriveEq1 ''Expr

instance (Eq1 f, Monad f, Eq a) => Eq (CaseAlt f a) where (==) = eq1

instance Eq a => Eq (Expr a) where (==) = eq1

deriveShow1 ''CaseAlt
deriveShow1 ''Expr

instance (Show1 f, Show a) => Show (CaseAlt f a) where showsPrec = showsPrec1

instance Show a => Show (Expr a) where showsPrec = showsPrec1

fromBinder :: BinderM a -> a
fromBinder (Named _ name) = name
fromBinder Anon = oops "Instantiating an anonymous binder"

isBinderName :: Eq a => a -> BinderM a -> Bool
isBinderName x (Named _ y) = x == y
isBinderName _ Anon = False

-- | Check if two binders have the same name. Two anonymous binder DO NOT have
-- the same name
binderNameEq :: Eq a => BinderM a -> BinderM a -> Bool
binderNameEq (Named _ x) (Named _ y) = x == y
binderNameEq _ _ = False

-- | Return 'Nothing' if the list of binders do not has duplicate names, or
-- 'Just' the duplicate binder
findDupBinderName :: Eq a => [BinderM a] -> Maybe (BinderM a)
findDupBinderName binders = find ((> 1) . length) groups >>= viaNonEmpty head
  where
    groups = groupBy binderNameEq binders

abstract1Binder :: (Monad f, Eq a) => BinderM a -> f a -> Scope () f a
abstract1Binder = abstract1By isBinderName

abstract2Binders :: (Monad f, Eq a) => BinderM a -> BinderM a -> f a -> Scope Bool f a
abstract2Binders = abstract2By isBinderName

abstractBinders :: (Monad f, Eq a) => [BinderM a] -> f a -> Scope Int f a
abstractBinders = abstractManyBy isBinderName

instantiate1Binder :: Monad f => BinderM a -> Scope n f a -> f a
instantiate1Binder = instantiate1By $ return . fromBinder

instantiate2Binders :: Monad f => BinderM a -> BinderM a -> Scope Bool f a -> f a
instantiate2Binders = instantiate2By $ return . fromBinder

instantiateBinders :: Monad f => [BinderM a] -> Scope Int f a -> f a
instantiateBinders = instantiateManyBy $ return . fromBinder

lam_ :: a ~ Text => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a
lam_ binder mTy body =
  Lam {label = Nothing, bnd = abstract1Binder binder body, ..}

-- | A smart constructor for lambda abstraction that takes a list of arguments
lams_ :: a ~ Text => NonEmpty (BinderM a, Maybe (Ty a)) -> Expr a -> Expr a
lams_ args body = foldr (uncurry lam_) body args

pi_ :: a ~ Text => BinderM a -> Ty a -> Expr a -> Expr a
pi_ binder ty body =
  Pi {label = Nothing, bnd = abstract1Binder binder body, ..}

app_ :: Expr a -> [Expr a] -> Expr a
app_ fn args = App {appKind = Nothing, ..}

iapp_ :: Expr a -> [Expr a] -> Expr a
iapp_ fn args = App {appKind = Just InfixApp, ..}

tapp_ :: Expr a -> [Expr a] -> Ty a
tapp_ fn args = App {appKind = Just TypeApp, ..}

let_ :: a ~ Text => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a -> Expr a
let_ binder mTy rhs body =
  Let {label = Nothing, bnd = abstract1Binder binder body, ..}

-- | A smart constructor for let that takes a list of bindings
lets_ :: a ~ Text => NonEmpty (BinderM a, Maybe (Ty a), Expr a) -> Expr a -> Expr a
lets_ bindings body = foldr go body bindings
  where
    go (binder, mTy, rhs) = let_ binder mTy rhs

ite_ :: Expr a -> Expr a -> Expr a -> Expr a
ite_ cond ifTrue ifFalse = Ite {mTy = Nothing, ..}

oite_ :: Expr a -> Expr a -> Expr a -> Expr a
oite_ cond ifTrue ifFalse = OIte {..}

case_ :: a ~ Text => Expr a -> NonEmpty (Text, [BinderM a], Expr a) -> Expr a
case_ cond alts = Case {mTy = Nothing, alts = abstr <$> alts, ..}
  where
    abstr (ctor, binders, body) =
      CaseAlt {bnd = abstractBinders binders body, ..}

ocase_ :: a ~ Text => Expr a -> BinderM a -> Expr a -> BinderM a -> Expr a -> Expr a
ocase_ cond lBinder lBody rBinder rBody =
  OCase
    { mTy = Nothing,
      lBnd = abstract1Binder lBinder lBody,
      rBnd = abstract1Binder rBinder rBody,
      ..
    }

pcase_ :: a ~ Text => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
pcase_ cond lBinder rBinder body =
  PCase {mTy = Nothing, bnd2 = abstract2Binders lBinder rBinder body, ..}

opcase_ :: a ~ Text => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
opcase_ cond lBinder rBinder body =
  OPCase {bnd2 = abstract2Binders lBinder rBinder body, ..}

mustClosed :: Traversable f => Text -> f a -> f b
mustClosed what a = fromMaybe (oops (what <> " is not closed")) $ closed a

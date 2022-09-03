{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
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
    abstractBinder,
    instantiateBinder,

    -- * Smart constructors
    lam_,
    pi_,
    app_,
    iapp_,
    tapp_,
    let_,
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

import Algebra.Lattice
import Algebra.Lattice.M2
import Algebra.PartialOrd
import Bound
import Control.Monad
import Data.Deriving
import Data.Functor.Classes
import Data.List (groupBy)
import Prettyprinter
import Taype.Name
import Taype.Prelude
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
        binder :: Maybe Binder,
        bnd :: Scope () Ty a
      }
  | -- | Lambda abstraction
    Lam
      { mTy :: Maybe (Ty a),
        label :: Maybe Label,
        binder :: Maybe Binder,
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
        binder :: Maybe Binder,
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
        left :: Expr a,
        right :: Expr a
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
        left :: Expr a,
        right :: Expr a
      }
  | -- | Product type
    Prod {left :: Ty a, right :: Ty a}
  | -- | Normal pair
    Pair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for product
    PCase
      { mTy :: Maybe (Ty a),
        cond :: Expr a,
        lBinder :: Maybe Binder,
        rBinder :: Maybe Binder,
        bnd2 :: Scope Bool Expr a
      }
  | -- | Oblivious product type
    OProd {left :: Ty a, right :: Ty a}
  | -- | Oblivious pair
    OPair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for oblivious product
    OPCase
      { cond :: Expr a,
        lBinder :: Maybe Binder,
        rBinder :: Maybe Binder,
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
        lBinder :: Maybe Binder,
        lBnd :: Scope () Expr a,
        rBinder :: Maybe Binder,
        rBnd :: Scope () Expr a
      }
  | -- | Oblivious conditional, i.e. multiplexer
    Mux
      { cond :: Expr a,
        left :: Expr a,
        right :: Expr a
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
  deriving stock (Eq, Ord)

instance Show Label where
  show SafeL = "safe"
  show LeakyL = "leaky"

instance Pretty Label where
  pretty SafeL = "⊥"
  pretty LeakyL = "⊤"

-- Isomorphic to Boolean
instance Lattice Label where
  SafeL \/ l = l
  LeakyL \/ _ = LeakyL
  SafeL /\ _ = SafeL
  LeakyL /\ l = l

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | InfixApp | TypeApp
  deriving stock (Eq, Show)

-- | Case alternatives
data CaseAlt f a = CaseAlt
  { ctor :: Text,
    binders :: [Maybe Binder],
    bnd :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

-- | Kinds
data Kind = AnyK | PublicK | OblivK | MixedK
  deriving stock (Eq)

instance Show Kind where
  show AnyK = "any"
  show PublicK = "public"
  show OblivK = "oblivious"
  show MixedK = "mixed"

instance Pretty Kind where
  pretty AnyK = "*@A"
  pretty PublicK = "*@P"
  pretty OblivK = "*@O"
  pretty MixedK = "*@M"

-- Kinds form a lattice and it is isomorphic to M2.
toM2 :: Kind -> M2
toM2 AnyK = M2o
toM2 PublicK = M2a
toM2 OblivK = M2b
toM2 MixedK = M2i

fromM2 :: M2 -> Kind
fromM2 M2o = AnyK
fromM2 M2a = PublicK
fromM2 M2b = OblivK
fromM2 M2i = MixedK

instance PartialOrd Kind where
  k1 `leq` k2 = toM2 k1 `leq` toM2 k2

instance Lattice Kind where
  k1 \/ k2 = fromM2 $ toM2 k1 \/ toM2 k2
  k1 /\ k2 = fromM2 $ toM2 k1 /\ toM2 k2

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
  = -- | Function
    FunDef
      { loc :: Int,
        attr :: Attribute,
        ty :: f a,
        label :: Maybe Label,
        expr :: f a
      }
  | -- | Algebraic data type. Do not support empty type
    ADTDef {loc :: Int, ctors :: NonEmpty (Text, [f a])}
  | -- | Oblivious algebraic data type. Only support one argument for now
    OADTDef {loc :: Int, ty :: f a, binder :: Maybe Binder, bnd :: Scope () f a}
  | -- | Constructor
    CtorDef {paraTypes :: [f a], dataType :: Text}
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
  _ -> -1

data Attribute = SectionAttr | RetractionAttr | SafeAttr | LeakyAttr
  deriving stock (Eq)

instance Show Attribute where
  show SectionAttr = "section"
  show RetractionAttr = "retraction"
  show SafeAttr = "safe"
  show LeakyAttr = "leaky"

instance Pretty Attribute where
  pretty = show

data LabelPolyStrategy = JoinStrategy | LeakyStrategy | SafeStrategy
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
        left = left >>= f,
        right = right >>= f
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
        left = left >>= f,
        right = right >>= f,
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
        left = left >>= f,
        right = right >>= f,
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
  ADTDef {..} >>>= f = ADTDef {ctors = ctors <&> second ((>>= f) <$>), ..}
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
    CaseAlt {ctor, bnd}
    CaseAlt {ctor = ctor', bnd = bnd'} =
      ctor == ctor' && liftEq eq bnd bnd'

instance Eq1 Expr where
  liftEq eq V {name} V {name = name'} = eq name name'
  liftEq _ GV {ref} GV {ref = ref'} = ref == ref'
  liftEq eq Pi {ty, bnd} Pi {ty = ty', bnd = bnd'} =
    -- Ignore labels
    liftEq eq ty ty' && liftEq eq bnd bnd'
  liftEq eq Lam {bnd} Lam {bnd = bnd'} =
    -- Ignore type annotations and labels
    liftEq eq bnd bnd'
  liftEq eq App {fn, args} App {fn = fn', args = args'} =
    -- Ignore application kind
    liftEq eq fn fn' && liftEq (liftEq eq) args args'
  liftEq eq Let {rhs, bnd} Let {rhs = rhs', bnd = bnd'} =
    -- Ignore type annotations and labels
    liftEq eq rhs rhs' && liftEq eq bnd bnd'
  liftEq _ TUnit TUnit = True
  liftEq _ VUnit VUnit = True
  liftEq _ TBool TBool = True
  liftEq _ OBool OBool = True
  liftEq _ BLit {bLit} BLit {bLit = bLit'} = bLit == bLit'
  liftEq _ TInt TInt = True
  liftEq _ OInt OInt = True
  liftEq _ ILit {iLit} ILit {iLit = iLit'} = iLit == iLit'
  liftEq
    eq
    Ite {cond, left, right}
    Ite {cond = cond', left = left', right = right'} =
      liftEq eq cond cond'
        && liftEq eq left left'
        && liftEq eq right right'
  liftEq eq Case {cond, alts} Case {cond = cond', alts = alts'} =
    liftEq eq cond cond' && liftEq (liftEq eq) alts alts'
  liftEq
    eq
    OIte {cond, left, right}
    OIte {cond = cond', left = left', right = right'} =
      liftEq eq cond cond'
        && liftEq eq left left'
        && liftEq eq right right'
  liftEq eq Prod {left, right} Prod {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq Pair {left, right} Pair {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq PCase {cond, bnd2} PCase {cond = cond', bnd2 = bnd2'} =
    liftEq eq cond cond' && liftEq eq bnd2 bnd2'
  liftEq eq OProd {left, right} OProd {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq OPair {left, right} OPair {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq OPCase {cond, bnd2} OPCase {cond = cond', bnd2 = bnd2'} =
    liftEq eq cond cond' && liftEq eq bnd2 bnd2'
  liftEq eq OSum {left, right} OSum {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq OInj {tag, inj} OInj {tag = tag', inj = inj'} =
    -- Ignore type annotations
    tag == tag' && liftEq eq inj inj'
  liftEq
    eq
    OCase {cond, lBnd, rBnd}
    OCase {cond = cond', lBnd = lBnd', rBnd = rBnd'} =
      liftEq eq cond cond' && liftEq eq lBnd lBnd' && liftEq eq rBnd rBnd'
  liftEq
    eq
    Mux {cond, left, right}
    Mux {cond = cond', left = left', right = right'} =
      liftEq eq cond cond'
        && liftEq eq left left'
        && liftEq eq right right'
  liftEq eq Asc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Asc {expr} = liftEq eq expr' expr
  liftEq eq Promote {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Promote {expr} = liftEq eq expr' expr
  liftEq eq Tape {expr} Tape {expr = expr'} = liftEq eq expr expr'
  liftEq eq Loc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Loc {expr} = liftEq eq expr' expr
  liftEq _ _ _ = False

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

abstractBinder ::
  (ScopeOps s (BinderM a) b', Monad f, Eq a) => b' -> f a -> Scope s f a
abstractBinder = abstractBy isBinderName

instantiateBinder ::
  (ScopeOps s (BinderM a) b', Monad f) => b' -> Scope s f a -> f a
instantiateBinder = instantiateBy $ return . fromBinder

lam_ :: a ~ Text => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a
lam_ binder mTy body =
  Lam
    { label = Nothing,
      bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

pi_ :: a ~ Text => BinderM a -> Ty a -> Expr a -> Expr a
pi_ binder ty body =
  Pi
    { label = Nothing,
      bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

app_ :: Expr a -> [Expr a] -> Expr a
app_ fn args = App {appKind = Nothing, ..}

iapp_ :: Expr a -> [Expr a] -> Expr a
iapp_ fn args = App {appKind = Just InfixApp, ..}

tapp_ :: Expr a -> [Expr a] -> Ty a
tapp_ fn args = App {appKind = Just TypeApp, ..}

let_ :: a ~ Text => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a -> Expr a
let_ binder mTy rhs body =
  Let
    { label = Nothing,
      bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

ite_ :: Expr a -> Expr a -> Expr a -> Expr a
ite_ cond left right = Ite {mTy = Nothing, ..}

oite_ :: Expr a -> Expr a -> Expr a -> Expr a
oite_ cond left right = OIte {..}

case_ :: a ~ Text => Expr a -> NonEmpty (Text, [BinderM a], Expr a) -> Expr a
case_ cond alts = Case {mTy = Nothing, alts = abstr <$> alts, ..}
  where
    abstr (ctor, binders, body) =
      CaseAlt
        { bnd = abstractBinder binders body,
          binders = Just <$> binders,
          ..
        }

ocase_ :: a ~ Text => Expr a -> BinderM a -> Expr a -> BinderM a -> Expr a -> Expr a
ocase_ cond lBinder lBody rBinder rBody =
  OCase
    { mTy = Nothing,
      lBinder = Just lBinder,
      lBnd = abstractBinder lBinder lBody,
      rBinder = Just rBinder,
      rBnd = abstractBinder rBinder rBody,
      ..
    }

pcase_ :: a ~ Text => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
pcase_ cond lBinder rBinder body =
  PCase
    { mTy = Nothing,
      lBinder = Just lBinder,
      rBinder = Just rBinder,
      bnd2 = abstractBinder (lBinder, rBinder) body,
      ..
    }

opcase_ :: a ~ Text => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
opcase_ cond lBinder rBinder body =
  OPCase
    { lBinder = Just lBinder,
      rBinder = Just rBinder,
      bnd2 = abstractBinder (lBinder, rBinder) body,
      ..
    }

mustClosed :: Traversable f => Text -> f a -> f b
mustClosed what a = fromMaybe (oops (what <> " is not closed")) $ closed a

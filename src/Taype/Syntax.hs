{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
  )
where

import Algebra.Lattice
import Algebra.Lattice.M2
import Algebra.PartialOrd
import Bound
import Control.Monad
import Data.Deriving
import Data.Functor.Classes
import Prettyprinter
import Taype.Binder
import Taype.Name
import Taype.Plate
import Taype.Prelude
import qualified Text.Show

----------------------------------------------------------------
-- Syntax

-- | Taype expression
--
-- It accommodates both the surface and the core syntax.
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
  | -- | (Dependent) case analysis
    --
    --  Do not support empty type, i.e. 'alts' must be non empty.
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
  | -- | Ascription
    --
    -- This does not appear in the core language.
    Asc {ty :: Ty a, expr :: Expr a}
  | -- | Label promotion
    --
    -- This does not appear in the surface language, and the type checker will
    -- insert promotion automatically.
    Promote {expr :: Expr a}
  | -- | Tape construct
    --
    -- This is the key operation in taype.
    Tape {expr :: Expr a}
  | -- | Location information for error reporting
    --
    -- This does not appear in the core language
    Loc {loc :: Int, expr :: Expr a}
  deriving stock (Functor, Foldable, Traversable)

-- | A type in taype is also an expression.
type Ty = Expr

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

-- Kind is isomorphic to M2.
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

-- | Kinds form a lattice.
instance Lattice Kind where
  k1 \/ k2 = fromM2 $ toM2 k1 \/ toM2 k2
  k1 /\ k2 = fromM2 $ toM2 k1 /\ toM2 k2

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
  | -- | Algebraic data type
    --
    -- Do not support empty type, so 'ctors' is an 'NonEmpty'.
    ADTDef {loc :: Int, ctors :: NonEmpty (Text, [f a])}
  | -- | Oblivious algebraic data type
    --
    -- It takes a single argument for now.
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

-- | Every function has an attribute that can be specified by the users. By
-- default the attribute is 'LeakyAttr'. Attributes are used for label inference
-- and oblivious program lifting.
data Attribute = SectionAttr | RetractionAttr | SafeAttr | LeakyAttr
  deriving stock (Eq)

instance Show Attribute where
  show SectionAttr = "section"
  show RetractionAttr = "retraction"
  show SafeAttr = "safe"
  show LeakyAttr = "leaky"

instance Pretty Attribute where
  pretty = show

-- | A simple label polymorphism mechanism for builtin functions and
-- constructors. Taype does not support general label polymorphism yet.
data LabelPolyStrategy = JoinStrategy | LeakyStrategy | SafeStrategy
  deriving stock (Eq, Show)

----------------------------------------------------------------
-- Instances of expressions and definitions

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

instance PlateM (Expr Name) where
  plateM f Let {..} = do
    mTy' <- mapM f mTy
    rhs' <- f rhs
    (x, body) <- unbind1 bnd
    body' <- f body
    return Let {mTy = mTy', rhs = rhs', bnd = abstract_ x body', ..}
  plateM f Pi {..} = do
    ty' <- f ty
    (x, body) <- unbind1 bnd
    body' <- f body
    return Pi {ty = ty', bnd = abstract_ x body', ..}
  plateM f Lam {..} = do
    mTy' <- mapM f mTy
    (x, body) <- unbind1 bnd
    body' <- f body
    return Lam {mTy = mTy', bnd = abstract_ x body', ..}
  plateM f App {..} = do
    fn' <- f fn
    args' <- mapM f args
    return App {fn = fn', args = args', ..}
  plateM f Ite {..} = do
    mTy' <- mapM f mTy
    cond' <- f cond
    left' <- f left
    right' <- f right
    return Ite {mTy = mTy', cond = cond', left = left', right = right'}
  plateM f Case {..} = do
    mTy' <- mapM f mTy
    cond' <- f cond
    alts' <- mapM go alts
    return Case {mTy = mTy', cond = cond', alts = alts'}
    where
      go CaseAlt {..} = do
        (xs, body) <- unbindMany (length binders) bnd
        body' <- f body
        return CaseAlt {bnd = abstract_ xs body', ..}
  plateM f OIte {..} = do
    cond' <- f cond
    left' <- f left
    right' <- f right
    return OIte {cond = cond', left = left', right = right'}
  plateM f Prod {..} = do
    left' <- f left
    right' <- f right
    return Prod {left = left', right = right'}
  plateM f Pair {..} = do
    left' <- f left
    right' <- f right
    return Pair {left = left', right = right'}
  plateM f PCase {..} = do
    mTy' <- mapM f mTy
    cond' <- f cond
    ((xl, xr), body) <- unbind2 bnd2
    body' <- f body
    return PCase {mTy = mTy', cond = cond', bnd2 = abstract_ (xl, xr) body', ..}
  plateM f OProd {..} = do
    left' <- f left
    right' <- f right
    return OProd {left = left', right = right'}
  plateM f OPair {..} = do
    left' <- f left
    right' <- f right
    return OPair {left = left', right = right'}
  plateM f OPCase {..} = do
    cond' <- f cond
    ((xl, xr), body) <- unbind2 bnd2
    body' <- f body
    return OPCase {cond = cond', bnd2 = abstract_ (xl, xr) body', ..}
  plateM f OSum {..} = do
    left' <- f left
    right' <- f right
    return OSum {left = left', right = right'}
  plateM f OInj {..} = do
    mTy' <- mapM f mTy
    inj' <- f inj
    return OInj {mTy = mTy', inj = inj', ..}
  plateM f OCase {..} = do
    mTy' <- mapM f mTy
    cond' <- f cond
    (xl, lBody) <- unbind1 lBnd
    lBody' <- f lBody
    (xr, rBody) <- unbind1 rBnd
    rBody' <- f rBody
    return
      OCase
        { mTy = mTy',
          cond = cond',
          lBnd = abstract_ xl lBody',
          rBnd = abstract_ xr rBody',
          ..
        }
  plateM f Mux {..} = do
    cond' <- f cond
    left' <- f left
    right' <- f right
    return Mux {cond = cond', left = left', right = right'}
  plateM f Asc {..} = do
    ty' <- f ty
    expr' <- f expr
    return Asc {ty = ty', expr = expr'}
  plateM f Promote {..} = do
    expr' <- f expr
    return Promote {expr = expr'}
  plateM f Tape {..} = do
    expr' <- f expr
    return Tape {expr = expr'}
  plateM f Loc {..} = do
    expr' <- f expr
    return Loc {expr = expr', ..}
  plateM _ e = return e

instance BiplateM (Def Name) (Expr Name) where
  biplateM f FunDef {..} = do
    ty' <- f ty
    expr' <- f expr
    return FunDef {ty = ty', expr = expr', ..}
  biplateM f ADTDef {..} = do
    ctors' <- forM ctors $ secondM (mapM f)
    return ADTDef {ctors = ctors', ..}
  biplateM f OADTDef {..} = do
    ty' <- f ty
    (x, body) <- unbind1 bnd
    body' <- f body
    return OADTDef {ty = ty', bnd = abstract_ x body', ..}
  -- Skip handling constructor definitions, as they should be in sync with the ADT
  -- definitions. The caller is responsible for resyncing these two definitions.
  -- Builtin definitions are not handled either.
  biplateM _ def = return def

----------------------------------------------------------------
-- Smart constructors

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

----------------------------------------------------------------
-- Template Haskell related stuff

deriveShow1 ''CaseAlt
deriveShow1 ''Expr

instance (Show1 f, Show a) => Show (CaseAlt f a) where showsPrec = showsPrec1

instance Show a => Show (Expr a) where showsPrec = showsPrec1

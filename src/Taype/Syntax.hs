{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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
    Ppx,
    PpxB (..),
    Kind (..),
    Def,
    DefB (..),
    NamedDef,
    Defs,
    getDefLoc,
    closeDefs,
    Pat (..),
    PolyConstraint (..),
    PolyType (..),

    -- * Smart constructors
    lam_,
    pi_,
    (@@),
    (@@@),
    let_,
    ite_,
    oite_,
    mux_,
    inj_,
    inl_,
    inr_,
    oproj_,
    prod_,
    deprod,
    tuple_,
    thunk_,
    match_,
    smatch_,
    smatchPat_,
    pmatch_,
    pmatchPat_,
    lamPat_,
    lam',
    lams',
    let',
    lets',
    match',
    pmatch',
    smatch',
    pi',
    lamP,
    arrow_,
    arrows_,

    -- * Utilities
    isArrow,
    isArrow1,
    readableExpr,
    readableDefs,

    -- * Pretty printer
    cuteBinder,
    cuteDefsDoc,
  )
where

import Algebra.Lattice
import Algebra.Lattice.M2
import Algebra.PartialOrd
import Bound
import Control.Monad
import Data.Functor.Classes
import Data.List (foldr1)
import Relude.Extra (bimapBoth, secondF, traverseBoth)
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Text.Show qualified
import Prelude hiding (Sum (..), group)

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
        binder :: Maybe Binder,
        bnd :: Scope () Ty a
      }
  | -- | Lambda abstraction
    Lam
      { argTy :: Maybe (Ty a),
        binder :: Maybe Binder,
        bnd :: Scope () Expr a
      }
  | -- | Application, including function application, type application, etc
    App
      { fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { rhsTy :: Maybe (Ty a),
        rhs :: Expr a,
        binder :: Maybe Binder,
        bnd :: Scope () Expr a
      }
  | -- | Unit type
    TUnit
  | -- | Unit value
    VUnit
  | -- | Public and oblivious Boolean type
    TBool {olabel :: OLabel}
  | -- | Boolean literal
    BLit {bLit :: Bool}
  | -- | Public and oblivious integer type
    TInt {olabel :: OLabel}
  | -- | Unsigned integer type
    UInt
  | -- | Integer literal
    ILit {iLit :: Int}
  | -- | (Dependent) if conditional
    Ite
      { cond :: Expr a,
        left :: Expr a,
        right :: Expr a
      }
  | -- | (Dependent) ADT pattern matching
    --
    --  Do not support empty type, i.e. 'alts' must be non empty.
    Match
      { cond :: Expr a,
        alts :: NonEmpty (MatchAlt Expr a)
      }
  | -- | Oblivious (and possibly leaky) if conditional
    --
    -- When 'label' is 'SafeL', this is just mux.
    OIte
      { label :: LLabel,
        cond :: Expr a,
        left :: Expr a,
        right :: Expr a
      }
  | -- | Product type
    --
    -- This definition includes public product and oblivious product.
    Prod {olabel :: OLabel, left :: Ty a, right :: Ty a}
  | -- | Psi type
    Psi {viewTy :: Maybe (Ty a), oadtName :: Text}
  | -- | Public, oblivious, and dependent pairs
    Pair {pairKind :: PairKind, left :: Expr a, right :: Expr a}
  | -- | Product and Psi type pattern matching
    PMatch
      { pairKind :: PairKind,
        condTy :: Maybe (Ty a, Ty a),
        cond :: Expr a,
        lBinder :: Maybe Binder,
        rBinder :: Maybe Binder,
        bnd2 :: Scope Bool Expr a
      }
  | -- | Public and oblivious sum type
    --
    -- Public sum type is mostly used for optimization.
    Sum {olabel :: OLabel, left :: Ty a, right :: Ty a}
  | -- | Public and oblivious injection
    Inj
      { injTy :: Maybe (Ty a, Ty a),
        olabel :: OLabel,
        tag :: Bool,
        expr :: Expr a
      }
  | -- | Oblivious sum projections
    OProj
      { projTy :: Maybe (Ty a, Ty a),
        projKind :: OProjKind,
        expr :: Expr a
      }
  | -- | Sum type pattern matching
    --
    -- Oblivious sum type pattern matching does not appear in the core language,
    -- as it is just syntax sugar for oblivious if and oblivious sum
    -- projections.
    SMatch
      { olabel :: OLabel,
        cond :: Expr a,
        lBinder :: Maybe Binder,
        lBnd :: Scope () Expr a,
        rBinder :: Maybe Binder,
        rBnd :: Scope () Expr a
      }
  | -- | Ascription
    --
    -- Cheat if @trustMe@ is @True@: the type of @expr@ is @ty@ regardless of
    -- them being equivalent or not. To avoid propagating this dangerous
    -- operation too far, the type of @expr@ is always inferred.
    --
    -- This does not appear in the core language.
    Asc {ty :: Ty a, expr :: Expr a, trustMe :: Bool}
  | -- | Location information for error reporting
    --
    -- This does not appear in the core language
    Loc {loc :: Int, expr :: Expr a}
  | -- | Type variable
    --
    -- We do not support general type polymorphism yet. The type variables are
    -- only used for defining OADT match instances (@idx@ must be @0@ in this
    -- case), and internally for lifting algorithm.
    TV {idx :: Int}
  | -- | Arbitrary oblivious value
    Arb {oblivTy :: Maybe (Ty a)}
  | -- | Polymorphic equality check
    PolyEq {lhs :: Expr a, rhs :: Expr a}
  | -- | Preprocessor
    Ppx {ppx :: Ppx a}
  deriving stock (Functor, Foldable, Traversable)

-- | A type in taype is also an expression.
type Ty = Expr

-- | Preprocessors
type Ppx = PpxB Ty

data PpxB f a
  = -- | Conditional
    ItePpx {condTy :: f a, retTy :: f a}
  | -- | Constructor
    CtorPpx {ctor :: Text, retTy :: f a}
  | -- | Pattern matching
    MatchPpx {condTy :: f a, retTy :: f a, dyn :: Bool}
  | -- | Builtin operations
    BuiltinPpx {fn :: Text, ty :: f a}
  | -- | Coercion
    CoercePpx {fromTy :: f a, toTy :: f a}
  | -- | Lifting public functions
    LiftPpx {fn :: Text, to :: Maybe (f a)}
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
        attr :: OADTInstAttr,
        poly :: PolyType,
        ty :: f a,
        expr :: f a,
        label :: LLabel
      }
  | -- | Algebraic data type
    --
    -- Do not support empty type, so 'ctors' is an 'NonEmpty'.
    ADTDef {loc :: Int, ctors :: NonEmpty (Text, [f a])}
  | -- | Oblivious algebraic data type
    --
    -- It takes a single argument for now.
    OADTDef
      { loc :: Int,
        pubName :: Text,
        viewTy :: f a,
        binder :: Maybe Binder,
        bnd :: Scope () f a
      }
  | -- | Constructor
    CtorDef {paraTypes :: [f a], dataType :: Text}
  | -- | Builtin operation
    BuiltinDef
      { paraTypes :: [f a],
        resType :: f a,
        label :: LLabel
      }
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

type NamedDef a = (Text, Def a)

type Defs a = [NamedDef a]

getDefLoc :: DefB f a -> Int
getDefLoc = \case
  FunDef {..} -> loc
  ADTDef {..} -> loc
  OADTDef {..} -> loc
  _ -> -1

closeDefs :: Defs Text -> Defs a
closeDefs = (second (>>>= GV) <$>)

-- | A rudimentary pattern that only supports pairs
data Pat a = VarP (BinderM a) | PairP Int PairKind (Pat a) (Pat a)

-- | Constraint on a polymorphic type variable
data PolyConstraint
  = -- | No restriction on how a type variable can be instantiated.
    UnrestrictedC
  | -- | The type variable needs to be mergeable, i.e. it can be branches of a
    -- conditional.
    MergeableC
  deriving stock (Eq, Show)

-- | Whether a function definition can have type polymorphism
data PolyType = MonoT | PolyT PolyConstraint
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
  Lam {..} >>= f = Lam {argTy = argTy <&> (>>= f), bnd = bnd >>>= f, ..}
  App {..} >>= f = App {fn = fn >>= f, args = args <&> (>>= f), ..}
  Let {..} >>= f =
    Let
      { rhsTy = rhsTy <&> (>>= f),
        rhs = rhs >>= f,
        bnd = bnd >>>= f,
        ..
      }
  TUnit >>= _ = TUnit
  VUnit >>= _ = VUnit
  TBool {..} >>= _ = TBool {..}
  BLit {..} >>= _ = BLit {..}
  TInt {..} >>= _ = TInt {..}
  UInt >>= _ = UInt
  ILit {..} >>= _ = ILit {..}
  Ite {..} >>= f =
    Ite
      { cond = cond >>= f,
        left = left >>= f,
        right = right >>= f
      }
  Match {..} >>= f =
    Match
      { cond = cond >>= f,
        alts = alts <&> (>>>= f)
      }
  OIte {..} >>= f =
    OIte
      { cond = cond >>= f,
        left = left >>= f,
        right = right >>= f,
        ..
      }
  Prod {..} >>= f = Prod {left = left >>= f, right = right >>= f, ..}
  Psi {..} >>= f = Psi {viewTy = viewTy <&> (>>= f), ..}
  Pair {..} >>= f = Pair {left = left >>= f, right = right >>= f, ..}
  PMatch {..} >>= f =
    PMatch
      { cond = cond >>= f,
        bnd2 = bnd2 >>>= f,
        condTy = condTy <&> bimapBoth (>>= f),
        ..
      }
  Sum {..} >>= f = Sum {left = left >>= f, right = right >>= f, ..}
  Inj {..} >>= f =
    Inj
      { injTy = injTy <&> bimapBoth (>>= f),
        expr = expr >>= f,
        ..
      }
  OProj {..} >>= f =
    OProj
      { expr = expr >>= f,
        projTy = projTy <&> bimapBoth (>>= f),
        ..
      }
  SMatch {..} >>= f =
    SMatch
      { cond = cond >>= f,
        lBnd = lBnd >>>= f,
        rBnd = rBnd >>>= f,
        ..
      }
  Asc {..} >>= f = Asc {ty = ty >>= f, expr = expr >>= f, ..}
  Loc {..} >>= f = Loc {expr = expr >>= f, ..}
  TV {..} >>= _ = TV {..}
  Arb {..} >>= f = Arb {oblivTy = oblivTy <&> (>>= f)}
  PolyEq {..} >>= f = PolyEq {lhs = lhs >>= f, rhs = rhs >>= f}
  Ppx {..} >>= f = Ppx {ppx = ppx >>>= f}

instance Bound PpxB where
  ItePpx {..} >>>= f = ItePpx {condTy = condTy >>= f, retTy = retTy >>= f}
  CtorPpx {..} >>>= f = CtorPpx {retTy = retTy >>= f, ..}
  MatchPpx {..} >>>= f = MatchPpx {condTy = condTy >>= f, retTy = retTy >>= f, ..}
  BuiltinPpx {..} >>>= f = BuiltinPpx {ty = ty >>= f, ..}
  CoercePpx {..} >>>= f = CoercePpx {fromTy = fromTy >>= f, toTy = toTy >>= f}
  LiftPpx {..} >>>= f = LiftPpx {to = to <&> (>>= f), ..}

instance Bound DefB where
  FunDef {..} >>>= f = FunDef {ty = ty >>= f, expr = expr >>= f, ..}
  ADTDef {..} >>>= f = ADTDef {ctors = ctors <&> second ((>>= f) <$>), ..}
  OADTDef {..} >>>= f = OADTDef {viewTy = viewTy >>= f, bnd = bnd >>>= f, ..}
  CtorDef {..} >>>= f = CtorDef {paraTypes = paraTypes <&> (>>= f), ..}
  BuiltinDef {..} >>>= f =
    BuiltinDef
      { paraTypes = paraTypes <&> (>>= f),
        resType = resType >>= f,
        ..
      }

instance Eq1 Expr where
  liftEq eq V {name} V {name = name'} = eq name name'
  liftEq _ GV {ref} GV {ref = ref'} = ref == ref'
  liftEq eq Pi {ty, bnd} Pi {ty = ty', bnd = bnd'} =
    liftEq eq ty ty' && liftEq eq bnd bnd'
  liftEq eq Lam {bnd} Lam {bnd = bnd'} =
    -- Ignore type annotations
    liftEq eq bnd bnd'
  liftEq eq App {fn, args} App {fn = fn', args = args'} =
    -- Ignore application kind
    liftEq eq fn fn' && liftEq (liftEq eq) args args'
  liftEq eq Let {rhs, bnd} Let {rhs = rhs', bnd = bnd'} =
    -- Ignore type annotations
    liftEq eq rhs rhs' && liftEq eq bnd bnd'
  liftEq _ TUnit TUnit = True
  liftEq _ VUnit VUnit = True
  liftEq _ TBool {olabel} TBool {olabel = olabel'} = olabel == olabel'
  liftEq _ BLit {bLit} BLit {bLit = bLit'} = bLit == bLit'
  liftEq _ TInt {olabel} TInt {olabel = olabel'} = olabel == olabel'
  liftEq _ UInt UInt = True
  liftEq _ ILit {iLit} ILit {iLit = iLit'} = iLit == iLit'
  liftEq
    eq
    Ite {cond, left, right}
    Ite {cond = cond', left = left', right = right'} =
      liftEq eq cond cond'
        && liftEq eq left left'
        && liftEq eq right right'
  liftEq eq Match {cond, alts} Match {cond = cond', alts = alts'} =
    liftEq eq cond cond' && liftEq (liftEq eq) alts alts'
  liftEq
    eq
    OIte {cond, left, right}
    OIte {cond = cond', left = left', right = right'} =
      -- Ignore the leakage label
      liftEq eq cond cond'
        && liftEq eq left left'
        && liftEq eq right right'
  liftEq
    eq
    Prod {olabel, left, right}
    Prod {olabel = olabel', left = left', right = right'} =
      olabel == olabel' && liftEq eq left left' && liftEq eq right right'
  liftEq _ Psi {oadtName} Psi {oadtName = oadtName'} = oadtName == oadtName'
  liftEq eq Pair {left, right} Pair {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq
    eq
    PMatch {pairKind, cond, bnd2}
    PMatch {pairKind = pairKind', cond = cond', bnd2 = bnd2'} =
      -- Ignore type annotations
      pairKind == pairKind'
        && liftEq eq cond cond'
        && liftEq eq bnd2 bnd2'
  liftEq
    eq
    Sum {olabel, left, right}
    Sum {olabel = olabel', left = left', right = right'} =
      olabel == olabel' && liftEq eq left left' && liftEq eq right right'
  liftEq
    eq
    Inj {olabel, tag, expr}
    Inj {olabel = olabel', tag = tag', expr = expr'} =
      -- Ignore type annotations
      olabel == olabel' && tag == tag' && liftEq eq expr expr'
  liftEq eq OProj {projKind, expr} OProj {projKind = projKind', expr = expr'} =
    projKind == projKind' && liftEq eq expr expr'
  liftEq
    eq
    SMatch {olabel, cond, lBnd, rBnd}
    SMatch {olabel = olabel', cond = cond', lBnd = lBnd', rBnd = rBnd'} =
      -- Ignore type annotations
      olabel == olabel'
        && liftEq eq cond cond'
        && liftEq eq lBnd lBnd'
        && liftEq eq rBnd rBnd'
  liftEq eq Asc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Asc {expr} = liftEq eq expr' expr
  liftEq eq Loc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Loc {expr} = liftEq eq expr' expr
  liftEq _ TV {idx} TV {idx = idx'} = idx == idx'
  liftEq eq PolyEq {lhs, rhs} PolyEq {lhs = lhs', rhs = rhs'} =
    liftEq eq lhs lhs' && liftEq eq rhs rhs'
  liftEq eq Ppx {ppx} Ppx {ppx = ppx'} = liftEq eq ppx ppx'
  liftEq _ _ _ = False

instance Eq1 Ppx where
  liftEq eq ItePpx {condTy, retTy} ItePpx {condTy = condTy', retTy = retTy'} =
    liftEq eq condTy condTy' && liftEq eq retTy retTy'
  liftEq eq CtorPpx {ctor, retTy} CtorPpx {ctor = ctor', retTy = retTy'} =
    ctor == ctor' && liftEq eq retTy retTy'
  liftEq
    eq
    MatchPpx {condTy, retTy}
    MatchPpx {condTy = condTy', retTy = retTy'} =
      liftEq eq condTy condTy' && liftEq eq retTy retTy'
  liftEq eq BuiltinPpx {fn, ty} BuiltinPpx {fn = fn', ty = ty'} =
    fn == fn' && liftEq eq ty ty'
  liftEq
    eq
    CoercePpx {fromTy, toTy}
    CoercePpx {fromTy = fromTy', toTy = toTy'} =
      liftEq eq fromTy fromTy' && liftEq eq toTy toTy'
  liftEq _ _ _ = False

instance (Eq a) => Eq (Expr a) where (==) = eq1

instance (Eq a) => Eq (Ppx a) where (==) = eq1

instance PlateM (Expr Name) where
  plateM f Let {..} = do
    rhsTy' <- mapM f rhsTy
    rhs' <- f rhs
    (x, body) <- unbind1 bnd
    body' <- f body
    return Let {rhsTy = rhsTy', rhs = rhs', bnd = abstract_ x body', ..}
  plateM f Pi {..} = do
    ty' <- f ty
    (x, body) <- unbind1 bnd
    body' <- f body
    return Pi {ty = ty', bnd = abstract_ x body', ..}
  plateM f Lam {..} = do
    argTy' <- mapM f argTy
    (x, body) <- unbind1 bnd
    body' <- f body
    return Lam {argTy = argTy', bnd = abstract_ x body', ..}
  plateM f App {..} = do
    fn' <- f fn
    args' <- mapM f args
    return App {fn = fn', args = args', ..}
  plateM f Ite {..} = do
    cond' <- f cond
    left' <- f left
    right' <- f right
    return Ite {cond = cond', left = left', right = right'}
  plateM f Match {..} = do
    cond' <- f cond
    alts' <- mapM (biplateM f) alts
    return Match {cond = cond', alts = alts'}
  plateM f OIte {..} = do
    cond' <- f cond
    left' <- f left
    right' <- f right
    return OIte {cond = cond', left = left', right = right', ..}
  plateM f Prod {..} = do
    left' <- f left
    right' <- f right
    return Prod {left = left', right = right', ..}
  plateM f Psi {..} = do
    viewTy' <- mapM f viewTy
    return Psi {viewTy = viewTy', ..}
  plateM f Pair {..} = do
    left' <- f left
    right' <- f right
    return Pair {left = left', right = right', ..}
  plateM f PMatch {..} = do
    condTy' <- mapM (traverseBoth f) condTy
    cond' <- f cond
    ((xl, xr), body) <- unbind2 bnd2
    body' <- f body
    return
      PMatch
        { condTy = condTy',
          cond = cond',
          bnd2 = abstract_ (xl, xr) body',
          ..
        }
  plateM f Sum {..} = do
    left' <- f left
    right' <- f right
    return Sum {left = left', right = right', ..}
  plateM f Inj {..} = do
    injTy' <- mapM (traverseBoth f) injTy
    expr' <- f expr
    return Inj {injTy = injTy', expr = expr', ..}
  plateM f OProj {..} = do
    projTy' <- mapM (traverseBoth f) projTy
    expr' <- f expr
    return OProj {projTy = projTy', expr = expr', ..}
  plateM f SMatch {..} = do
    cond' <- f cond
    (xl, lBody) <- unbind1 lBnd
    lBody' <- f lBody
    (xr, rBody) <- unbind1 rBnd
    rBody' <- f rBody
    return
      SMatch
        { cond = cond',
          lBnd = abstract_ xl lBody',
          rBnd = abstract_ xr rBody',
          ..
        }
  plateM f Asc {..} = do
    ty' <- f ty
    expr' <- f expr
    return Asc {ty = ty', expr = expr', ..}
  plateM f Loc {..} = do
    expr' <- f expr
    return Loc {expr = expr', ..}
  plateM f Arb {..} = do
    oblivTy' <- mapM f oblivTy
    return Arb {oblivTy = oblivTy'}
  plateM f PolyEq {..} = do
    lhs' <- f lhs
    rhs' <- f rhs
    return PolyEq {lhs = lhs', rhs = rhs'}
  plateM f Ppx {..} = do
    ppx' <- biplateM f ppx
    return Ppx {ppx = ppx'}
  plateM _ e = return e

instance BiplateM (Ppx Name) (Ty Name) where
  biplateM f ItePpx {..} = do
    condTy' <- f condTy
    retTy' <- f retTy
    return ItePpx {condTy = condTy', retTy = retTy'}
  biplateM f CtorPpx {..} = do
    retTy' <- f retTy
    return CtorPpx {retTy = retTy', ..}
  biplateM f MatchPpx {..} = do
    condTy' <- f condTy
    retTy' <- f retTy
    return MatchPpx {condTy = condTy', retTy = retTy', ..}
  biplateM f BuiltinPpx {..} = do
    ty' <- f ty
    return BuiltinPpx {ty = ty', ..}
  biplateM f CoercePpx {..} = do
    fromTy' <- f fromTy
    toTy' <- f toTy
    return CoercePpx {fromTy = fromTy', toTy = toTy'}
  biplateM f LiftPpx {..} = do
    to' <- mapM f to
    return LiftPpx {to = to', ..}

instance BiplateM (Def Name) (Expr Name) where
  biplateM f FunDef {..} = do
    ty' <- f ty
    expr' <- f expr
    return FunDef {ty = ty', expr = expr', ..}
  biplateM f ADTDef {..} = do
    ctors' <- forM ctors $ secondM (mapM f)
    return ADTDef {ctors = ctors', ..}
  biplateM f OADTDef {..} = do
    viewTy' <- f viewTy
    (x, body) <- unbind1 bnd
    body' <- f body
    return OADTDef {viewTy = viewTy', bnd = abstract_ x body', ..}
  -- Skip handling constructor definitions, as they should be in sync with the ADT
  -- definitions. The caller is responsible for resyncing these two definitions.
  -- Builtin definitions are not handled either.
  biplateM _ def = return def

----------------------------------------------------------------
-- Smart constructors

lam_ :: (a ~ Text) => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a
lam_ binder argTy body =
  Lam
    { bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

pi_ :: (a ~ Text) => BinderM a -> Ty a -> Expr a -> Expr a
pi_ binder ty body =
  Pi
    { bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

arrow_ :: Ty a -> Ty a -> Ty a
arrow_ dom cod =
  Pi
    { ty = dom,
      binder = Just Anon,
      bnd = abstract (const Nothing) cod
    }

arrows_ :: [Ty a] -> Ty a -> Ty a
arrows_ = flip $ foldr arrow_

(@@) :: Expr a -> [Expr a] -> Expr a
fn @@ args = App {..}

infixl 2 @@

(@@@) :: Text -> [Expr a] -> Expr a
fn @@@ args = App {fn = GV fn, ..}

infixl 2 @@@

let_ :: (a ~ Text) => BinderM a -> Maybe (Ty a) -> Expr a -> Expr a -> Expr a
let_ binder rhsTy rhs body =
  Let
    { bnd = abstractBinder binder body,
      binder = Just binder,
      ..
    }

ite_ :: Expr a -> Expr a -> Expr a -> Expr a
ite_ cond left right = Ite {..}

oite_ :: Expr a -> Expr a -> Expr a -> Expr a
oite_ cond left right = OIte {label = LeakyL, ..}

mux_ :: Expr a -> Expr a -> Expr a -> Expr a
mux_ cond left right = OIte {label = SafeL, ..}

inj_ :: OLabel -> Bool -> Expr a -> Expr a
inj_ olabel tag expr = Inj {injTy = Nothing, ..}

inl_ :: Expr a -> Expr a
inl_ = inj_ PublicL True

inr_ :: Expr a -> Expr a
inr_ = inj_ PublicL False

oproj_ :: OProjKind -> Expr a -> Expr a
oproj_ projKind expr = OProj {projTy = Nothing, ..}

prod_ :: [Ty a] -> Ty a
prod_ [] = TUnit
prod_ ts = foldr1 (Prod PublicL) ts

deprod :: Ty a -> [Ty a]
deprod TUnit = []
deprod Prod {olabel = PublicL, ..} = left : deprod right
deprod Loc {..} = deprod expr
deprod t = [t]

tuple_ :: [Expr a] -> Expr a
tuple_ [] = VUnit
tuple_ es = foldr1 (Pair PublicP) es

thunk_ :: Expr a -> Expr a
thunk_ e = Lam {argTy = Just TUnit, binder = Nothing, bnd = abstract0 e}

match_ :: (a ~ Text) => Expr a -> NonEmpty (Text, [BinderM a], Expr a) -> Expr a
match_ cond alts = Match {alts = uncurry3 matchAlt_ <$> alts, ..}

smatch_ ::
  (a ~ Text) =>
  OLabel ->
  Expr a ->
  BinderM a ->
  Expr a ->
  BinderM a ->
  Expr a ->
  Expr a
smatch_ olabel cond lBinder lBody rBinder rBody =
  SMatch
    { lBinder = Just lBinder,
      lBnd = abstractBinder lBinder lBody,
      rBinder = Just rBinder,
      rBnd = abstractBinder rBinder rBody,
      ..
    }

smatchPat_ ::
  (a ~ Text) =>
  OLabel ->
  Expr a ->
  Pat a ->
  Expr a ->
  Pat a ->
  Expr a ->
  Expr a
smatchPat_ olabel cond lPat lBody rPat rBody = runFreshM $ do
  (lBinder, lBody') <- elabPat lPat lBody
  (rBinder, rBody') <- elabPat rPat rBody
  return $ smatch_ olabel cond lBinder lBody' rBinder rBody'

pmatch_ ::
  (a ~ Text) => PairKind -> Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
pmatch_ pairKind cond lBinder rBinder body =
  PMatch
    { condTy = Nothing,
      lBinder = Just lBinder,
      rBinder = Just rBinder,
      bnd2 = abstractBinder (lBinder, rBinder) body,
      ..
    }

-- The pattern has to be 'PairP'.
pmatchPat_ :: (a ~ Text) => Expr a -> Pat a -> Expr a -> Expr a
pmatchPat_ cond (PairP _ pairKind left right) body = runFreshM $ do
  (lBinder, rBinder, body') <- elabPatPair left right body
  return $ pmatch_ pairKind cond lBinder rBinder body'
pmatchPat_ _ _ _ = oops "Not a pair pattern"

lamPat_ :: (a ~ Text) => Pat a -> Maybe (Ty a) -> Expr a -> Expr a
lamPat_ pat argTy body = runFreshM $ do
  (binder, body') <- elabPat pat body
  return $ lam_ binder argTy body'

-- | Elaborate pattern.
elabPat :: (a ~ Text, MonadFresh m) => Pat a -> Expr a -> m (BinderM a, Expr a)
elabPat (VarP binder) e = return (binder, e)
elabPat (PairP loc pairKind left right) e = do
  x <- fresh
  let name = internalName ("p" <> show x)
      binder = Named loc name
  (lBinder, rBinder, body) <- elabPatPair left right e
  return
    ( binder,
      Loc {expr = pmatch_ pairKind (V name) lBinder rBinder body, ..}
    )

-- | Elaborate a pair of patterns.
elabPatPair ::
  (a ~ Text, MonadFresh m) =>
  Pat a ->
  Pat a ->
  Expr a ->
  m (BinderM a, BinderM a, Expr a)
elabPatPair left right e = do
  (rBinder, e') <- elabPat right e
  (lBinder, body) <- elabPat left e'
  return (lBinder, rBinder, body)

----------------------------------------------------------------
-- Smart constructors that work with 'Name's

lam' :: Name -> Ty Name -> Expr Name -> Expr Name
lam' x t body =
  Lam
    { argTy = Just t,
      binder = Nothing,
      bnd = abstract_ x body
    }

lams' :: [(Name, Ty Name)] -> Expr Name -> Expr Name
lams' = flip $ foldr $ uncurry lam'

let' :: Name -> Ty Name -> Expr Name -> Expr Name -> Expr Name
let' x t rhs body =
  Let
    { rhsTy = Just t,
      binder = Nothing,
      bnd = abstract_ x body,
      ..
    }

lets' :: [(Name, Ty Name, Expr Name)] -> Expr Name -> Expr Name
lets' = flip $ foldr $ uncurry3 let'

match' :: Expr Name -> NonEmpty (Text, [Name], Expr Name) -> Expr Name
match' cond alts = Match {alts = uncurry3 matchAlt' <$> alts, ..}

pmatch' :: PairKind -> Expr Name -> Name -> Name -> Expr Name -> Expr Name
pmatch' pairKind cond xl xr body =
  PMatch
    { condTy = Nothing,
      lBinder = Nothing,
      rBinder = Nothing,
      bnd2 = abstract_ (xl, xr) body,
      ..
    }

smatch' :: Expr Name -> Name -> Expr Name -> Name -> Expr Name -> Expr Name
smatch' cond xl lBody xr rBody =
  SMatch
    { olabel = PublicL,
      lBinder = Nothing,
      lBnd = abstract_ xl lBody,
      rBinder = Nothing,
      rBnd = abstract_ xr rBody,
      ..
    }

pi' :: Name -> Ty Name -> Ty Name -> Ty Name
pi' x ty body = Pi {binder = Nothing, bnd = abstract_ x body, ..}

lamP ::
  (MonadFresh m) => [(Name, Maybe Binder, Ty Name)] -> Expr Name -> m (Expr Name)
lamP [] e = return $ thunk_ e
lamP [(x, binder, t)] e =
  return
    Lam
      { argTy = Just t,
        bnd = abstract_ x e,
        ..
      }
lamP ctx e = do
  p <- fresh
  e' <- go ctx p
  return $ lam' p (prod_ [t | (_, _, t) <- ctx]) e'
  where
    go [(xl, lBinder, _), (xr, rBinder, _)] p =
      return
        PMatch
          { pairKind = PublicP,
            condTy = Nothing,
            cond = V p,
            bnd2 = abstract_ (xl, xr) e,
            ..
          }
    go ((xl, lBinder, _) : ctx'@(_ : _)) p = do
      xr <- fresh
      e' <- go ctx' xr
      return
        PMatch
          { pairKind = PublicP,
            condTy = Nothing,
            cond = V p,
            bnd2 = abstract_ (xl, xr) e',
            rBinder = Nothing,
            ..
          }
    go _ _ = oops "Fewer than 2 entries"

----------------------------------------------------------------
-- Utilities

-- | Check if a type is a non-dependent function type.
--
-- This function only checks the top-level function type.
isArrow1 :: Ty Name -> Maybe (Ty Name, Ty Name)
isArrow1 Pi {..} = do
  body <- instantiate0 bnd
  return (ty, body)
isArrow1 Loc {..} = isArrow1 expr
isArrow1 _ = Nothing

-- | Check if a type is a non-dependent type, and return the list of argument
-- types and the return type.
--
-- This function checks the function codomain, but not the argument types.
isArrow :: Ty Name -> Maybe ([Ty Name], Ty Name)
isArrow Pi {..} = do
  body <- instantiate0 bnd
  (argTs, t) <- isArrow body
  return (ty : argTs, t)
isArrow Loc {..} = isArrow expr
isArrow t = Just ([], t)

-- | Make the taype expressions more readable.
--
-- This is only used for error reporting and printing, as the resulting
-- expression is not in core taype ANF.
readableExpr :: (MonadFresh m) => Expr Name -> m (Expr Name)
readableExpr = transformM go
  where
    go Let {binder = Nothing, ..} = return $ instantiate_ rhs bnd
    go e = return e

-- | Make all definitions readable.
--
-- The result can only be used for printing, as the definitions are not in ANF.
readableDefs :: Defs Name -> Defs Name
readableDefs = secondF (runFreshM . biplateM readableExpr)

----------------------------------------------------------------
-- Pretty printer

instance Cute Kind

-- | Pretty printer for a taype expression
instance Cute (Expr Text) where
  cute V {..} = cute name
  cute GV {..} | isInfix ref = return $ parens $ pretty ref
  cute GV {..} = cute ref
  cute e@Pi {..} = do
    (x, body) <- unbind1NameOrBinder binder bnd
    binderDoc <- cuteTypeBinder e x ty binder
    bodyDoc <- cute body
    return $ group binderDoc <+> "->" <> line <> bodyDoc
  cute e@Lam {} = cuteLam False e
  cute e@App {fn = GV {..}, args = [left, right]}
    | isInfix ref = cuteInfix e ref left right
  cute App {..} = cuteApp fn args
  cute Let {..} = do
    (x, body) <- unbind1NameOrBinder binder bnd
    binderDoc <- cuteBinder x rhsTy
    rhsDoc <- cute rhs
    bodyDoc <- cute body
    return $ cuteLetDoc binderDoc rhsDoc bodyDoc
  cute TUnit = "unit"
  cute VUnit = "()"
  cute TBool {..} = cute $ accentOfOLabel olabel <> "bool"
  cute BLit {..} = if bLit then "true" else "false"
  cute TInt {..} = cute $ accentOfOLabel olabel <> "int"
  cute UInt = "uint"
  cute ILit {..} = cute iLit
  cute Ite {..} = cuteIte PublicL cond left right
  cute Match {..} = cuteMatch PublicL True cond alts
  cute OIte {..} = cuteIte OblivL cond left right
  cute e@Prod {..} = cuteInfix e (accentOfOLabel olabel <> "*") left right
  cute Psi {..} = cute $ psiName oadtName
  cute Pair {..} = cutePair pairKind left right
  cute PMatch {..} = cutePMatch pairKind cond lBinder rBinder bnd2
  cute e@Sum {..} = cuteInfix e (accentOfOLabel olabel <> "+") left right
  cute Inj {..} = do
    cuteApp_
      (pretty (accentOfOLabel olabel <> if tag then "inl" else "inr"))
      [expr]
  cute OProj {..} = do
    projDoc <-
      cute $
        oblivName $
          "pr" <> case projKind of
            TagP -> "t"
            LeftP -> "l"
            RightP -> "r"
    cuteApp_ projDoc [expr]
  cute SMatch {..} = do
    condDoc <- cute cond
    (xl, lBody) <- unbind1NameOrBinder lBinder lBnd
    (xr, rBody) <- unbind1NameOrBinder rBinder rBnd
    lBodyDoc <- cute lBody
    rBodyDoc <- cute rBody
    return $
      cuteMatchDoc olabel True condDoc $
        cuteAltDocs
          [ (accentOfOLabel olabel <> "inl", [xl], lBodyDoc),
            (accentOfOLabel olabel <> "inr", [xr], rBodyDoc)
          ]
  cute Asc {..} = do
    tyDoc <- cute ty
    exprDoc <- cute expr
    return $
      parens $
        hang $
          align exprDoc
            <> sep1 ((if trustMe then colon <> colon else colon) <+> tyDoc)
  cute Loc {..} = cute expr
  cute TV {..} = return $ "'a" <> (if idx == 0 then "" else pretty idx)
  cute Arb {..} = case oblivTy of
    Just ty -> do
      tyDoc <- cute ty
      return $ parens $ arbDoc <> tyDoc
    _ -> return arbDoc
    where
      arbDoc = pretty (oblivAccent <> oblivAccent)
  cute e@PolyEq {..} = cuteInfix e "=" lhs rhs
  cute Ppx {..} = cute ppx

-- | Pretty printer for preprocessors
instance Cute (Ppx Text) where
  cute = \case
    ItePpx {..} -> go "if" [condTy, retTy]
    CtorPpx {..} -> go ctor [retTy]
    MatchPpx {..} -> go "match" [condTy, retTy]
    BuiltinPpx {..} -> go fn [ty]
    CoercePpx {..} -> go "coerce" [fromTy, toTy]
    LiftPpx {..} ->
      go "lift" $
        [GV fn] <> case to of
          Just ty -> [ty]
          Nothing -> []
    where
      go name = cuteApp_ (pretty (ppxName name))

-- | Pretty printer for taype definitions
cuteDefsDoc :: Options -> Defs Text -> Doc
cuteDefsDoc options = foldMap go
  where
    go (name, def) = cuteDefDoc options name def <> hardline2

-- | Pretty printer for a definition
cuteDefDoc :: Options -> Text -> Def Text -> Doc
cuteDefDoc options name = \case
  FunDef {..} ->
    hang $
      "fn"
        <> leakyDoc
          <+> go (cuteBinder name (Just ty))
          <+> equals
        <> go (cuteLam True expr)
    where
      leakyDoc = case label of
        LeakyL -> "'"
        _ -> ""
  ADTDef {..} ->
    hang $
      "data"
        <+> pretty name
        <> sep1
          (equals <+> sepWith (line <> pipe <> space) (cuteCtor <$> ctors))
    where
      cuteCtor (ctor, paraTypes) = go $ cuteApp_ (pretty ctor) paraTypes
  OADTDef {..} ->
    hang $ "obliv" <+> pretty name <+> rest
    where
      rest = go $ do
        (x, body) <- unbind1NameOrBinder binder bnd
        binderDoc <- cuteBinder x (Just viewTy)
        bodyDoc <- cute body
        return $ parens binderDoc <+> equals </> bodyDoc
  _ -> oops "Builtin functions or constructors in the definitions"
  where
    go = runCuteM options

cuteLam :: Bool -> Expr Text -> CuteM Doc
cuteLam isRoot e = do
  (binderDocs, bodyDoc) <- go e
  return $ cuteLamDoc isRoot binderDocs bodyDoc
  where
    go Lam {..} = do
      (x, body) <- unbind1NameOrBinder binder bnd
      binderDoc <- cuteEnclosedBinder x argTy
      (binderDocs, bodyDoc) <- go body
      return (binderDoc : binderDocs, bodyDoc)
    go Loc {..} = go expr
    go expr = ([],) <$> cute expr

cuteBinder :: Text -> Maybe (Ty Text) -> CuteM Doc
cuteBinder x Nothing = cute x
cuteBinder x (Just ty) = do
  tyDoc <- cute ty
  return $
    hang $
      pretty x <> sep1_ x (colon <+> align (group tyDoc))

cuteEnclosedBinder :: Text -> Maybe (Ty Text) -> CuteM Doc
cuteEnclosedBinder x mTy = do
  doc <- cuteBinder x mTy
  return $ if isJust mTy then parens doc else doc

cuteTypeBinder ::
  Ty Text ->
  Text ->
  Ty Text ->
  Maybe Binder ->
  CuteM Doc
cuteTypeBinder super x ty = \case
  Just Anon -> ifM (asks optInternalNames) go (cuteSub super ty)
  _ -> go
  where
    go = parens <$> cuteBinder x (Just ty)

instance HasPLevel (Expr a) where
  plevel = \case
    V {} -> 0
    GV {} -> 0
    TV {} -> 0
    -- Do not distinguish infix further.
    App {fn = GV {..}} | isInfix ref -> 20
    App {} -> 10
    Psi {} -> 0
    TUnit -> 0
    VUnit -> 0
    TBool {} -> 0
    BLit {} -> 0
    TInt {} -> 0
    UInt -> 0
    ILit {} -> 0
    Prod {} -> 20
    Pair {} -> 0
    Sum {} -> 20
    Inj {} -> 10
    Asc {} -> 0
    Loc {..} -> plevel expr
    Arb {} -> 0
    PolyEq {} -> 20
    Ppx {} -> 0
    _ -> 90

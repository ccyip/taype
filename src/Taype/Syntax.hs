{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
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
    isCtor,
    PolyConstraint (..),
    PolyType (..),

    -- * OADT structure
    OADTInst (..),
    OADTInstAttr (..),
    attrOfName,
    instNamesOfOADT,
    oadtNameOfInst,

    -- * Smart constructors
    lam_,
    pi_,
    (@@),
    (@@@),
    let_,
    ite_,
    oite_,
    mux_,
    oinj_,
    oproj_,
    prod_,
    match_,
    omatch_,
    omatchPat_,
    pmatch_,
    pmatchPat_,
    lam',
    lams',
    let',
    lets',
    pmatch',
    pi',
    arrow_,
    arrows_,

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
import Data.Char
import Data.Functor.Classes
import Data.List (foldr1)
import Data.Text qualified as T
import Relude.Extra (bimapBoth, traverseBoth)
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Text.Show qualified
import Prelude hiding (group)

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
      { appKind :: AppKind,
        fn :: Expr a,
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
  | -- | Oblivious sum type
    OSum {left :: Ty a, right :: Ty a}
  | -- | Oblivious injection
    OInj
      { injTy :: Maybe (Ty a, Ty a),
        tag :: Bool,
        expr :: Expr a
      }
  | -- | Oblivious sum projections
    OProj
      { projTy :: Maybe (Ty a, Ty a),
        projKind :: OProjKind,
        expr :: Expr a
      }
  | -- | Oblivious sum type pattern matching
    --
    -- This does not appear in the core language, as it is just syntax sugar for
    -- oblivious if and oblivious sum projections.
    OMatch
      { cond :: Expr a,
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
    -- We do not support general type polymorphism yet. This (unique) type
    -- variable is only used for defining OADT match instances.
    TV
  | -- | Arbitrary oblivious value
    Arb {oblivTy :: Maybe (Ty a)}
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
    MatchPpx {condTy :: f a, retTy :: f a}
  | -- | Builtin operations
    BuiltinPpx {fn :: Text, retTy :: f a}
  | -- | Coercion
    CoercePpx {fromTy :: f a, toTy :: f a}
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
data Pat a = VarP (BinderM a) | PairP Int (Pat a) (Pat a)

-- | Check if a name is a constructor.
isCtor :: Text -> Bool
isCtor x = maybe False (\(c, _) -> isUpper c) $ T.uncons x

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
-- OADT structure

data OADTInst
  = -- | Section
    SectionInst {oadtName :: Text}
  | -- | Retraction
    RetractionInst {oadtName :: Text}
  | -- | Constructor
    CtorInst {oadtName :: Text, ctor :: Text}
  | -- | View of an ADT
    ViewInst {oadtName :: Text}
  | -- | Join of public views
    JoinInst {oadtName :: Text}
  | -- | Convert an OADT with different public views
    ReshapeInst {oadtName :: Text}
  | -- | Pattern matching
    MatchInst {oadtName :: Text}
  | -- | Coercion between two OADTs
    CoerceInst {oadtName :: Text, oadtTo :: Text}
  deriving stock (Eq, Show)

data OADTInstAttr
  = KnownInst OADTInst
  | UnknownInst
  | NotAnInst
  deriving stock (Eq, Show)

-- | Parse an instance from the given name.
attrOfName :: Text -> OADTInstAttr
attrOfName x = case T.splitOn instInfix x of
  xs | any T.null xs -> UnknownInst
  [_] -> NotAnInst
  [oadtName, instName] ->
    if
        | instName == sectionInstName -> KnownInst $ SectionInst {..}
        | instName == retractionInstName -> KnownInst $ RetractionInst {..}
        | isCtor instName -> KnownInst $ CtorInst {ctor = instName, ..}
        | instName == "view" -> KnownInst $ ViewInst {..}
        | instName == "join" -> KnownInst $ JoinInst {..}
        | instName == "reshape" -> KnownInst $ ReshapeInst {..}
        | instName == "match" -> KnownInst $ MatchInst {..}
        | otherwise -> UnknownInst
  [oadtName, oadtTo, "coerce"] -> KnownInst $ CoerceInst {..}
  _ -> UnknownInst

-- | Return a list of must-have instance names, given an OADT name.
instNamesOfOADT :: Text -> [Text]
instNamesOfOADT x = [sectionName x, retractionName x]

oadtNameOfInst :: OADTInst -> Text
oadtNameOfInst = \case
  SectionInst {..} -> oadtName
  RetractionInst {..} -> oadtName
  CtorInst {..} -> oadtName
  ViewInst {..} -> oadtName
  JoinInst {..} -> oadtName
  ReshapeInst {..} -> oadtName
  MatchInst {..} -> oadtName
  CoerceInst {..} -> oadtName

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
  OSum {..} >>= f = OSum {left = left >>= f, right = right >>= f}
  OInj {..} >>= f =
    OInj
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
  OMatch {..} >>= f =
    OMatch
      { cond = cond >>= f,
        lBnd = lBnd >>>= f,
        rBnd = rBnd >>>= f,
        ..
      }
  Asc {..} >>= f = Asc {ty = ty >>= f, expr = expr >>= f, ..}
  Loc {..} >>= f = Loc {expr = expr >>= f, ..}
  TV >>= _ = TV
  Arb {..} >>= f = Arb {oblivTy = oblivTy <&> (>>= f)}
  Ppx {..} >>= f = Ppx {ppx = ppx >>>= f}

instance Bound PpxB where
  ItePpx {..} >>>= f = ItePpx {condTy = condTy >>= f, retTy = retTy >>= f}
  CtorPpx {..} >>>= f = CtorPpx {retTy = retTy >>= f, ..}
  MatchPpx {..} >>>= f = MatchPpx {condTy = condTy >>= f, retTy = retTy >>= f}
  BuiltinPpx {..} >>>= f = BuiltinPpx {retTy = retTy >>= f, ..}
  CoercePpx {..} >>>= f = CoercePpx {fromTy = fromTy >>= f, toTy = toTy >>= f}

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
  liftEq eq OSum {left, right} OSum {left = left', right = right'} =
    liftEq eq left left' && liftEq eq right right'
  liftEq eq OInj {tag, expr} OInj {tag = tag', expr = expr'} =
    -- Ignore type annotations
    tag == tag' && liftEq eq expr expr'
  liftEq eq OProj {projKind, expr} OProj {projKind = projKind', expr = expr'} =
    projKind == projKind' && liftEq eq expr expr'
  liftEq
    eq
    OMatch {cond, lBnd, rBnd}
    OMatch {cond = cond', lBnd = lBnd', rBnd = rBnd'} =
      -- Ignore type annotations
      liftEq eq cond cond' && liftEq eq lBnd lBnd' && liftEq eq rBnd rBnd'
  liftEq eq Asc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Asc {expr} = liftEq eq expr' expr
  liftEq eq Loc {expr} expr' = liftEq eq expr expr'
  liftEq eq expr' Loc {expr} = liftEq eq expr' expr
  liftEq _ TV TV = True
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
  liftEq eq BuiltinPpx {fn, retTy} BuiltinPpx {fn = fn', retTy = retTy'} =
    fn == fn' && liftEq eq retTy retTy'
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
  plateM f OSum {..} = do
    left' <- f left
    right' <- f right
    return OSum {left = left', right = right'}
  plateM f OInj {..} = do
    injTy' <- mapM (traverseBoth f) injTy
    expr' <- f expr
    return OInj {injTy = injTy', expr = expr', ..}
  plateM f OProj {..} = do
    projTy' <- mapM (traverseBoth f) projTy
    expr' <- f expr
    return OProj {projTy = projTy', expr = expr', ..}
  plateM f OMatch {..} = do
    cond' <- f cond
    (xl, lBody) <- unbind1 lBnd
    lBody' <- f lBody
    (xr, rBody) <- unbind1 rBnd
    rBody' <- f rBody
    return
      OMatch
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
    return MatchPpx {condTy = condTy', retTy = retTy'}
  biplateM f BuiltinPpx {..} = do
    retTy' <- f retTy
    return BuiltinPpx {retTy = retTy', ..}
  biplateM f CoercePpx {..} = do
    fromTy' <- f fromTy
    toTy' <- f toTy
    return CoercePpx {fromTy = fromTy', toTy = toTy'}

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
fn @@ args = App {appKind = FunApp, ..}
infixl 2 @@

(@@@) :: Text -> [Expr a] -> Expr a
fn @@@ args = App {appKind = TypeApp, fn = GV fn, ..}
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

oinj_ :: Bool -> Expr a -> Expr a
oinj_ tag expr = OInj {injTy = Nothing, ..}

oproj_ :: OProjKind -> Expr a -> Expr a
oproj_ projKind expr = OProj {projTy = Nothing, ..}

prod_ :: [Ty a] -> Ty a
prod_ [] = TUnit
prod_ ts = foldr1 (Prod PublicL) ts

match_ :: (a ~ Text) => Expr a -> NonEmpty (Text, [BinderM a], Expr a) -> Expr a
match_ cond alts = Match {alts = uncurry3 matchAlt_ <$> alts, ..}

omatch_ ::
  (a ~ Text) =>
  Expr a ->
  BinderM a ->
  Expr a ->
  BinderM a ->
  Expr a ->
  Expr a
omatch_ cond lBinder lBody rBinder rBody =
  OMatch
    { lBinder = Just lBinder,
      lBnd = abstractBinder lBinder lBody,
      rBinder = Just rBinder,
      rBnd = abstractBinder rBinder rBody,
      ..
    }

omatchPat_ ::
  (a ~ Text) =>
  Expr a ->
  Pat a ->
  Expr a ->
  Pat a ->
  Expr a ->
  Expr a
omatchPat_ cond lPat lBody rPat rBody = runFreshM $ do
  xl <- freshPatBinder lPat
  lBody' <- elabPat (pmatch_ OblivP) lPat (V $ fromBinder xl) lBody
  xr <- freshPatBinder rPat
  rBody' <- elabPat (pmatch_ OblivP) rPat (V $ fromBinder xr) rBody
  return $ omatch_ cond xl lBody' xr rBody'

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
pmatchPat_ :: (a ~ Text) => PairKind -> Expr a -> Pat a -> Expr a -> Expr a
pmatchPat_ pairKind cond pat body =
  runFreshM $ elabPat (pmatch_ pairKind) pat cond body

-- | Elaborate pattern.
--
-- The first argument is the smart constructor of case analysis for product-like
-- types, e.g., public and oblivious products.
--
-- The second argument is the pattern to elaborate.
--
-- The third argument is the source expression of the pair pattern 'PairP',
-- which is not used if the pattern is simply a 'VarP'.
--
-- The last argument is the pattern matching body.
--
-- The invariant of this function may be a bit awkward: the returned expression
-- is closed under all pattern variables in the pattern if the pattern is a
-- 'PairP', while it is open if the pattern is a 'VarP'.
elabPat ::
  (a ~ Text, MonadFresh m) =>
  (Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a) ->
  Pat a ->
  Expr a ->
  Expr a ->
  m (Expr a)
elabPat pmatch = go
  where
    go (VarP _) _ body = return body
    go (PairP _ lPat rPat) src body = do
      xl <- freshPatBinder lPat
      xr <- freshPatBinder rPat
      body' <- go rPat (srcFromBinder xr) body >>= go lPat (srcFromBinder xl)
      return $ pmatch src xl xr body'
    srcFromBinder (Named loc name) = Loc {expr = V name, ..}
    srcFromBinder _ = oops "Not a pair pattern"

freshPatBinder :: (a ~ Text, MonadFresh m) => Pat a -> m (BinderM a)
freshPatBinder (VarP binder) = return binder
freshPatBinder (PairP loc _ _) = do
  x <- fresh
  return $ Named loc $ internalName ("p" <> show x)

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

pmatch' :: PairKind -> Expr Name -> Name -> Name -> Expr Name -> Expr Name
pmatch' pairKind cond xl xr body =
  PMatch
    { condTy = Nothing,
      lBinder = Nothing,
      rBinder = Nothing,
      bnd2 = abstract_ (xl, xr) body,
      ..
    }

pi' :: Name -> Ty Name -> Ty Name -> Ty Name
pi' x ty body = Pi {binder = Nothing, bnd = abstract_ x body, ..}

----------------------------------------------------------------
-- Pretty printer

instance Cute Kind

-- | Pretty printer for a taype expression
instance Cute (Expr Text) where
  cute V {..} = cute name
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
  cute e@Let {} = do
    (bindingDocs, bodyDoc) <- go e
    return $ cuteLetDoc bindingDocs bodyDoc
    where
      go Let {..} = do
        (x, body) <- unbind1NameOrBinder binder bnd
        binderDoc <- cuteBinder x rhsTy
        rhsDoc <- cute rhs
        (bindingDocs, bodyDoc) <- go body
        return ((binderDoc, rhsDoc) : bindingDocs, bodyDoc)
      go Loc {..} = go expr
      go expr = ([],) <$> cute expr
  cute TUnit = "unit"
  cute VUnit = "()"
  cute TBool {..} = cute $ accentOfOLabel olabel <> "bool"
  cute BLit {..} = if bLit then "True" else "False"
  cute TInt {..} = cute $ accentOfOLabel olabel <> "int"
  cute ILit {..} = cute iLit
  cute Ite {..} = cuteIte PublicL cond left right
  cute Match {..} = cuteMatch PublicL True cond alts
  cute OIte {..} = cuteIte OblivL cond left right
  cute e@Prod {..} = cuteInfix e (accentOfOLabel olabel <> "*") left right
  cute Psi {..} = cute $ psiName oadtName
  cute Pair {..} = cutePair pairKind left right
  cute PMatch {..} = cutePMatch pairKind cond lBinder rBinder bnd2
  cute e@OSum {..} = cuteInfix e (oblivName "+") left right
  cute OInj {..} = do
    cuteApp_
      (pretty (oblivName $ if tag then "inl" else "inr"))
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
  cute OMatch {..} = do
    condDoc <- cute cond
    (xl, lBody) <- unbind1NameOrBinder lBinder lBnd
    (xr, rBody) <- unbind1NameOrBinder rBinder rBnd
    lBodyDoc <- cute lBody
    rBodyDoc <- cute rBody
    return $
      cuteMatchDoc OblivL True condDoc $
        cuteAltDocs
          [ (oblivName "inl", [xl], lBodyDoc),
            (oblivName "inr", [xr], rBodyDoc)
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
  cute TV = "'a"
  cute Arb {..} = case oblivTy of
    Just ty -> do
      tyDoc <- cute ty
      return $ parens $ arbDoc <> tyDoc
    _ -> return arbDoc
    where
      arbDoc = pretty (oblivAccent <> oblivAccent)
  cute Ppx {..} = cute ppx

-- | Pretty printer for preprocessors
instance Cute (Ppx Text) where
  cute = \case
    ItePpx {..} -> go "if" [condTy, retTy]
    CtorPpx {..} -> go ctor [retTy]
    MatchPpx {..} -> go "match" [condTy, retTy]
    BuiltinPpx {..} -> go fn [retTy]
    CoercePpx {..} -> go "coerce" [fromTy, toTy]
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
      "fn" <> leakyDoc
        <+> go (cuteBinder name (Just ty))
        <+> equals <> go (cuteLam True expr)
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
    -- Do not distinguish infix further.
    App {fn = GV {..}} | isInfix ref -> 20
    App {} -> 10
    Psi {} -> 0
    TUnit -> 0
    VUnit -> 0
    TBool {} -> 0
    BLit {} -> 0
    TInt {} -> 0
    ILit {} -> 0
    Prod {} -> 20
    Pair {} -> 0
    OSum {} -> 20
    OInj {} -> 10
    Asc {} -> 0
    Loc {..} -> plevel expr
    Arb {} -> 0
    Ppx {} -> 0
    _ -> 90

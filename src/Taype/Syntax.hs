{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
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
    Typ,
    Label,
    AppKind (..),
    Binder (..),
    Def (..),
    NamedDef (..),
    Attribute (..),
    LabelPolyStrategy (..),

    -- * Helper functions
    abstract1Binder,
    instantiate1Binder,

    -- * Smart constructors
    lam,
  )
where

import Bound
import Control.Monad
import Data.Deriving
import Data.Functor.Classes
import Prettyprinter
import Taype.Error
import Taype.Fresh
import qualified Text.Show

-- | Taype expression, including the surface and the core syntax
data Expr a
  = -- | Local variable
    V {name :: a}
  | -- | Global variable
    GV {ref :: Text}
  | -- | Dependent function type
    Pi
      { typ :: Typ a,
        label :: Maybe Label,
        body :: Scope () Typ a
      }
  | -- | Lambda abstraction
    Lam
      { maybeType :: Maybe (Typ a),
        label :: Maybe Label,
        body :: Scope () Expr a
      }
  | -- | Application, including function application, type application, etc
    App
      { appKind :: Maybe AppKind,
        fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { maybeType :: Maybe (Typ a),
        label :: Maybe Label,
        rhs :: Expr a,
        body :: Scope () Expr a
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
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | (Dependent) case analysis.
    --  Do not support empty type, i.e. 'alts' must be non empty
    Case
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        alts :: NonEmpty (Name, Scope Int Expr a)
      }
  | -- | Oblivious and leaky if conditional
    OIte
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Product type
    Prod {left :: Typ a, right :: Typ a}
  | -- | Normal pair
    Pair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for product
    PCase
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        body2 :: Scope Bool Expr a
      }
  | -- | Oblivious product type
    OProd {left :: Typ a, right :: Typ a}
  | -- | Oblivious pair
    OPair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for oblivious product
    OPCase
      { cond :: Expr a,
        body2 :: Scope Bool Expr a
      }
  | -- | Oblivious sum type
    OSum {left :: Typ a, right :: Typ a}
  | -- | Oblivious injection
    OInj
      { maybeType :: Maybe (Typ a),
        tag :: Bool,
        inj :: Expr a
      }
  | -- | (Leaky) case analysis for oblivious sum type
    OCase
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        lBody :: Scope () Expr a,
        rBody :: Scope () Expr a
      }
  | -- | Oblivious conditional, i.e. multiplexer
    Mux
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Ascription. Do not appear in core taype
    Asc {typ :: Typ a, expr :: Expr a}
  | -- | Label promotion. Do not appear in surface taype
    Promote {expr :: Expr a}
  | -- | Tape, the key operation in taype
    Tape {expr :: Expr a}
  | -- | Add location information
    Loc {loc :: Int, expr :: Expr a}
  deriving stock (Functor, Foldable, Traversable)

-- | A type in taype is also an expression
type Typ = Expr

-- | A leakage label is just a Boolean
type Label = Bool

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | TypeApp
  deriving stock (Eq, Show)

-- | A binder is either anonymous, i.e. \"_\", or a name
data Binder = Anon | Named Text
  deriving stock (Eq, Show)

-- | Global definition
data Def a
  = -- Function
    FunDef {attr :: Attribute, typ :: Typ a, label :: Maybe Label, expr :: Expr a}
  | -- | Algebraic data type. Do not support empty type
    ADTDef {ctors :: NonEmpty Text}
  | -- | Oblivious algebraic data type. Only support one argument for now
    OADTDef {typ :: Typ a, body :: Scope () Expr a}
  | -- | Constructor
    CtorDef {paraTypes :: [Typ a], dataType :: Text}
  | -- | Builtin operation
    BuiltinDef {paraTypes :: [Typ a], resType :: Typ a, strategy :: LabelPolyStrategy}
  deriving stock (Functor, Foldable, Traversable)

data NamedDef a = NamedDef {name :: Text, loc :: Int, def :: Def a}

data Attribute = SectionAttr | RetractionAttr | SafeAttr | LeakyAttr
  deriving stock (Eq, Show)

data LabelPolyStrategy = JoinStrategy | TopStrategy
  deriving stock (Eq, Show)

instance Applicative Expr where
  pure = V
  (<*>) = ap

instance Monad Expr where
  V {..} >>= f = f name
  GV {..} >>= _ = GV {..}
  Pi {..} >>= f = Pi {typ = typ >>= f, body = body >>>= f, ..}
  Lam {..} >>= f = Lam {maybeType = (>>= f) <$> maybeType, body = body >>>= f, ..}
  App {..} >>= f = App {fn = fn >>= f, args = (>>= f) <$> args, ..}
  Let {..} >>= f =
    Let
      { maybeType = (>>= f) <$> maybeType,
        rhs = rhs >>= f,
        body = body >>>= f,
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
      { maybeType = (>>= f) <$> maybeType,
        cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f
      }
  Case {..} >>= f =
    Case
      { maybeType = (>>= f) <$> maybeType,
        cond = cond >>= f,
        alts = second (>>>= f) <$> alts,
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
      { maybeType = (>>= f) <$> maybeType,
        cond = cond >>= f,
        body2 = body2 >>>= f,
        ..
      }
  OProd {..} >>= f = OProd {left = left >>= f, right = right >>= f, ..}
  OPair {..} >>= f = OPair {left = left >>= f, right = right >>= f, ..}
  OPCase {..} >>= f =
    OPCase
      { cond = cond >>= f,
        body2 = body2 >>>= f,
        ..
      }
  OSum {..} >>= f = OSum {left = left >>= f, right = right >>= f, ..}
  OInj {..} >>= f = OInj {maybeType = (>>= f) <$> maybeType, inj = inj >>= f, ..}
  OCase {..} >>= f =
    OCase
      { maybeType = (>>= f) <$> maybeType,
        cond = cond >>= f,
        lBody = lBody >>>= f,
        rBody = rBody >>>= f,
        ..
      }
  Mux {..} >>= f =
    Mux
      { cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f,
        ..
      }
  Asc {..} >>= f = Asc {typ = typ >>= f, expr = expr >>= f, ..}
  Promote {..} >>= f = Promote {expr = expr >>= f, ..}
  Tape {..} >>= f = Tape {expr = expr >>= f, ..}
  Loc {..} >>= f = Loc {expr = expr >>= f, ..}

deriveEq1 ''Expr
deriveShow1 ''Expr

instance Eq a => Eq (Expr a) where (==) = eq1

instance Show a => Show (Expr a) where showsPrec = showsPrec1

deriving stock instance Eq a => Eq (Def a)

deriving stock instance Show a => Show (Def a)

deriving stock instance Eq a => Eq (NamedDef a)

deriving stock instance Show a => Show (NamedDef a)

abstract1Binder :: (Monad f) => Binder -> f Text -> Scope () f Text
abstract1Binder Anon = abstract $ const Nothing
abstract1Binder (Named name) = abstract1 name

instantiate1Binder :: (Monad f) => Binder -> Scope n f Text -> f Text
instantiate1Binder Anon = instantiate1 (oops "Instantiating an anonymous binder")
instantiate1Binder (Named name) = instantiate1 (return name)

-- | A smart constructor for 'Lam'
lam :: Eq a => a -> Maybe (Typ a) -> Maybe Label -> Expr a -> Expr a
lam x maybeType label b = Lam {body = abstract1 x b, ..}

-- | Pretty printer for Taype expressions
instance Pretty (Expr Text) where
  pretty = runFresh . prettyExpr

prettyExpr :: Expr Text -> Fresh (Doc ann)
prettyExpr V {..} = return $ pretty name
prettyExpr Lam {..} = do
  x <- freshName
  return $ "\\" <+> pretty x <+> "->" <+> pretty (instantiate1 (V x) body)
prettyExpr App {..} = return $ pretty fn <+> hsep (pretty <$> args)
prettyExpr _ = return "<not implemented>"

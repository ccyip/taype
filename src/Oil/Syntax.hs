{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Syntax of OIL (OADT Intermediate Language for taype).
module Oil.Syntax
  ( -- * Syntax
    Expr (..),
    Binding (..),
    Ty (..),
    sizeTy,
    Def (..),

    -- * Array operations
    arrNew,
    arrConcat,
    arrSlice,
    arrMux,
  )
where

import Bound
import Control.Monad
import Taype.Binder
import Taype.Common
import Taype.Name
import Taype.Plate

----------------------------------------------------------------
-- Syntax

-- | OIL expression
--
-- We try to keep the syntax minimal.
data Expr a
  = -- | Local variable
    V {name :: a}
  | -- | Global variable
    GV {ref :: Text}
  | -- | Integer literal
    ILit {iLit :: Int}
  | -- | Lambda abstraction
    Lam
      { binder :: Maybe Binder,
        bnd :: Scope () Expr a
      }
  | -- | Application
    App
      { appKind :: AppKind,
        fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { bindings :: NonEmpty (Binding Expr a),
        bndMany :: Scope Int Expr a
      }
  | -- | Case analysis
    Case
      { cond :: Expr a,
        alts :: NonEmpty (CaseAlt Expr a)
      }
  deriving stock (Functor, Foldable, Traversable)

data Binding f a = Binding
  { binder :: Maybe Binder,
    bnd :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

data Ty a
  = -- | Local type variable
    TV {name :: a}
  | -- | Global type variable
    TGV {ref :: Text}
  | -- | Integer type
    TInt
  | -- | Oblivious array
    OArray
  | -- | Function type
    Arrow {dom :: Ty a, cod :: Ty a}
  | -- | Type application
    TApp {tctor :: Text, args :: [Ty a]}
  deriving stock (Functor, Foldable, Traversable)

-- | The type of data size
--
-- We reuse the integer type for size type for convenience, and ignore the
-- issues of overflow, potential negative values, etc.
sizeTy :: Ty a
sizeTy = TInt

-- | Global definition
data Def b a
  = -- | Function
    FunDef
      { binders :: [Maybe Binder],
        ty :: Scope Int Ty b,
        expr :: Expr a
      }
  | -- | Algebraic data type
    ADTDef
      { binders :: [Maybe Binder],
        ctors :: NonEmpty (Text, [Scope Int Ty b])
      }
  deriving stock (Functor, Foldable, Traversable)

----------------------------------------------------------------
-- Array operations
--
-- We simply define array operations as global names.

-- | Array creation with arbitrary values
arrNew :: Text
arrNew = "@new"

-- | Array concatenation
arrConcat :: Text
arrConcat = "@concat"

-- | Array slicing
arrSlice :: Text
arrSlice = "@slice"

-- | Multiplexer
--
-- Unlike the multiplexer expressions in taype, this also takes an extra
-- argument for the size of the oblivious array.
arrMux :: Text
arrMux = "@mux"

----------------------------------------------------------------
-- Instances of expressions and definitions

instance Applicative Expr where
  pure = V
  (<*>) = ap

instance Monad Expr where
  V {..} >>= f = f name
  GV {..} >>= _ = GV {..}
  ILit {..} >>= _ = ILit {..}
  Lam {..} >>= f = Lam {bnd = bnd >>>= f, ..}
  App {..} >>= f = App {fn = fn >>= f, args = args <&> (>>= f), ..}
  Let {..} >>= f =
    Let
      { bndMany = bndMany >>>= f,
        bindings = bindings <&> (>>>= f),
        ..
      }
  Case {..} >>= f = Case {cond = cond >>= f, alts = alts <&> (>>>= f)}

instance PlateM (Expr Name) where
  plateM f Lam {..} = do
    (x, body) <- unbind1 bnd
    body' <- f body
    return Lam {bnd = abstract_ x body', ..}
  plateM f App {..} = do
    fn' <- f fn
    args' <- mapM f args
    return App {fn = fn', args = args', ..}
  plateM f Let {..} = do
    (xs, body) <- unbindMany (length bindings) bndMany
    bindings' <- mapM (go xs) bindings
    body' <- f body
    return Let {bindings = bindings', bndMany = abstract_ xs body'}
    where
      go xs Binding {..} = do
        rhs <- f $ instantiateName xs bnd
        return Binding {bnd = abstract_ xs rhs, ..}
  plateM f Case {..} = do
    cond' <- f cond
    alts' <- mapM (biplateM f) alts
    return Case {cond = cond', alts = alts'}
  plateM _ e = return e

instance Bound Binding where
  Binding {..} >>>= f = Binding {bnd = bnd >>>= f, ..}

instance Applicative Ty where
  pure = TV
  (<*>) = ap

instance Monad Ty where
  TV {..} >>= f = f name
  TGV {..} >>= _ = TGV {..}
  TInt >>= _ = TInt
  OArray >>= _ = OArray
  Arrow {..} >>= f = Arrow {dom = dom >>= f, cod = cod >>= f}
  TApp {..} >>= f = TApp {args = args <&> (>>= f), ..}

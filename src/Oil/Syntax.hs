{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

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
    NamedDef,
    Defs,

    -- * Smart constructors
    Apply (..),
    adtDef_,
    funDef_,
    ar_,
    lam_,
    lams_,
    case_,

    -- * Array operations
    aName,
    aNew,
    aConcat,
    aSlice,
    aMux,

    -- * Pretty printer
    cuteDefs,
  )
where

import Bound
import Control.Monad (ap)
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Name
import qualified Taype.NonEmpty as NE
import Taype.Plate
import Taype.Prelude
import Prelude hiding (group)

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
        tyBnd :: Scope Int Ty b,
        expr :: Expr a
      }
  | -- | Algebraic data type
    ADTDef
      { binders :: [Maybe Binder],
        ctors :: NonEmpty (Text, [Scope Int Ty b])
      }
  deriving stock (Functor, Foldable, Traversable)

type NamedDef b a = (Text, Def b a)

type Defs b a = [NamedDef b a]

----------------------------------------------------------------
-- Array operations
--
-- We simply define array operations as global names.

-- | Oblivious array name
aName :: Text
aName = "@"

-- | Array creation with arbitrary values
aNew :: Text
aNew = "@new"

-- | Array concatenation
aConcat :: Text
aConcat = "@concat"

-- | Array slicing
aSlice :: Text
aSlice = "@slice"

-- | Multiplexer
--
-- Unlike the multiplexer expressions in taype, this also takes an extra
-- argument for the size of the oblivious array.
aMux :: Text
aMux = "@mux"

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

instance IsString a => IsString (Expr a) where
  fromString = return . fromString

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

instance IsString a => IsString (Ty a) where
  fromString = return . fromString

-- | A specialized 'Bound' instance
--
-- Similar to '>>>=', but handle both variable classes (one for expressions and
-- one for types). Perhaps we should introduce a 'Bibound' class.
boundDef :: Def b a -> (a -> Expr c) -> (b -> Ty d) -> Def d c
boundDef FunDef {..} f g =
  FunDef
    { tyBnd = tyBnd >>>= g,
      expr = expr >>= f,
      ..
    }
boundDef ADTDef {..} _ g =
  ADTDef
    { ctors = ctors <&> second ((>>>= g) <$>),
      ..
    }

----------------------------------------------------------------
-- Smart constructors

class Apply a b | a -> b where
  (@@) :: b -> [a] -> a

infixl 2 @@

adtDef_ :: Text -> [Binder] -> [(Text, [Ty Text])] -> NamedDef b a
adtDef_ name binders ctors = (name, boundDef def GV close)
  where
    def =
      ADTDef
        { binders = Just <$> binders,
          ctors =
            mustNonEmpty "constructor list" $
              ctors <&> second (abstractBinder binders <$>)
        }
    close "self" = TGV name
    close x = TGV x

funDef_ :: Text -> [Binder] -> Ty Text -> Expr Text -> NamedDef b a
funDef_ name binders ty expr = (name, boundDef def close TGV)
  where
    def =
      FunDef
        { binders = Just <$> binders,
          tyBnd = abstractBinder binders ty,
          ..
        }
    close "self" = GV name
    close x = GV x

ar_ :: [Ty a] -> Ty a
ar_ [] = oops "Arrow without type"
ar_ [t] = t
ar_ (t : ts) = Arrow t $ ar_ ts

lam_ :: a ~ Text => BinderM a -> Expr a -> Expr a
lam_ binder body =
  Lam
    { binder = Just binder,
      bnd = abstractBinder binder body
    }

lams_ :: a ~ Text => [BinderM a] -> Expr a -> Expr a
lams_ = flip $ foldr lam_

instance Apply (Expr a) (Expr a) where
  fn @@ args = App {appKind = FunApp, ..}

instance Apply (Ty a) Text where
  tctor @@ args = TApp {..}

case_ :: a ~ Text => Expr a -> [(Text, [BinderM a], Expr a)] -> Expr a
case_ cond alts =
  Case
    { alts = mustNonEmpty "Alternative list" $ uncurry3 caseAlt_ <$> alts,
      ..
    }

----------------------------------------------------------------
-- Pretty printer

instance Cute (Expr Text) where
  cute V {..} = cute name
  cute GV {..} = cute ref
  cute ILit {..} = cute iLit
  cute e@Lam {} = cuteLam False e
  cute e@App {fn = GV {..}, args = [left, right]}
    | isInfix ref = cuteInfix e ref left right
  cute App {fn = GV "(,)", args = [left, right]} = cutePair "" left right
  cute App {..} = cuteApp fn args
  cute Let {..} = do
    let (binders, bnds) =
          NE.unzip $ bindings <&> \Binding {..} -> (binder, bnd)
    (xs, body) <- unbindManyNamesOrBinders (toList binders) bndMany
    bindingDocs <- zipWithM (cuteBinding xs) xs (toList bnds)
    bodyDoc <- cute body
    return $ cuteLetDoc bindingDocs bodyDoc
    where
      cuteBinding xs x bnd = do
        binderDoc <- cute x
        rhsDoc <- cute $ instantiateName xs bnd
        return (binderDoc, rhsDoc)
  cute
    Case
      { alts =
          CaseAlt {ctor = "False", binders = [], bnd = rBnd}
            :| [CaseAlt {ctor = "True", binders = [], bnd = lBnd}],
        ..
      } = do
      (_, left) <- unbindManyNamesOrBinders [] lBnd
      (_, right) <- unbindManyNamesOrBinders [] rBnd
      cuteIte "" cond left right
  cute Case {alts = CaseAlt {ctor = "(,)", ..} :| [], ..} = do
    (xs, body) <- unbindManyNamesOrBinders binders bnd
    case xs of
      [xl, xr] -> cutePCase_ "" cond xl xr body
      _ -> oops "Binder number does not match"
  cute Case {..} = cuteCase "" True cond alts

-- | Pretty printer for a type
instance Cute (Ty Text) where
  cute TV {..} = cute name
  cute TGV {..} = cute ref
  cute TInt = "Int"
  cute OArray = cute aName
  cute e@Arrow {..} = do
    domDoc <- cuteSub e dom
    codDoc <- cute cod
    return $ domDoc <+> "->" <> line <> codDoc
  cute t@TApp {args = [left, right], ..}
    | isInfix tctor = cuteInfix t tctor left right
  cute TApp {..} = cuteApp_ (pretty tctor) args

-- | Pretty printer for a definition
instance Cute (NamedDef Text Text) where
  cute (name, def) = case def of
    FunDef {..} -> do
      (xs, ty) <- unbindManyNamesOrBinders binders tyBnd
      tyDoc <- cute ty
      doc <- cuteLam True expr
      return $
        hang $
          "fn" <+> pretty name <> tyVarsDoc xs
            <> sep1_ name (colon <+> align (group tyDoc))
            <+> equals
            <> doc
    ADTDef {..} -> do
      xs <- mapM freshNameOrBinder binders
      ctorDocs <- mapM (cuteCtor xs) ctors
      return $
        hang $
          "data" <+> adtName <> tyVarsDoc xs
            <> sep1
              ( equals
                  <+> sepWith (line <> pipe <> space) ctorDocs
              )
      where
        cuteCtor xs (ctor, paraBnds) = do
          let paraTypes = paraBnds <&> instantiateName xs
          cuteApp_ (pretty ctor) paraTypes
        adtName = if isInfix name then parens $ pretty name else pretty name
    where
      tyVarsDoc [] = ""
      tyVarsDoc xs = softline <> brackets (sep $ pretty <$> xs)

-- | Pretty printer for OIL definitions
cuteDefs :: Options -> Defs Text Text -> Doc
cuteDefs options =
  foldMap $ \def -> runCuteM options (cute def) <> hardline <> hardline

cuteLam :: Bool -> Expr Text -> CuteM Doc
cuteLam isRoot e = do
  (binderDocs, bodyDoc) <- go e
  return $ cuteLamDoc isRoot binderDocs bodyDoc
  where
    go Lam {..} = do
      (x, body) <- unbind1NameOrBinder binder bnd
      binderDoc <- cute x
      (binderDocs, bodyDoc) <- go body
      return (binderDoc : binderDocs, bodyDoc)
    go expr = ([],) <$> cute expr

instance HasPLevel (Expr a) where
  plevel = \case
    V {} -> 0
    GV {} -> 0
    ILit {} -> 0
    App {fn = GV {..}} | isInfix ref -> 20
    App {} -> 10
    _ -> 90

instance HasPLevel (Ty a) where
  plevel = \case
    TV {} -> 0
    TGV {} -> 0
    TInt {} -> 0
    OArray {} -> 0
    TApp {..} | isInfix tctor -> 20
    TApp {} -> 10
    _ -> 90

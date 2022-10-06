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
    Ty (..),
    sizeTy,
    Def (..),
    NamedDef,
    Defs,
    closedDef,
    Program (..),

    -- * Smart constructors
    Apply (..),
    adtDef_,
    funDef_,
    ar_,
    lam_,
    lams_,
    let_,
    lets_,
    case_,
    ite_,
    tGV,
    lam',
    lams',
    let',
    lets',
    case',

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
      { fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { binder :: Maybe Binder,
        rhs :: Expr a,
        bnd :: Scope () Expr a
      }
  | -- | Case analysis
    Case
      { cond :: Expr a,
        alts :: [CaseAlt Expr a]
      }
  deriving stock (Functor, Foldable, Traversable)

data Ty a
  = -- | Local type variable
    TV {name :: a}
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
        ctors :: [(Text, [Scope Int Ty b])]
      }
  deriving stock (Functor, Foldable, Traversable)

type NamedDef b a = (Text, Def b a)

type Defs b a = [NamedDef b a]

-- | OIL program
data Program b a = Program
  { preludeDefs :: Defs b a,
    mainDefs :: Defs b a,
    concealDefs :: Defs b a,
    revealDefs :: Defs b a
  }

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
  App {..} >>= f = App {fn = fn >>= f, args = args <&> (>>= f)}
  Let {..} >>= f =
    Let
      { rhs = rhs >>= f,
        bnd = bnd >>>= f,
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
    return App {fn = fn', args = args'}
  plateM f Let {..} = do
    rhs' <- f rhs
    (x, body) <- unbind1 bnd
    body' <- f body
    return Let {rhs = rhs', bnd = abstract_ x body', ..}
  plateM f Case {..} = do
    cond' <- f cond
    alts' <- mapM (biplateM f) alts
    return Case {cond = cond', alts = alts'}
  plateM _ e = return e

instance IsString a => IsString (Expr a) where
  fromString = return . fromString

instance Applicative Ty where
  pure = TV
  (<*>) = ap

instance Monad Ty where
  TV {..} >>= f = f name
  TInt >>= _ = TInt
  OArray >>= _ = OArray
  Arrow {..} >>= f = Arrow {dom = dom >>= f, cod = cod >>= f}
  TApp {..} >>= f = TApp {args = args <&> (>>= f), ..}

instance IsString a => IsString (Ty a) where
  fromString = return . fromString

instance PlateM (Ty Name) where
  plateM f Arrow {..} = do
    dom' <- f dom
    cod' <- f cod
    return Arrow {dom = dom', cod = cod'}
  plateM f TApp {..} = do
    args' <- mapM f args
    return TApp {args = args', ..}
  plateM _ t = return t

instance BiplateM (Def b Name) (Expr Name) where
  biplateM f FunDef {..} = do
    expr' <- f expr
    return FunDef {expr = expr', ..}
  biplateM _ def = return def

-- | A specialized 'Bound' instance
--
-- Similar to '>>>=', but handle both variable classes (one for expressions and
-- one for types). Perhaps we should introduce a @Bibound@ class.
boundDef :: (a -> Expr c) -> (b -> Ty d) -> Def b a -> Def d c
boundDef f g FunDef {..} =
  FunDef
    { tyBnd = tyBnd >>>= g,
      expr = expr >>= f,
      ..
    }
boundDef _ g ADTDef {..} =
  ADTDef
    { ctors = ctors <&> second ((>>>= g) <$>),
      ..
    }

-- | Make sure a definition is closed, i.e. there is no free variable.
--
-- This is similar to 'fromClosed', but don't bother defining a 'Bitraversable'
-- instance and a @biclosed@ function corresponding to 'closed' in the bound
-- library.
closedDef :: Def b a -> Def d c
closedDef = boundDef go go
  where
    go = oops "Definition is not closed"

----------------------------------------------------------------
-- Smart constructors

class Apply a b | a -> b where
  (@@) :: b -> [a] -> a

infixl 2 @@

adtDef_ :: Text -> [Binder] -> [(Text, [Ty Text])] -> NamedDef b a
adtDef_ name binders ctors = (name, boundDef GV close def)
  where
    def =
      ADTDef
        { binders = Just <$> binders,
          ctors = ctors <&> second (abstractBinder binders <$>)
        }
    close "$self" = tGV name
    close x = tGV x

funDef_ :: Text -> [Binder] -> Ty Text -> Expr Text -> NamedDef b a
funDef_ name binders ty expr = (name, boundDef close tGV def)
  where
    def =
      FunDef
        { binders = Just <$> binders,
          tyBnd = abstractBinder binders ty,
          ..
        }
    close "$self" = GV name
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

let_ :: a ~ Text => BinderM a -> Expr a -> Expr a -> Expr a
let_ binder rhs body =
  Let
    { binder = Just binder,
      bnd = abstractBinder binder body,
      ..
    }

lets_ :: a ~ Text => [(BinderM a, Expr a)] -> Expr a -> Expr a
lets_ = flip $ foldr $ uncurry let_

instance Apply (Expr a) (Expr a) where
  fn @@ args = App {..}

case_ :: a ~ Text => Expr a -> [(Text, [BinderM a], Expr a)] -> Expr a
case_ cond alts =
  Case
    { alts = uncurry3 caseAlt_ <$> alts,
      ..
    }

-- Do not reuse 'case_' to avoid the constraint on @a@.
ite_ :: Eq a => Expr a -> Expr a -> Expr a -> Expr a
ite_ cond left right =
  Case
    { alts =
        [ CaseAlt {ctor = "False", binders = [], bnd = abstract_ [] right},
          CaseAlt {ctor = "True", binders = [], bnd = abstract_ [] left}
        ],
      ..
    }

-- | Global type, i.e. type constructor without argument
tGV :: Text -> Ty a
tGV tctor = TApp {args = [], ..}

instance Apply (Ty a) Text where
  tctor @@ args = TApp {..}

----------------------------------------------------------------
-- Smart constructors that work with 'Name's

lam' :: Name -> Maybe Binder -> Expr Name -> Expr Name
lam' x binder body =
  Lam
    { bnd = abstract_ x body,
      ..
    }

lams' :: [(Name, Maybe Binder)] -> Expr Name -> Expr Name
lams' = flip $ foldr $ uncurry lam'

let' :: Name -> Maybe Binder -> Expr Name -> Expr Name -> Expr Name
let' x binder rhs body =
  Let {bnd = abstract_ x body, ..}

lets' :: [(Name, Maybe Binder, Expr Name)] -> Expr Name -> Expr Name
lets' = flip $ foldr $ uncurry3 let'

case' :: Expr Name -> [(Text, [(Name, Maybe Binder)], Expr Name)] -> Expr Name
case' cond alts = Case {alts = go <$> alts, ..}
  where
    go (ctor, namedBinders, body) =
      let (xs, binders) = unzip namedBinders
       in CaseAlt {bnd = abstract_ xs body, ..}

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
  cute e@Let {} = do
    (bindingDocs, bodyDoc) <- go e
    return $ cuteLetDoc bindingDocs bodyDoc
    where
      go Let {..} = do
        (x, body) <- unbind1NameOrBinder binder bnd
        binderDoc <- cute x
        rhsDoc <- cute rhs
        (bindingDocs, bodyDoc) <- go body
        return ((binderDoc, rhsDoc) : bindingDocs, bodyDoc)
      go expr = ([],) <$> cute expr
  cute
    Case
      { alts =
          [ CaseAlt {ctor = "False", binders = [], bnd = rBnd},
            CaseAlt {ctor = "True", binders = [], bnd = lBnd}
            ],
        ..
      } = do
      (_, left) <- unbindManyNamesOrBinders [] lBnd
      (_, right) <- unbindManyNamesOrBinders [] rBnd
      cuteIte "" cond left right
  cute Case {alts = [CaseAlt {ctor = "(,)", ..}], ..} = do
    (xs, body) <- unbindManyNamesOrBinders binders bnd
    case xs of
      [xl, xr] -> cutePCase_ "" cond xl xr body
      _ -> oops "Binder number does not match"
  cute Case {..} = cuteCase "" True cond alts

-- | Pretty printer for a type
instance Cute (Ty Text) where
  cute TV {..} = cute name
  cute TInt = "int"
  cute OArray = cute aName
  cute e@Arrow {..} = do
    domDoc <- cuteSub e dom
    codDoc <- cute cod
    return $ group domDoc <+> "->" <> line <> codDoc
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
          "fn"
            <+> pretty name
              <> tyVarsDoc xs
              <> sep1_ name (colon <+> align (group tyDoc))
            <+> equals
              <> doc
    ADTDef {..} -> do
      xs <- mapM freshNameOrBinder binders
      ctorDocs <- mapM (cuteCtor xs) ctors
      return $
        hang $
          "data"
            <+> adtName
              <> tyVarsDoc xs
              <> sep1 (equals <+> sepWith (line <> pipe <> space) ctorDocs)
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
  foldMap $ \def -> runCuteM options (cute def) <> hardline2

cuteLam :: Bool -> Expr Text -> CuteM Doc
cuteLam isRoot e = do
  (binderDocs, bodyDoc) <- go e
  return $ cuteLamDoc isRoot binderDocs bodyDoc
  where
    go Lam {..} = do
      (x, body) <- unbind1NameOrBinder binder bnd
      (binderDocs, bodyDoc) <- go body
      return (pretty x : binderDocs, bodyDoc)
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
    TInt {} -> 0
    OArray {} -> 0
    TApp {..} | tctor `elem` leakyInfixes -> 19
    TApp {..} | isInfix tctor -> 20
    TApp {args = []} -> 0
    TApp {} -> 10
    _ -> 90

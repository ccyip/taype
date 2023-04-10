{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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
    Def,
    DefB (..),
    NamedDef,
    Defs,
    Program (..),

    -- * Smart constructors
    Apply (..),
    arrows_,
    ite_,
    prod_,
    pair_,
    tGV,
    lamB,
    lamsB,
    letB,
    letsB,
    matchB,
    lam',
    lams',
    let',
    lets',

    -- * Array operations
    aName,
    aNew,
    aConcat,
    aSlice,
    aMux,

    -- * Pretty printer
    cuteProgramDoc,
  )
where

import Bound
import Control.Monad (ap)
import Data.Functor.Classes
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
  | -- | ADT pattern matching
    Match
      { cond :: Expr a,
        alts :: [MatchAlt Expr a]
      }
  deriving stock (Functor, Foldable, Traversable)

data Ty
  = -- | Integer type
    TInt
  | -- | Oblivious array
    OArray
  | -- | Function type
    Arrow {dom :: Ty, cod :: Ty}
  | -- | Type application
    --
    -- This includes types with no argument, such as ADTs.
    TApp {tctor :: Text, args :: [Ty]}
  deriving stock (Eq)

-- | The type of data size
--
-- We reuse the integer type for size type for convenience, and ignore the
-- issues of overflow, potential negative values, etc.
sizeTy :: Ty
sizeTy = TInt

-- | Global definition
type Def = DefB Expr

-- | Generalized global definition
data DefB f a
  = -- | Function
    FunDef
      { ty :: Ty,
        expr :: f a
      }
  | -- | Algebraic data type
    ADTDef
      { ctors :: [(Text, [Ty])]
      }
  deriving stock (Functor, Foldable, Traversable)

type NamedDef a = (Text, Def a)

type Defs a = [NamedDef a]

-- | OIL program
data Program = Program
  { mainDefs :: forall a. Defs a,
    concealDefs :: forall a. Defs a,
    revealDefs :: forall a. Defs a
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
  Match {..} >>= f = Match {cond = cond >>= f, alts = alts <&> (>>>= f)}

instance Eq1 Expr where
  liftEq eq V {name} V {name = name'} = eq name name'
  liftEq _ GV {ref} GV {ref = ref'} = ref == ref'
  liftEq _ ILit {iLit} ILit {iLit = iLit'} = iLit == iLit'
  liftEq eq Lam {bnd} Lam {bnd = bnd'} = liftEq eq bnd bnd'
  liftEq eq App {fn, args} App {fn = fn', args = args'} =
    liftEq eq fn fn' && liftEq (liftEq eq) args args'
  liftEq eq Let {rhs, bnd} Let {rhs = rhs', bnd = bnd'} =
    liftEq eq rhs rhs' && liftEq eq bnd bnd'
  liftEq eq Match {cond, alts} Match {cond = cond', alts = alts'} =
    liftEq eq cond cond' && liftEq (liftEq eq) alts alts'
  liftEq _ _ _ = False

instance (Eq a) => Eq (Expr a) where (==) = eq1

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
  plateM f Match {..} = do
    cond' <- f cond
    alts' <- mapM (biplateM f) alts
    return Match {cond = cond', alts = alts'}
  plateM _ e = return e

instance PlateM Ty where
  plateM f Arrow {..} = do
    dom' <- f dom
    cod' <- f cod
    return Arrow {dom = dom', cod = cod'}
  plateM f TApp {..} = do
    args' <- mapM f args
    return TApp {args = args', ..}
  plateM _ t = return t

instance BiplateM (Def Name) (Expr Name) where
  biplateM f FunDef {..} = do
    expr' <- f expr
    return FunDef {expr = expr', ..}
  biplateM _ def = return def

instance BiplateM (Defs Name) (Expr Name) where
  biplateM f = mapM $ secondM $ biplateM f

----------------------------------------------------------------
-- Smart constructors

class Apply a b | a -> b where
  (@@) :: b -> [a] -> a

infixl 2 @@

instance Apply (Expr a) (Expr a) where
  fn @@ args = App {..}

instance Apply Ty Text where
  tctor @@ args = TApp {..}

arrows_ :: [Ty] -> Ty
arrows_ [] = oops "Arrow without type"
arrows_ [t] = t
arrows_ (t : ts) = Arrow t $ arrows_ ts

ite_ :: (Eq a) => Expr a -> Expr a -> Expr a -> Expr a
ite_ cond left right =
  Match
    { alts =
        [ MatchAlt {ctor = "False", binders = [], bnd = abstract_ [] right},
          MatchAlt {ctor = "True", binders = [], bnd = abstract_ [] left}
        ],
      ..
    }

prod_ :: Ty -> Ty -> Ty
prod_ a b = "*" @@ [a, b]

pair_ :: Expr a -> Expr a -> Expr a
pair_ a b = GV "(,)" @@ [a, b]

-- | Global type, i.e. type constructor without argument
tGV :: Text -> Ty
tGV tctor = TApp {args = [], ..}

----------------------------------------------------------------
-- Smart constructors that work with 'Name's

lamB :: Name -> Maybe Binder -> Expr Name -> Expr Name
lamB x binder body =
  Lam
    { bnd = abstract_ x body,
      ..
    }

lamsB :: [(Name, Maybe Binder)] -> Expr Name -> Expr Name
lamsB = flip $ foldr $ uncurry lamB

letB :: Name -> Maybe Binder -> Expr Name -> Expr Name -> Expr Name
letB x binder rhs body =
  Let {bnd = abstract_ x body, ..}

letsB :: [(Name, Maybe Binder, Expr Name)] -> Expr Name -> Expr Name
letsB = flip $ foldr $ uncurry3 letB

matchB :: Expr Name -> [(Text, [(Name, Maybe Binder)], Expr Name)] -> Expr Name
matchB cond alts = Match {alts = go <$> alts, ..}
  where
    go (ctor, namedBinders, body) =
      let (xs, binders) = unzip namedBinders
       in MatchAlt {bnd = abstract_ xs body, ..}

lam' :: Name -> Expr Name -> Expr Name
lam' x = lamB x Nothing

lams' :: [Name] -> Expr Name -> Expr Name
lams' = flip $ foldr lam'

let' :: Name -> Expr Name -> Expr Name -> Expr Name
let' x = letB x Nothing

lets' :: [(Name, Expr Name)] -> Expr Name -> Expr Name
lets' = flip $ foldr $ uncurry let'

----------------------------------------------------------------
-- Pretty printer

instance Cute (Expr Text) where
  cute V {..} = cute name
  cute GV {..} = cute ref
  cute ILit {..} = cute iLit
  cute e@Lam {} = cuteLam False e
  cute e@App {fn = GV {..}, args = [left, right]}
    | isInfix ref = cuteInfix e ref left right
  cute App {fn = GV "(,)", args = [left, right]} = cutePair PublicP left right
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
    Match
      { alts =
          [ MatchAlt {ctor = "False", binders = [], bnd = rBnd},
            MatchAlt {ctor = "True", binders = [], bnd = lBnd}
            ],
        ..
      } = do
      (_, left) <- unbindManyNamesOrBinders [] lBnd
      (_, right) <- unbindManyNamesOrBinders [] rBnd
      cuteIte PublicL cond left right
  cute Match {alts = [MatchAlt {ctor = "(,)", ..}], ..} = do
    (xs, body) <- unbindManyNamesOrBinders binders bnd
    case xs of
      [xl, xr] -> cutePMatch_ PublicP cond xl xr body
      _ -> oops "Binder number does not match"
  cute Match {..} = cuteMatch PublicL True cond alts

-- | Pretty printer for a type
instance Cute Ty where
  cute TInt = "int"
  cute OArray = cute aName
  cute e@Arrow {..} = do
    domDoc <- cuteSub e dom
    codDoc <- cute cod
    return $ group domDoc <+> "->" <> line <> codDoc
  cute t@TApp {args = left : right : _, ..}
    | isInfix tctor = cuteInfix t tctor left right
  cute TApp {..} = cuteApp_ (pretty tctor) args

-- | Pretty printer for a definition
cuteDefDoc :: Options -> Text -> Def Text -> Doc
cuteDefDoc options name = \case
  FunDef {..} ->
    hang $
      "fn"
        <+> pretty name
          <> sep1_ name (colon <+> align (group $ go (cute ty)))
        <+> equals
          <> go (cuteLam True expr)
  ADTDef {..} ->
    hang $
      "data"
        <+> adtName
          <> sep1
            (equals <+> sepWith (line <> pipe <> space) (cuteCtor <$> ctors))
  where
    cuteCtor (ctor, paraTypes) = go $ cuteApp_ (pretty ctor) paraTypes
    adtName = if isInfix name then parens $ pretty name else pretty name
    go = runCuteM options

-- | Pretty printer for OIL definitions
cuteDefsDoc :: Options -> Defs Text -> Doc
cuteDefsDoc options = foldMap go
  where
    go (name, def) = cuteDefDoc options name def <> hardline2

-- | Pretty printer for an OIL program
cuteProgramDoc :: Options -> Program -> Doc
cuteProgramDoc options Program {..} =
  go "Computation phase" mainDefs
    <> go "Conceal phase" concealDefs
    <> go "Reveal phase" revealDefs
  where
    go comment defs =
      pretty commentDelim <+> comment <> hardline2 <> cuteDefsDoc options defs

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

instance HasPLevel Ty where
  plevel = \case
    TInt {} -> 0
    OArray {} -> 0
    TApp {..} | isInfix tctor -> 20
    TApp {args = []} -> 0
    TApp {} -> 10
    _ -> 90

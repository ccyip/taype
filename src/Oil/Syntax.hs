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
    Attribute (..),
    Flags (..),
    emptyFlags,
    Program (..),
    OADTInfo (..),

    -- * Smart constructors
    Apply (..),
    ite_,
    prod_,
    arrows_,
    sum_,
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
    match',
    fst',

    -- * Array operations
    aName,
    aNew,
    aConcat,
    aSlice,
    aMux,

    -- * Pretty printer
    cuteProgramDoc,

    -- * Dependency graph
    DepGraph (..),
    mkDepGraph,
    reachableSet,

    -- * Optimizer monad
    Env (..),
    OptM,
  )
where

import Bound
import Control.Monad (ap)
import Data.Functor.Classes
import Data.Graph (Graph, Vertex, graphFromEdges, reachable)
import Data.Maybe (fromJust)
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
  | -- | Type variable
    --
    -- General type polymorphism is not supported. This type variable must be
    -- unique in a definition.
    TV
  deriving stock (Show, Eq)

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
      { attr :: Attribute,
        flags :: Flags,
        ty :: Ty,
        expr :: f a
      }
  | -- | Algebraic data type
    ADTDef
      { ctors :: [(Text, [Ty])]
      }
  deriving stock (Functor, Foldable, Traversable)

type NamedDef a = (Text, Def a)

type Defs a = [NamedDef a]

data Attribute
  = SectionAttr
  | LeakyAttr
  | OADTAttr Ty
  | ReshapeAttr
  | NoAttr
  deriving stock (Show, Eq)

data Flags = Flags
  { inlineFlag :: Bool,
    simplifierFlag :: Maybe (Expr Name -> OptM (Expr Name))
  }

emptyFlags :: Flags
emptyFlags =
  Flags
    { inlineFlag = False,
      simplifierFlag = Nothing
    }

-- | OIL program
data Program = Program
  { mainDefs :: forall a. Defs a,
    concealDefs :: forall a. Defs a,
    revealDefs :: forall a. Defs a,
    oadts :: [OADTInfo]
  }

data OADTInfo = OADTInfo
  { oadtName :: Text,
    section :: Text,
    retraction :: Text,
    embelView :: Maybe Text
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

ite_ :: (Eq a) => Expr a -> Expr a -> Expr a -> Expr a
ite_ cond left right =
  Match
    { alts =
        [ MatchAlt {ctor = "false", binders = [], bnd = abstract_ [] right},
          MatchAlt {ctor = "true", binders = [], bnd = abstract_ [] left}
        ],
      ..
    }

prod_ :: Ty -> Ty -> Ty
prod_ a b = "*" @@ [a, b]

arrows_ :: [Ty] -> Ty -> Ty
arrows_ = flip $ foldr Arrow

sum_ :: Ty -> Ty -> Ty
sum_ a b = "+" @@ [a, b]

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

match' :: Expr Name -> [(Text, [Name], Expr Name)] -> Expr Name
match' cond alts = Match {alts = go <$> alts, ..}
  where
    go (ctor, xs, body) =
      MatchAlt
        { bnd = abstract_ xs body,
          binders = replicate (length xs) Nothing,
          ..
        }

fst' :: Expr Name
fst' = runFreshM $ do
  x <- fresh
  xl <- fresh
  xr <- fresh
  return $ lam' x $ match' (V x) [("(,)", [xl, xr], V xl)]

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
  cute Let {..} = do
    (x, body) <- unbind1NameOrBinder binder bnd
    binderDoc <- cute x
    rhsDoc <- cute rhs
    bodyDoc <- cute body
    return $ cuteLetDoc binderDoc rhsDoc bodyDoc
  cute
    Match
      { alts =
          [ MatchAlt {ctor = "false", binders = [], bnd = rBnd},
            MatchAlt {ctor = "true", binders = [], bnd = lBnd}
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
  cute TV = "'a"

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
      pretty commentDelim <+> comment <//> cuteDefsDoc options defs

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
    TV -> 0
    TApp {..} | isInfix tctor -> 20
    TApp {args = []} -> 0
    TApp {} -> 10
    _ -> 90

----------------------------------------------------------------
-- Dependency graph

data DepGraph = DepGraph
  { graph :: Graph,
    fromVertex :: Vertex -> (NamedDef Name, Text, [Text]),
    toVertex :: Text -> Maybe Vertex
  }

mkDepGraph :: Defs Name -> DepGraph
mkDepGraph defs =
  let depss = runFreshM $ mapM (go . snd) defs
      edges = zipWith (\def deps -> (def, fst def, deps)) defs depss
      (graph, fromVertex, toVertex) = graphFromEdges edges
   in DepGraph {..}
  where
    go :: Def Name -> FreshM [Text]
    go FunDef {..} = do
      deps <- universeM expr
      return $ hashNub [x | GV x <- deps]
    go _ = return []

reachableSet :: DepGraph -> Text -> HashSet Text
reachableSet DepGraph {..} =
  fromList . toNames . reachable graph . fromJust . toVertex
  where
    toNames vs = [name | (_, name, _) <- fromVertex <$> vs]

----------------------------------------------------------------
-- Optimizer monad

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Local definition (binding) context
    --
    -- All expressions are in ANF and simplified (deep or shallow). If the
    -- expression is a global variable, it must be in application form (with
    -- empty arguments).
    dctx :: [(Name, Expr Name)],
    -- | Whether to recursively simplify under binders
    deepSimp :: Bool,
    simplifier :: Expr Name -> OptM (Expr Name)
  }

type OptM = FreshT (ReaderT Env IO)

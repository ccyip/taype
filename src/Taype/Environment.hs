{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Environments and contexts.
module Taype.Environment
  ( -- * Environment
    Env (..),
    initEnv,

    -- * Contexts
    GCtx (..),
    defsFromGCtx,
    fromClosedDefs,
    TCtx (..),
    BCtx (..),

    -- * Manipulating environment
    mapGCtxDef,
    mapMGCtxDef,
    lookupGCtx,
    insertGCtx,
    lookupGSig,
    lookupGDef,
    lookupTy,
    lookupBinder,
    extendCtx,
    extendCtx1,
    withLabel,
    withLoc,
    mayWithLoc,
    withCur,
    withOption,
    withOptPrintLabels,

    -- * Prelude context
    preludeGCtx,

    -- * Pretty printer
    cuteDefs,
  )
where

import Data.HashMap.Strict ((!?))
import qualified Data.HashMap.Strict as M
import Data.List (lookup)
import qualified GHC.Exts as E
import Relude.Extra.Bifunctor
import Relude.Extra.Tuple
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Taype.Syntax

----------------------------------------------------------------
-- Environment

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Global signature context
    --
    -- We reuse the same 'GCtx' data as in 'gdctx', but only use the signature
    -- part.
    gsctx :: GCtx Name,
    -- | Global definition context
    --
    -- We reuse the same 'GCtx' data as in 'gsctx', but only use the definition
    -- part.
    gdctx :: GCtx Name,
    -- | Local typing context
    tctx :: TCtx Name,
    -- | Binder context, used for pretty printing
    bctx :: BCtx Name,
    -- | Current expression for error reporting
    cur :: Expr Name,
    -- | Location of the current expression for error reporting
    loc :: Int,
    -- | Default label for inference
    label :: Label
  }

instance HasOptions Env where
  getOptions Env {..} = options

-- | Make an initial environment.
--
-- Some fields are intantiated arbitrarily, because they will be replaced later.
initEnv :: Options -> GCtx Name -> GCtx Name -> Env
initEnv options gsctx gdctx =
  Env
    { tctx = TCtx [],
      bctx = BCtx [],
      loc = -1,
      cur = V 0,
      label = LeakyL,
      ..
    }

----------------------------------------------------------------
-- Contexts

newtype GCtx a = GCtx {unGCtx :: HashMap Text (Def a)}
  deriving stock (Functor, Foldable, Traversable)
  deriving newtype (Semigroup, Monoid)

instance IsList (GCtx a) where
  type Item (GCtx a) = NamedDef a
  fromList = GCtx . fromList
  toList = E.toList . unGCtx

-- | Build a list of named definitions from the context.
defsFromGCtx :: GCtx a -> [Text] -> Defs a
defsFromGCtx (GCtx gctx) = fmapToSnd go
  where
    go name = fromMaybe (oops "Definition not in context") (gctx !? name)

fromClosedDefs :: Defs a -> Defs b
fromClosedDefs = secondF fromClosed

newtype TCtx a = TCtx {unTCtx :: [(a, (Ty a, Label))]}
  deriving stock (Functor, Foldable, Traversable)

instance BiplateM (TCtx Name) (Ty Name) where
  biplateM f (TCtx tctx) = TCtx <$> forM tctx (secondM $ firstM f)

newtype BCtx a = BCtx {unBCtx :: [(a, Binder)]}
  deriving stock (Functor, Foldable, Traversable)

----------------------------------------------------------------
-- Manipulating environment

mapGCtxDef :: (Def a -> Def b) -> GCtx a -> GCtx b
mapGCtxDef f (GCtx gctx) = GCtx $ f <$> gctx

mapMGCtxDef :: (Monad m) => (Def a -> m (Def b)) -> GCtx a -> m (GCtx b)
mapMGCtxDef f (GCtx gctx) = GCtx <$> mapM f gctx

-- | Lookup a definition in a given global context.
lookupGCtx :: Text -> GCtx a -> Maybe (Def a)
lookupGCtx x (GCtx gctx) = gctx !? x

-- | Insert a definition into a given global context. If a definition with the
-- same name already exists in the context, it will be replaced.
insertGCtx :: Text -> Def a -> GCtx a -> GCtx a
insertGCtx x def (GCtx gctx) = GCtx $ M.insert x def gctx

-- | Look up a definition in the global typing context.
lookupGSig :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupGSig x = do
  gctx <- asks gsctx
  return $ lookupGCtx x gctx

-- | Look up a definition in the global definition context.
lookupGDef :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupGDef x = do
  gctx <- asks gdctx
  return $ lookupGCtx x gctx

-- | Look up a type and its label in the typing context.
lookupTy :: MonadReader Env m => Name -> m (Maybe (Ty Name, Label))
lookupTy x = do
  TCtx tctx <- asks tctx
  return $ lookup x tctx

-- | Look up the binder of a name.
lookupBinder :: MonadReader Env m => Name -> m (Maybe Binder)
lookupBinder x = do
  BCtx bctx <- asks bctx
  return $ lookup x bctx

-- | Extend the typing context.
--
-- To maintain the invariant, the given types have to be well-kinded and in core
-- taype ANF.
extendCtx ::
  MonadReader Env m => [(Name, Ty Name, Label, Maybe Binder)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {tctx = TCtx tctx, bctx = BCtx bctx, ..} =
      Env
        { tctx = TCtx $ (ctx1 <$> xs) <> tctx,
          bctx = BCtx $ mapMaybe bctx1 xs <> bctx,
          ..
        }
    ctx1 (x, t, l, _) = (x, (t, l))
    bctx1 (x, _, _, mb) = (x,) <$> mb

-- | Extend the typing context with one entry.
extendCtx1 ::
  MonadReader Env m => Name -> Ty Name -> Label -> Maybe Binder -> m a -> m a
extendCtx1 x t l mb = extendCtx [(x, t, l, mb)]

withLabel :: MonadReader Env m => Label -> m a -> m a
withLabel l = local $ \Env {..} -> Env {label = l, ..}

withLoc :: MonadReader Env m => Int -> m a -> m a
withLoc l = local $ \Env {..} -> Env {loc = l, ..}

mayWithLoc :: MonadReader Env m => Maybe Int -> m a -> m a
mayWithLoc (Just l) = withLoc l
mayWithLoc _ = id

withCur :: MonadReader Env m => Expr Name -> m a -> m a
withCur e = local (\Env {..} -> Env {cur = e, ..})

withOption :: MonadReader Env m => (Options -> Options) -> m a -> m a
withOption f = local $ \Env {..} -> Env {options = f options, ..}

withOptPrintLabels :: MonadReader Env m => m a -> m a
withOptPrintLabels = withOption $ \opt -> opt {optPrintLabels = True}

----------------------------------------------------------------
-- Prelude context

-- | The prelude context includes builtin functions.
preludeGCtx :: GCtx a
preludeGCtx =
  GCtx $
    fromList $
      builtin
        <$> [ ("+", [TInt, TInt], TInt, JoinStrategy),
              (oblivName "+", [OInt, OInt], OInt, SafeStrategy),
              ("-", [TInt, TInt], TInt, JoinStrategy),
              (oblivName "-", [OInt, OInt], OInt, SafeStrategy),
              ("*", [TInt, TInt], TInt, JoinStrategy),
              (oblivName "*", [OInt, OInt], OInt, SafeStrategy),
              ("/", [TInt, TInt], TInt, JoinStrategy),
              (oblivName "/", [OInt, OInt], OInt, SafeStrategy),
              ("&&", [TBool, TBool], TBool, JoinStrategy),
              (oblivName "&&", [OBool, OBool], OBool, SafeStrategy),
              ("||", [TBool, TBool], TBool, JoinStrategy),
              (oblivName "||", [OBool, OBool], OBool, SafeStrategy),
              ("not", [TBool], TBool, JoinStrategy),
              (oblivName "not", [OBool], OBool, SafeStrategy),
              ("==", [TInt, TInt], TBool, JoinStrategy),
              (oblivName "==", [OInt, OInt], OBool, SafeStrategy),
              ("<=", [TInt, TInt], TBool, JoinStrategy),
              (oblivName "<=", [OInt, OInt], OBool, SafeStrategy),
              (sectionName "bool", [TBool], OBool, JoinStrategy),
              (retractionName "bool", [OBool], TBool, LeakyStrategy),
              (sectionName "int", [TInt], OInt, JoinStrategy),
              (retractionName "int", [OInt], TInt, LeakyStrategy)
            ]

builtin :: (Text, [Ty a], Ty a, LabelPolyStrategy) -> NamedDef a
builtin (name, paraTypes, resType, strategy) = (name, BuiltinDef {..})

----------------------------------------------------------------
-- Pretty printer

instance Cute (TCtx Text) where
  cute (TCtx tctx) = do
    docs <- mapM go tctx
    return $
      hang $
        "Typing context"
          <> colon
          <> hardline
          <> if null tctx then "<empty>" else sepWith hardline docs
    where
      go (x, (t, l)) = cuteBinder x (Just l) (Just t)

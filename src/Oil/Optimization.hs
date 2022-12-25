{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Optimize OIL programs.
module Oil.Optimization (optimize) where

import qualified Bound.Scope as B
import Data.List (lookup)
import Oil.Syntax
import Taype.Common
import Taype.Name
import Taype.Plate
import Taype.Prelude

-- | Optimize OIL programs.
--
-- All definitions must be closed.
optimize :: Defs Name -> IO (Defs Name)
optimize defs =
  runOptM Env {dctx = [], deepSimp = True, ..} $ biplateM simplify defsANF
  where
    defsANF = runFreshM $ biplateM toANF defs
    gctx = fromList defsANF

-- | Simplifier
--
-- This function only simplifies the root let.
simplify :: Expr Name -> OptM (Expr Name)
simplify = go <=< simplify1
  where
    go Let {..} = do
      rhs' <- ifM (asks deepSimp) (deep rhs) (return rhs)
      -- Common subexpression elimination
      matchCtx rhs' >>= \case
        Just x -> simplify $ instantiateName x bnd
        _ -> do
          (x, body) <- unbind1 bnd
          body' <- extendCtx1 x rhs' $ simplify body
          -- Dead code elimination
          return $
            if x `elem` body'
              then letB x binder rhs' body'
              else body'
    go e = return e
    deep Lam {..} = do
      (x, body) <- unbind1 bnd
      body' <- simplify body
      return $ lamB x binder body'
    deep Case {..} = do
      alts' <- mapM goAlt alts
      return Case {alts = alts', ..}
    deep e = return e
    goAlt CaseAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- simplify body
      return CaseAlt {bnd = abstract_ xs body', ..}

-- | Simplify one let binding.
simplify1 :: Expr Name -> OptM (Expr Name)
simplify1 Let {..} = do
  -- We try dead code elimination first before simplification to avoid
  -- doing unnecessary work.
  if null (B.bindings bnd)
    then simplify1 $ instantiate_ (oops "Instantiating nothing") bnd
    else go rhs
  where
    go e@V {} = go $ e @@ []
    go e@GV {} = go $ e @@ []
    go Let {binder = binderN, rhs = rhsN, bnd = bndN} = do
      (x, bodyN) <- unbind1 bndN
      simplify1 $ letB x binderN rhsN Let {rhs = bodyN, ..}
    go App {fn = V {..}, args = []} = simplify1 $ instantiateName name bnd
    go e@App {fn = V {..}, args = arg : args} =
      lookupCtx name >>= \case
        Just (Lam {bnd = bndN}) -> do
          x <- fresh
          go $ let' x (instantiate_ arg bndN) Let {rhs = V x @@ args, ..}
        Just (App {fn = fnN, args = argsN}) ->
          return Let {rhs = fnN @@ argsN <> (arg : args), ..}
        _ -> fallback e
    go e@Case {cond = V {..}, ..} =
      lookupCtx name >>= \case
        Just (App {fn = GV {..}, ..}) ->
          case find (\CaseAlt {ctor} -> ctor == ref) alts of
            Just CaseAlt {bnd = bndN} ->
              go $ Let {rhs = instantiate_ args bndN, ..}
            _ -> fallback e
        _ -> fallback e
    go e = fallback e
    fallback rhs' = return Let {rhs = rhs', ..}
simplify1 e = return e

-- | Transform a OIL expression to its ANF.
--
-- Unlike the taype ANF, OIL ANF is stricter:
--
--   - The last expression in a let sequence must be local variable.
--
--   - All arguments in an application must be local variables, where in taype
--     ANF they can be global names.
toANF :: MonadFresh m => Expr Name -> m (Expr Name)
toANF = \case
  e@V {} -> return e
  e@GV {} -> go e
  e@ILit {} -> go e
  Lam {..} -> do
    (x, body) <- unbind1 bnd
    body' <- toANF body
    y <- fresh
    return $ let' y (lamB x binder body') (V y)
  App {..} -> do
    fn' <- toANF fn
    args' <- mapM toANF args
    x <- fresh
    xs <- freshes $ length args'
    y <- fresh
    let bindings = (x, fn') : zip xs args' <> [(y, V x @@ V <$> xs)]
    return $ lets' bindings (V y)
  Let {..} -> do
    rhs' <- toANF rhs
    (x, body) <- unbind1 bnd
    body' <- toANF body
    return $ letB x binder rhs' body'
  Case {..} -> do
    cond' <- toANF cond
    x <- fresh
    alts' <- mapM goAlt alts
    y <- fresh
    return $ lets' [(x, cond'), (y, Case {cond = V x, alts = alts'})] (V y)
  where
    go e = do
      x <- fresh
      return $ let' x e (V x)
    goAlt CaseAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- toANF body
      return CaseAlt {bnd = abstract_ xs body', ..}

----------------------------------------------------------------
-- Optimizer monad

data Env = Env
  { -- | Global definition context
    gctx :: HashMap Text (Def Name),
    -- | Local definition (binding) context
    --
    -- All expressions are in ANF and simplified (deep or shallow). If the
    -- expression is a global variable, it must be in application form (with
    -- empty arguments).
    dctx :: [(Name, Expr Name)],
    -- | Whether to recursively simplify under binders
    deepSimp :: Bool
  }

type OptM = FreshT (ReaderT Env IO)

runOptM :: Env -> OptM a -> IO a
runOptM env m = runReaderT (runFreshT m) env

lookupCtx :: MonadReader Env m => Name -> m (Maybe (Expr Name))
lookupCtx x = do
  dctx <- asks dctx
  return $ lookup x dctx

matchCtx :: MonadReader Env m => Expr Name -> m (Maybe Name)
matchCtx e = do
  dctx <- asks dctx
  return $ fst <$> find ((e ==) . snd) dctx

extendCtx1 :: MonadReader Env m => Name -> Expr Name -> m a -> m a
extendCtx1 x e = local go
  where
    go Env {..} = Env {dctx = (x, e) : dctx, ..}

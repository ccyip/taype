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
-- Optimize OIL programs.
module Oil.Optimization (optimize) where

import Bound.Scope qualified as B
import Data.HashMap.Strict ((!?))
import Data.List (lookup)
import Oil.Syntax
import Taype.Common
import Taype.Name
import Taype.Plate
import Taype.Prelude

-- | Optimize OIL programs.
--
-- All definitions must be closed.
optimize :: Options -> Defs Name -> IO (Defs Name)
optimize options@Options {..} defs =
  if optFlagNoSimplify
    then return defs
    else do
      let inlinables = [def | def@(_, FunDef {attr = InlineAttr}) <- defs]
      inlinables' <- runOpt $ biplateM (simplify <=< toANF) inlinables
      let ictx = fromList $ runFreshM $ biplateM stripBinders inlinables'
          go opt (name, def) =
            case lookup name inlinables' of
              Just def' -> return (name, def')
              _ -> (name,) <$> opt def
      runOpt $ mapM (go $ biplateM (simplify <=< inline ictx <=< toANF)) defs
  where
    runOpt = runOptM Env {dctx = [], deepSimp = True, ..}

-- | Simplifier
simplify :: Expr Name -> OptM (Expr Name)
simplify = go <=< simplify1
  where
    go Let {..} = do
      rhs' <- ifM (asks deepSimp) (deep rhs) (return rhs)
      -- Common subexpression elimination
      matchDef rhs' >>= \case
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
    deep Match {..} = do
      alts' <- mapM goAlt alts
      return Match {alts = alts', ..}
    deep e = return e
    goAlt MatchAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- simplify body
      return MatchAlt {bnd = abstract_ xs body', ..}

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
      lookupDef name >>= \case
        Just (Lam {bnd = bndN}) -> do
          x <- fresh
          simplify1 $ let' x (instantiate_ arg bndN) Let {rhs = V x @@ args, ..}
        Just (App {fn = fnN, args = argsN}) ->
          return Let {rhs = fnN @@ argsN <> (arg : args), ..}
        _ -> fallback e
    go e@Match {cond = V {..}, ..} =
      lookupDef name >>= \case
        Just (App {fn = GV {..}, ..}) ->
          case find (\MatchAlt {ctor} -> ctor == ref) alts of
            Just MatchAlt {bnd = bndN} ->
              simplify1 $ Let {rhs = instantiate_ args bndN, ..}
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
toANF :: (MonadFresh m) => Expr Name -> m (Expr Name)
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
  Match {..} -> do
    cond' <- toANF cond
    x <- fresh
    alts' <- mapM goAlt alts
    y <- fresh
    return $ lets' [(x, cond'), (y, Match {cond = V x, alts = alts'})] (V y)
  where
    go e = do
      x <- fresh
      return $ let' x e (V x)
    goAlt MatchAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- toANF body
      return MatchAlt {bnd = abstract_ xs body', ..}

stripBinders :: (MonadFresh m) => Expr Name -> m (Expr Name)
stripBinders = transformM go
  where
    go Lam {..} = return Lam {binder = Nothing, ..}
    go Let {..} = return Let {binder = Nothing, ..}
    go Match {..} = return Match {alts = goAlt <$> alts, ..}
    go e = return e
    goAlt MatchAlt {..} =
      MatchAlt {binders = Nothing <$ binders, ..}

inline :: (MonadFresh m) => HashMap Text (Def Name) -> Expr Name -> m (Expr Name)
inline ctx = transformM go
  where
    go e@GV {..} = case ctx !? ref of
      Just FunDef {..} -> return expr
      _ -> return e
    go e = return e

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
    deepSimp :: Bool
  }

type OptM = FreshT (ReaderT Env IO)

runOptM :: Env -> OptM a -> IO a
runOptM env m = runReaderT (runFreshT m) env

lookupDef :: (MonadReader Env m) => Name -> m (Maybe (Expr Name))
lookupDef x = do
  dctx <- asks dctx
  return $ lookup x dctx

matchDef :: (MonadReader Env m) => Expr Name -> m (Maybe Name)
matchDef e = do
  dctx <- asks dctx
  return $ fst <$> find ((e ==) . snd) dctx

extendCtx :: (MonadReader Env m) => [(Name, Expr Name)] -> m a -> m a
extendCtx bindings = local go
  where
    go Env {..} = Env {dctx = bindings <> dctx, ..}

extendCtx1 :: (MonadReader Env m) => Name -> Expr Name -> m a -> m a
extendCtx1 x e = extendCtx [(x, e)]

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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

import Oil.Syntax
import Taype.Common
import Taype.Name
import Taype.Plate

data Env = Env
  { -- | Global definition context
    gctx :: HashMap Text (Def Name),
    -- | Local definition (binding) context
    dctx :: [(Name, Expr Name)]
  }

type OptM = FreshT (ReaderT Env IO)

runOptM :: Env -> OptM a -> IO a
runOptM env m = runReaderT (runFreshT m) env

-- | Optimize OIL programs.
--
-- All definitions must be closed.
optimize :: Defs Name -> IO (Defs Name)
optimize defs = runOptM Env {dctx = [], ..} $ biplateM simplify defsANF
  where
    defsANF = runFreshM $ biplateM toANF defs
    gctx = fromList defsANF

-- | Simplifier
--
-- This function only simplifies the root let.
simplify :: Expr Name -> OptM (Expr Name)
simplify = return

-- | Transform a OIL expression to its ANF.
--
-- Unlike the taype ANF, OIL ANF is stricter:
--
--   - The last expression in a let sequence must be local variable.
--
--   - All arguments in an application must be local variables, where in taype
--     ANF they can be global names.
--
--   - The right hand side of a let binding is never local or global variables:
--     in this case, they have to be applications on empty arguments.
toANF :: MonadFresh m => Expr Name -> m (Expr Name)
toANF = \case
  e@V {} -> go $ e @@ []
  e@GV {} -> go $ e @@ []
  e@ILit {} -> go e
  Lam {..} -> do
    (x, body) <- unbind1 bnd
    body' <- toANF body
    return $ lamB x binder body'
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
    return $ let' x cond' Case {cond = V x, alts = alts'}
  where
    go e = do
      x <- fresh
      return $ let' x e (V x)
    goAlt CaseAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- toANF body
      return CaseAlt {bnd = abstract_ xs body', ..}

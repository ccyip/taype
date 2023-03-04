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
import Data.HashMap.Strict (union, (!?))
import Data.List (lookup)
import Oil.Syntax
import Taype.Binder
import Taype.Common
import Taype.Name
import Taype.Plate
import Taype.Prelude

-- | Optimize OIL programs.
--
-- All definitions must be closed.
optimize ::
  Options -> HashMap Text Attribute -> Defs Name -> Defs Name -> IO (Defs Name)
optimize options@Options {..} actx deps defs = do
  simplified <-
    if optFlagNoSimplify
      then return defs
      else
        runOptM Env {gctx = mempty, dctx = [], deepSimp = True, ..} $
          biplateM (simplify <=< toANF) defs
  if optFlagNoTupling
    then return simplified
    else foldMapM (go (fromList deps `union` fromList simplified)) simplified
  where
    go gctx (name, def) =
      runOptM Env {dctx = [], deepSimp = False, ..} $
        lookupAttr name >>= \case
          Just (SectionAttr {..}) -> goTuple oblivRef name
          Just (RetractionAttr {..}) -> goTuple oblivRef name
          _ -> return [(name, def)]
    goTuple oblivRef name = do
      let tgtName = internalName $ oblivRef <> "_" <> name
      (tgtDef, _, def) <- tupling oblivRef name tgtName
      return [(tgtName, tgtDef), (name, def)]

-- | Perform tupling on two functions.
--
-- The first argument is the name of the target tupled function. The next two
-- arguments are the names of the two source functions.
--
-- Given source functions 'f' and 'g' of types 'A -> B' and 'A -> C'
-- respectively, this function returns the definition of the tupled function 'h'
-- of type 'A -> B * C', along with the new definitions of 'f' and 'g' as the
-- projections from 'h'. The tupled function 'h' should have property:
--
-- @h x = (f x, g x)@
tupling :: Text -> Text -> Text -> OptM (Def Name, Def Name, Def Name)
tupling f g h = do
  (fTy, fExpr) <- lookupFun f
  (gTy, gExpr) <- lookupFun g
  xf <- fresh
  xg <- fresh
  xl <- fresh
  xr <- fresh
  xp <- fresh
  x <- fresh
  hExpr <-
    optimizeTupled f g h $
      lets'
        [ (xf, fExpr),
          (xg, gExpr),
          (xl, V xf @@ [V x]),
          (xr, V xg @@ [V x]),
          (xp, pair_ (V xl) (V xr))
        ]
        (V xp)

  -- Before removing the extra argument from the projections, we do one final
  -- simplification, although technically we only need to do dead code
  -- elimination.
  hExpr' <- withDeepSimp True (simplify hExpr) >>= fixProj
  return
    ( FunDef
        { binders = [],
          tyBnd = abstract_ [] (tupledType fTy gTy),
          expr = lam' x hExpr'
        },
      FunDef {binders = [], tyBnd = abstract_ [] fTy, expr = projFun True},
      FunDef {binders = [], tyBnd = abstract_ [] gTy, expr = projFun False}
    )
  where
    lookupFun x =
      lookupGDef x >>= \case
        Just (FunDef {binders = [], ..}) -> return (instantiate_ [] tyBnd, expr)
        _ -> oops "Invalid tupling source"
    tupledType (Arrow dom1 cod1) (Arrow dom2 cod2)
      | dom1 == dom2 =
          Arrow {dom = dom1, cod = prod_ cod1 cod2}
    tupledType _ _ = oops "Invalid tupling source types"
    projFun b =
      fromClosed $
        lam_ "x" $
          GV (projName b) @@ [GV h @@ ["x"]]
    fixProj = transformM $ \case
      App {fn = fn@GV {..}, args = _ : args}
        | ref == projName True || ref == projName False ->
            return $ App {..}
      e -> return e

optimizeTupled :: Text -> Text -> Text -> Expr Name -> OptM (Expr Name)
optimizeTupled f g h = go
  where
    go = go1 <=< simplify
    go1 Let {rhs = Lam {bnd = bndN}, ..} = do
      (x, bodyN) <- unbind1 bndN
      bodyN' <- go bodyN
      (bindings, v) <- hoisting x bodyN'
      body' <- extendCtx bindings $ go $ instantiateName v bnd
      return $ lets' bindings body'
    go1 Let {rhs = Case {..}, ..} = do
      let x = fromV cond
      alts' <- mapM (goAlt x) alts
      v <- fresh
      return $ let' v Case {alts = alts', ..} (V v)
      where
        goAlt x CaseAlt {bnd = bndN, ..} = do
          (xs, bodyN) <- unbindMany (length binders) bndN
          bodyN' <-
            extendCtx1 x (GV ctor @@ V <$> xs) $ go Let {rhs = bodyN, ..}
          -- Even if the binders are not used in current case, they may get used
          -- in a follow-up expression which is pushed into the alternatives.
          let binders' =
                binders <&> \case
                  Just Anon -> Nothing
                  b -> b
          return CaseAlt {bnd = abstract_ xs bodyN', binders = binders', ..}
    go1 Let {rhs = App {fn = GV {..}, args = arg : args}, ..}
      | ref == f || ref == g = do
          xh <- fresh
          xf <- fresh
          x <- fresh
          let rhs' =
                lets'
                  [ (xh, GV h @@ [arg]),
                    (xf, GV (projName (ref == f)) @@ [arg, V xh]),
                    (x, V xf @@ args)
                  ]
                  (V x)
          (bindings, v) <- simplify rhs' >>= toBindings
          body' <- extendCtx bindings $ go $ instantiateName v bnd
          return $ lets' bindings body'
    go1 Let {..} = do
      (v, body) <- unbind1 bnd
      body' <- extendCtx1 v rhs $ go body
      return $ letB v binder rhs body'
    go1 e = return e

hoisting :: MonadFresh m => Name -> Expr Name -> m ([(Name, Expr Name)], Name)
hoisting x e = do
  (bindings, y) <- toBindings e
  let (hoisted, remain) = go [x] bindings
  v <- fresh
  return (snoc hoisted (v, lam' x $ lets' remain (V y)), v)
  where
    go _ [] = ([], [])
    go xs ((v, rhs) : bindings) =
      if any (`elem` rhs) xs
        then
          let (hoisted, remain) = go (v : xs) bindings
           in (hoisted, (v, rhs) : remain)
        else
          let (hoisted, remain) = go xs bindings
           in ((v, rhs) : hoisted, remain)

-- | Simplifier
--
-- This function only simplifies the root let.
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
      lookupDef name >>= \case
        Just (Lam {bnd = bndN}) -> do
          x <- fresh
          simplify1 $ let' x (instantiate_ arg bndN) Let {rhs = V x @@ args, ..}
        Just (App {fn = fnN, args = argsN}) ->
          return Let {rhs = fnN @@ argsN <> (arg : args), ..}
        _ -> fallback e
    go e@Case {cond = V {..}, ..} =
      lookupDef name >>= \case
        Just (App {fn = GV {..}, ..}) ->
          case find (\CaseAlt {ctor} -> ctor == ref) alts of
            Just CaseAlt {bnd = bndN} ->
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

fromV :: Expr a -> a
fromV V {..} = name
fromV _ = oops "Not a local variable"

toBindings :: MonadFresh m => Expr Name -> m ([(Name, Expr Name)], Name)
toBindings Let {..} = do
  (x, body) <- unbind1 bnd
  (bindings, y) <- toBindings body
  return ((x, rhs) : bindings, y)
toBindings V {..} = return ([], name)
toBindings _ = oops "Not a valid let list in ANF"

----------------------------------------------------------------
-- Optimizer monad

data Env = Env
  { -- | Commandline options
    options :: Options,
    -- | Global definition context
    gctx :: HashMap Text (Def Name),
    -- | Local definition (binding) context
    --
    -- All expressions are in ANF and simplified (deep or shallow). If the
    -- expression is a global variable, it must be in application form (with
    -- empty arguments).
    dctx :: [(Name, Expr Name)],
    -- | Attribute context
    actx :: HashMap Text Attribute,
    -- | Whether to recursively simplify under binders
    deepSimp :: Bool
  }

type OptM = FreshT (ReaderT Env IO)

runOptM :: Env -> OptM a -> IO a
runOptM env m = runReaderT (runFreshT m) env

lookupDef :: MonadReader Env m => Name -> m (Maybe (Expr Name))
lookupDef x = do
  dctx <- asks dctx
  return $ lookup x dctx

lookupGDef :: MonadReader Env m => Text -> m (Maybe (Def Name))
lookupGDef x = do
  gctx <- asks gctx
  return $ gctx !? x

lookupAttr :: MonadReader Env m => Text -> m (Maybe Attribute)
lookupAttr x = do
  actx <- asks actx
  return $ actx !? x

matchDef :: MonadReader Env m => Expr Name -> m (Maybe Name)
matchDef e = do
  dctx <- asks dctx
  return $ fst <$> find ((e ==) . snd) dctx

extendCtx :: MonadReader Env m => [(Name, Expr Name)] -> m a -> m a
extendCtx bindings = local go
  where
    go Env {..} = Env {dctx = bindings <> dctx, ..}

extendCtx1 :: MonadReader Env m => Name -> Expr Name -> m a -> m a
extendCtx1 x e = extendCtx [(x, e)]

withDeepSimp :: MonadReader Env m => Bool -> m a -> m a
withDeepSimp b = local $ \Env {..} -> Env {deepSimp = b, ..}

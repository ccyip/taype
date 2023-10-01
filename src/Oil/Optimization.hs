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
import Data.HashSet (member)
import Data.List (lookup)
import Data.Text qualified as T
import Oil.Syntax
import Relude.Extra.Foldable1
import Taype.Common
import Taype.Name
import Taype.Plate
import Taype.Prelude

-- | Optimize OIL programs.
--
-- All definitions must be closed.
optimize :: Options -> Defs Name -> IO (Defs Name)
optimize options@Options {..} defs =
  if optFlagNoOptimization
    then return defs
    else do
      let defs1 =
            if optFlagNoMemo
              then defs
              else memo defs
          defs2 =
            if optFlagNoGuardReshape
              then defs1
              else guardReshape defs1
          defs' = defs2
      (inlinables, ictx) <-
        if optFlagNoInline
          then return (mempty, mempty)
          else inlineCtx defs'
      let go opt (name, def) =
            case lookup name inlinables of
              Just def' -> return (name, def')
              _ -> (name,) <$> runOpt opt def
      mapM (go $ simplify_ <=< inline_ ictx <=< toANF) defs'
  where
    runOpt opt def =
      let simplifier = case def of
            FunDef {flags = Flags {simplifierFlag = Just f}} -> f
            _ -> return
       in runOptM
            Env
              { dctx = [],
                deepSimp = True,
                ..
              }
            $ biplateM opt def
    simplify_ = if optFlagNoSimplify then return else simplify
    inline_ ictx = if optFlagNoInline then return else inline ictx
    inlineCtx defs' = do
      let inlinables =
            [ def
              | def@(_, FunDef {flags = Flags {inlineFlag = True}}) <- defs'
            ]
      inlinables' <- mapM (secondM $ runOpt (simplify_ <=< toANF)) inlinables
      let ictx = fromList $ runFreshM $ biplateM stripBinders inlinables'
      return (inlinables', ictx)

-- | Simplifier
simplify :: Expr Name -> OptM (Expr Name)
simplify t = do
  simplifier <- asks simplifier
  simplify1 t >>= simplifier >>= go
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
          simplify1 $ Let {rhs = fnN @@ argsN <> (arg : args), ..}
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

-- | Memoize public views.
memo :: Defs Name -> Defs Name
memo = memoInt . memoADT

-- | Memoize integer public views.
memoInt :: Defs Name -> Defs Name
memoInt = foldMap go
  where
    go (name, FunDef {attr = attr@(OADTAttr TInt), ..}) = runFreshM $ do
      x <- fresh
      y <- fresh
      let name_ = internalName name
          expr' =
            let' y (GV "make_memo" @@ [GV "()"]) $
              lam' x $
                GV "memo" @@ [V y, GV name_, V x]
          def' =
            FunDef {expr = expr', ..}
      return [(name_, FunDef {..}), (name, def')]
    go namedDef = [namedDef]

-- | Memoize ADT public views.
--
-- Only support ADT as public view, but not combination of them (e.g., product
-- of ADTs).
memoADT :: Defs Name -> Defs Name
memoADT defs =
  if null projs
    then defs
    else foldMap go defs <> copiedDefs
  where
    graph = mkDepGraph defs
    (projs, views, viewCtors) =
      let (projL, viewL, ctorL) =
            unzip3
              [ (name, tctor, fst <$> getCtors tctor)
                | (name, FunDef {attr = OADTAttr (TApp {args = [], ..})}) <- defs,
                  tctor /= "bool"
              ]
       in ( fromList projL :: HashSet Text,
            fromList viewL :: HashSet Text,
            foldMap fromList ctorL :: HashSet Text
          )
    -- We keep a copy of the functions whose types contain ADT public views, but do not contain oblivious array.
    isKept t = 0 == keptN t
    keptN OArray = -1 :: Int
    keptN TApp {..} | tctor `member` views = 0
    keptN TApp {..} = minimum1 (1 :| (keptN <$> args))
    keptN Arrow {..} = keptN dom `min` keptN cod
    keptN _ = 1
    kept = [name | (name, FunDef {..}) <- defs, isKept ty]
    keptClos = foldMap (reachableSet graph) kept
    copiedDefs =
      [ def
        | def@(name, _) <- defs,
          name `member` keptClos,
          not (name `member` projs)
      ]
    getCtors name = case lookup name defs of
      Just ADTDef {..} -> ctors
      _ -> oops "Not an ADT"
    go def@(name, FunDef {attr = OADTAttr (TApp {args = [], ..}), ..})
      | tctor /= "bool" =
          let ctors = getCtors tctor
           in [ def,
                genMemoTy tctor ctors,
                genEmbel tctor ctors name,
                genErase tctor ctors,
                genProj tctor name
              ]
                <> genSmartCtors tctor ctors expr
    go (name, FunDef {..}) =
      [ ( rewriteName name,
          FunDef
            { ty = rewriteTy ty,
              expr = rewriteExpr expr,
              ..
            }
        )
      ]
    go def = [def]
    mkSmartCtor x = "mk_" <> x <> "_memo"
    memoTy = tGV . memoName
    embelTy name = prod_ TInt (memoTy name)
    genMemoTy t ctors = (memoName t, ADTDef {ctors = genMemoCtor <$> ctors})
    genMemoCtor (ctor, ts) = (memoName ctor, genCtorArgTs ts)
    unlessView TApp {args = [], ..} _ f | tctor `member` views = f tctor
    unlessView _ t _ = t
    genCtorArgTy t = unlessView t t embelTy
    genCtorArgTs ts = genCtorArgTy <$> ts
    genCtorArg mk x t = unlessView t (V x) $ \name -> GV (mk name) @@ [V x]
    genCtorArgs mk = zipWith (genCtorArg mk)
    genEmbel t ctors f =
      ( embelName t,
        FunDef
          { attr = NoAttr,
            flags = emptyFlags,
            ty = Arrow (tGV t) (embelTy t),
            expr = genEmbelExpr ctors f
          }
      )
    genEmbelExpr ctors f = runFreshM $ do
      x <- fresh
      e <- genEmbelMemoExpr x ctors
      return $ lam' x $ pair_ (GV f @@ [V x]) e
    genEmbelMemoExpr x ctors =
      let genAlt (ctor, ts) = do
            xs <- freshes $ length ts
            let args = genCtorArgs embelName xs ts
            return (ctor, xs, GV (memoName ctor) @@ args)
       in do
            alts <- mapM genAlt ctors
            return $ match' (V x) alts
    genErase t ctors =
      ( eraseName t,
        FunDef
          { attr = NoAttr,
            flags = emptyFlags,
            ty = Arrow (embelTy t) (tGV t),
            expr = genEraseExpr ctors
          }
      )
    genEraseExpr ctors = runFreshM $ do
      x <- fresh
      xl <- fresh
      xr <- fresh
      e <- genEraseMemoExpr xr ctors
      return $ lam' x $ match' (V x) [("(,)", [xl, xr], e)]
    genEraseMemoExpr x ctors =
      let genAlt (ctor, ts) = do
            xs <- freshes $ length ts
            let args = genCtorArgs eraseName xs ts
            return (memoName ctor, xs, GV ctor @@ args)
       in do
            alts <- mapM genAlt ctors
            return $ match' (V x) alts
    genProj t f =
      ( memoName f,
        FunDef
          { attr = OADTAttr (embelTy t),
            flags = emptyFlags {inlineFlag = True},
            ty = Arrow (embelTy t) TInt,
            expr = fst'
          }
      )
    genSmartCtors t ctors e = genSmartCtor t e <$> ctors
    genSmartCtor t e (ctor, ts) =
      ( mkSmartCtor ctor,
        FunDef
          { attr = NoAttr,
            flags =
              emptyFlags
                { inlineFlag = True,
                  simplifierFlag = Just rewriteSmartCtor
                },
            ty = arrows_ (genCtorArgTs ts) (embelTy t),
            expr = genSmartCtorExpr e ctor ts
          }
      )
    genSmartCtorExpr e ctor ts = runFreshM $ do
      xs <- freshes $ length ts
      let args = genCtorArgs eraseName xs ts
      return $
        lams' xs $
          pair_ (e @@ [GV ctor @@ args]) (GV (memoName ctor) @@ (V <$> xs))

    rewriteName x | x `member` keptClos = memoName x
    rewriteName x | x `member` viewCtors = mkSmartCtor x
    rewriteName x = x
    rewriteTy = (runFreshM .) $ transformM $ \case
      TApp {..} | tctor `member` views -> return $ embelTy tctor
      t -> return t
    rewriteExpr = (runFreshM .) $ transformM $ \case
      GV {..} -> return GV {ref = rewriteName ref}
      Match {alts = alts@(MatchAlt {ctor = ctor'} : _), ..}
        | ctor' `member` viewCtors -> do
            xl <- fresh
            xr <- fresh
            let rewriteAlt MatchAlt {..} = MatchAlt {ctor = memoName ctor, ..}
            return $
              match'
                cond
                [ ( "(,)",
                    [xl, xr],
                    Match {cond = V xr, alts = rewriteAlt <$> alts}
                  )
                ]
      t -> return t

    rewriteSmartCtor :: Expr Name -> OptM (Expr Name)
    rewriteSmartCtor e@Let {rhs = App {fn = GV pName, args = [V y]}, ..}
      | pName `member` projs =
          lookupDef y >>= \case
            Just App {fn = GV eName, args = [V a]} | isEraseName eName -> do
              Options {optFlagNoInline} <- asks options
              let f = if optFlagNoInline then GV (memoName pName) else fst'
              x <- fresh
              simplify1 $ let' x f Let {rhs = V x @@ [V a], ..}
            _ -> return e
    rewriteSmartCtor e = return e
    isEraseName name =
      case T.stripPrefix erasePrefix name of
        Just t | t `member` views -> True
        _ -> False

-- | Guard reshape instances.
--
-- Do nothing if reshaping between the same public views. Unfortunately,
-- equality checks are not necessarily cheap.
guardReshape :: Defs Name -> Defs Name
guardReshape defs = foldMap go defs
  where
    graph = mkDepGraph defs
    reshapes =
      [ (name, reachableSet graph name)
        | (name, FunDef {attr = ReshapeAttr}) <- defs
      ]
    go (name, def) = runFreshM $ do
      let reshapeNames = [x | (x, s) <- reshapes, name `member` s]
      def' <- flip transformBiM def $ \case
        GV {..} | ref `elem` reshapeNames -> return GV {ref = mkName_ ref}
        e -> return (e :: Expr Name)
      case def' of
        FunDef {attr = ReshapeAttr, ..} -> do
          k1 <- fresh
          k2 <- fresh
          x <- fresh
          let name_ = mkName_ name
              expr' =
                lams' [k1, k2, x] $
                  ite_
                    (GV "=" @@ [V k1, V k2])
                    (V x)
                    (GV name_ @@ [V k1, V k2, V x])
              newDef = FunDef {attr = ReshapeAttr, expr = expr', ..}
          return [(name_, FunDef {attr = ReshapeAttr, ..}), (name, newDef)]
        _ -> return [(name, def')]
    mkName_ x = x <> "_"

----------------------------------------------------------------
-- Optimizer monad

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

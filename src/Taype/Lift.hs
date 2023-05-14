{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Lifting algorithm that derives oblivious programs from the public ones.
module Taype.Lift (liftDefs) where

import Control.Monad.Error.Class
import Control.Monad.RWS
import Data.List (lookup)
import Data.Maybe (fromJust)
import Relude.Extra.Bifunctor (secondF)
import Taype.Common
import Taype.Cute
import Taype.Environment (GCtx, lookupGCtx)
import Taype.Error
import Taype.Name
import Taype.NonEmpty qualified as NE
import Taype.Plate
import Taype.Prelude
import Taype.Syntax
import Taype.TypeChecker
import Prelude hiding (Constraint, group)

----------------------------------------------------------------
-- Environment for the lifting algorithm

data Constraint a
  = EqC {lhs :: Int, rhs :: Ty a}
  | CompatibleC {idx :: Int, cls :: Ty a}
  | IteC {cond :: Int, ret :: Int}
  | CtorC {ctor :: Text, ret :: Int, args :: [Int]}
  | MatchC {cond :: Int, ret :: Int, argss :: [[Int]]}
  | BuiltinC {fn :: Text, ty :: Int}
  | CoerceC {from :: Int, to :: Int}
  | LiftC {fn :: Text, ty :: Int}
  deriving stock (Functor, Foldable, Traversable)

type Constraints a = [Constraint a]

type CCtx a = [(a, (Ty a, Int))]

data Env = Env
  { options :: Options,
    gctx :: GCtx Name,
    defName :: Text,
    defLoc :: Int,
    cctx :: CCtx Name
  }

type LiftM a = FreshT (RWST Env (Constraints Name) Int (ExceptT Err IO)) a

runLiftM :: Env -> LiftM a -> ExceptT Err IO (a, Constraints Name)
runLiftM env m = evalRWST (runFreshT m) env 0

lookupGDef :: (MonadReader Env m) => Text -> m (Def Name)
lookupGDef x = do
  Env {..} <- ask
  return $ fromJust $ lookupGCtx x gctx

lookupCCtx :: (MonadReader Env m) => Name -> m (Ty Name, Int)
lookupCCtx x = do
  Env {..} <- ask
  return $ fromJust $ lookup x cctx

extendCCtx :: (MonadReader Env m) => [(Name, Ty Name, Int)] -> m a -> m a
extendCCtx xs = local go
  where
    go Env {..} = Env {cctx = [(x, (t, a)) | (x, t, a) <- xs] <> cctx, ..}

extendCCtx1 :: (MonadReader Env m) => Name -> Ty Name -> Int -> m a -> m a
extendCCtx1 x t a = extendCCtx [(x, t, a)]

----------------------------------------------------------------
-- Lifting algorithm

-- | Lift an expression to a given type.
--
-- The second argument is the type of the expression, and the third one is the
-- target type, as a type variable index. We can simply add a equality
-- constraint if the target type is known.
--
-- The given expression and types must be in core taype ANF. The return
-- expression contains type variables that will instantiated later, and it
-- should be typed by the target type after instantiation. Note that the return
-- expression may not be in ANF.
liftExpr :: Expr Name -> Ty Name -> Int -> LiftM (Expr Name)
liftExpr e@VUnit t@TUnit idx = do
  tell [EqC idx t]
  return e
liftExpr e@BLit {} t@(TBool PublicL) idx = do
  tell [EqC idx t]
  return e
liftExpr e@ILit {} t@(TInt PublicL) idx = do
  tell [EqC idx t]
  return e
liftExpr e@V {..} _ idx = do
  (_, idx') <- lookupCCtx name
  tell [CoerceC {from = idx', to = idx}]
  return $
    Ppx (CoercePpx {fromTy = TV idx', toTy = TV idx}) @@ [e]
liftExpr Let {..} t idx = do
  let rhsTy' = fromJust rhsTy
  rhsIdx <- freshTV rhsTy'
  rhs' <- liftExpr rhs rhsTy' rhsIdx
  (x, body) <- unbind1 bnd
  body' <- extendCCtx1 x rhsTy' rhsIdx $ liftExpr body t idx
  return Let {rhsTy = Just (TV rhsIdx), rhs = rhs', bnd = abstract_ x body', ..}
liftExpr Lam {..} t idx =
  case isArrow1 t of
    Just (dom, cod) -> do
      domIdx <- freshTV dom
      codIdx <- freshTV cod
      tell [EqC idx (arrow_ (TV domIdx) (TV codIdx))]
      (x, body) <- unbind1 bnd
      body' <- extendCCtx1 x dom domIdx $ liftExpr body cod codIdx
      return Lam {argTy = Just (TV domIdx), bnd = abstract_ x body', ..}
    _ -> err "Lifting dependent lambda abstractions is not supported"
-- Must be a constructor application if the head is a global name.
liftExpr App {fn = GV {..}, ..} _ idx =
  lookupGDef ref >>= \case
    CtorDef {..} -> do
      domIds <- freshTVs paraTypes
      tell [CtorC {ctor = ref, ret = idx, args = domIds}]
      args' <- zipWith3M liftExpr args paraTypes domIds
      return $ Ppx (CtorPpx {ctor = ref, retTy = TV idx}) @@ [tuple_ args']
    _ -> oops "Not a constructor"
liftExpr App {..} _ idx = do
  (fnTy, fnIdx) <- lookupCCtx $ isV fn
  case isArrow fnTy of
    Just (dom, _) -> do
      let doms = take (length args) dom
      domIds <- freshTVs doms
      tell [EqC fnIdx (arrows_ (TV <$> domIds) (TV idx))]
      args' <- zipWith3M liftExpr args doms domIds
      return App {args = args', ..}
    _ -> err "Lifting application of dependent functions is not supported"
liftExpr Pair {..} Prod {olabel = PublicL} idx = do
  (_, leftIdx) <- lookupCCtx $ isV left
  (_, rightIdx) <- lookupCCtx $ isV right
  tell
    [ EqC
        idx
        Prod {olabel = PublicL, left = TV leftIdx, right = TV rightIdx}
    ]
  return Pair {..}
liftExpr PMatch {pairKind = pairKind@PublicP, ..} t idx = do
  (condTy', condIdx) <- lookupCCtx $ isV cond
  let (leftTy, rightTy) = isProd condTy'
  leftIdx <- freshTV leftTy
  rightIdx <- freshTV rightTy
  tell
    [ EqC
        condIdx
        Prod {olabel = PublicL, left = TV leftIdx, right = TV rightIdx}
    ]
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCCtx
      [ (xl, leftTy, leftIdx),
        (xr, rightTy, rightIdx)
      ]
      $ liftExpr body t idx
  return PMatch {bnd2 = abstract_ (xl, xr) body', ..}
liftExpr Ite {..} t idx = do
  (_, condIdx) <- lookupCCtx $ isV cond
  tell [IteC condIdx idx]
  left' <- liftExpr left t idx
  right' <- liftExpr right t idx
  return $
    Ppx (ItePpx {condTy = TV condIdx, retTy = TV idx})
      @@ [cond, thunk_ left', thunk_ right']
liftExpr Match {..} t idx = do
  (condTy, condIdx) <- lookupCCtx $ isV cond
  lookupGDef (isGV condTy) >>= \case
    ADTDef {..} -> do
      let tss = snd <$> ctors
      argss <- mapM freshTVs tss
      tell [MatchC {cond = condIdx, ret = idx, argss = toList argss}]
      alts' <- NE.zipWith3M go alts tss argss
      return $
        Ppx (MatchPpx {condTy = TV condIdx, retTy = TV idx}) @@ toList alts'
    _ -> oops "Not an ADT"
  where
    go MatchAlt {..} ts as = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- extendCCtx (zip3 xs ts as) $ liftExpr body t idx
      lamP (zip3 xs binders (TV <$> as)) body'
liftExpr GV {..} _ idx =
  lookupGDef ref >>= \case
    BuiltinDef {} -> do
      tell [BuiltinC {fn = ref, ty = idx}]
      return $ Ppx (BuiltinPpx {fn = ref, ty = TV idx})
    FunDef {} -> do
      tell [LiftC {fn = ref, ty = idx}]
      return $ Ppx (LiftPpx {fn = ref, ty = TV idx})
    _ -> oops "Refer to a global name that is not a function or builtin"
liftExpr _ _ _ =
  err "Lifting oblivious constructs or preprocessors is not supported"

-- | Generate lifted definitions for the lifting preprocessors.
--
-- This function first generates partial definitions with type variables and
-- type constraints for all functions specified in the lifting preprocessors. It
-- then calls an external program to solve the constraints, and generates the
-- complete definitions by instantiating the type variables inside with the
-- models returned by the solver.
liftDefs :: Options -> GCtx Name -> Defs Name -> ExceptT Err IO (Defs Name)
liftDefs options@Options {..} gctx defs = do
  lifted <- mapM go $ hashNub $ fst <$> lifts
  let liftedDefs = secondF fst lifted
      liftedDefs' =
        fromClosedDefs $
          if optReadable then readableDefs liftedDefs else liftedDefs
      constraints = secondF ((fromClosed <$>) . snd) lifted
      liftedDoc = cuteDefsDoc options liftedDefs'
      constraintsDoc = cuteNamedConstraintsDoc options constraints
  when optPrintLifted $ printDoc options liftedDoc
  writeDocOpt options "lifted.tpc" liftedDoc
  when optPrintConstraints $ printDoc options constraintsDoc
  writeDocOpt options "constraints.sexp" constraintsDoc
  oops "Not implemented yet"
  where
    lifts = collectLifts defs
    go name =
      (name,)
        <$> case lookupGCtx name gctx of
          Just FunDef {..} ->
            runLiftM Env {cctx = [], defName = name, defLoc = loc, ..} $
              do
                x <- freshTV ty
                expr' <- liftExpr expr ty x
                return
                  FunDef
                    { loc = -1,
                      expr = expr',
                      ty = TV x,
                      ..
                    }
          _ -> oops "Not a function"

----------------------------------------------------------------
-- Auxiliaries

freshTV :: Ty Name -> LiftM Int
freshTV cls = do
  n <- get
  put (n + 1)
  tell [CompatibleC {idx = n, ..}]
  return n

freshTVs :: [Ty Name] -> LiftM [Int]
freshTVs = mapM freshTV

isV :: Expr a -> a
isV V {..} = name
isV _ = oops "Not a local variable"

isGV :: Expr a -> Text
isGV GV {..} = ref
isGV _ = oops "Not a global name"

isProd :: Expr a -> (Expr a, Expr a)
isProd Prod {olabel = PublicL, ..} = (left, right)
isProd _ = oops "Not a product"

collectLifts :: Defs Name -> [(Text, Ty Name)]
collectLifts = runFreshM . foldMapM (go . snd)
  where
    go def = do
      es <- universeBiM def
      return $ [(fn, ty) | Ppx {ppx = LiftPpx {..}} <- es]

instance Cute (Constraint Text) where
  cute c = parens . hang <$> go c
    where
      go EqC {..} = do
        rhsDoc <- cuteTy rhs
        return $ sep ["=", aDoc lhs, rhsDoc]
      go CompatibleC {..} = do
        clsDoc <- cuteTy cls
        return $ sep ["compat", aDoc idx, clsDoc]
      go IteC {..} = do
        return $ sep [pretty $ ppxName "if", aDoc cond, aDoc ret]
      go CtorC {..} = do
        return $ sep [pretty $ ppxName ctor, aDoc ret, asDoc args]
      go MatchC {..} = do
        return $
          sep
            [ pretty $ ppxName "match",
              aDoc cond,
              aDoc ret,
              assDoc argss
            ]
      go BuiltinC {..} = do
        return $ sep [pretty $ ppxName fn, aDoc ty]
      go CoerceC {..} = do
        return $ sep [pretty $ ppxName "coerce", aDoc from, aDoc to]
      go LiftC {..} = do
        return $ sep [pretty $ ppxName "lift", pretty fn, aDoc ty]
      aDoc idx = "'a" <> if idx == 0 then "" else pretty idx
      asDoc as = parens $ align $ fillSep $ aDoc <$> as
      assDoc ass = parens $ align $ sep $ asDoc <$> ass
      cuteTy t = do
        doc <- cuteSubAgg t
        return $ group doc

cuteNamedConstraintsDoc :: Options -> [(Text, Constraints Text)] -> Doc
cuteNamedConstraintsDoc options = foldMap ((<> hardline2) . go)
  where
    go (name, cs) =
      parens $
        hang $
          "constraints"
            <+> pretty name
            </> parens (align (csDoc (runCuteM options . cute <$> cs)))
    csDoc [] = mempty
    csDoc (doc : docs) = doc <> foldMap sep1 docs

err :: Doc -> LiftM a
err errMsg = do
  Env {..} <- ask
  throwError
    Err
      { errCategory = "Lifting Error",
        errClass = ErrorC,
        errLoc = defLoc,
        errMsg =
          "Cannot lift function"
            <+> pretty defName
            </> errMsg
      }

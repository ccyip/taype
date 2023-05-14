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
import Prelude hiding (Constraint, group)

----------------------------------------------------------------
-- Environment for the lifting algorithm

data STy = SUnit | SConst Text | SV Int | SProd STy STy | SArrow STy STy
  deriving stock (Eq, Show)

data Constraint
  = EqC {lhs :: Int, rhs :: STy}
  | CompatibleC {idx :: Int, cls :: STy}
  | IteC {cond :: Int, ret :: Int}
  | CtorC {ctor :: Text, ret :: Int, args :: [Int]}
  | MatchC {cond :: Int, ret :: Int, argss :: [[Int]]}
  | BuiltinC {fn :: Text, ty :: Int}
  | CoerceC {from :: Int, to :: Int}
  | LiftC {fn :: Text, ty :: Int}

type Constraints = [Constraint]

type CCtx a = [(a, (Ty a, Int))]

data Env = Env
  { options :: Options,
    gctx :: GCtx Name,
    defName :: Text,
    defLoc :: Int,
    cctx :: CCtx Name
  }

type LiftM a = FreshT (RWST Env Constraints Int (ExceptT Err IO)) a

runLiftM :: Env -> LiftM a -> ExceptT Err IO (a, Constraints)
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
  tell [EqC idx (fromJust (pubTyToSTy t))]
  return e
liftExpr e@BLit {} t@(TBool PublicL) idx = do
  tell [EqC idx (fromJust (pubTyToSTy t))]
  return e
liftExpr e@ILit {} t@(TInt PublicL) idx = do
  tell [EqC idx (fromJust (pubTyToSTy t))]
  return e
liftExpr e@V {..} _ idx = do
  (_, idx') <- lookupCCtx name
  tell [CoerceC {from = idx', to = idx}]
  return $
    Ppx (CoercePpx {fromTy = TV idx', toTy = TV idx}) @@ [e]
liftExpr Let {..} t idx = do
  let rhsTy' = fromJust rhsTy
  rhsIdx <- freshSV rhsTy'
  rhs' <- liftExpr rhs rhsTy' rhsIdx
  (x, body) <- unbind1 bnd
  body' <- extendCCtx1 x rhsTy' rhsIdx $ liftExpr body t idx
  return Let {rhsTy = Just (TV rhsIdx), rhs = rhs', bnd = abstract_ x body', ..}
liftExpr Lam {..} t idx =
  case isArrow1 t of
    Just (dom, cod) -> do
      domIdx <- freshSV dom
      codIdx <- freshSV cod
      tell [EqC idx (SArrow (SV domIdx) (SV codIdx))]
      (x, body) <- unbind1 bnd
      body' <- extendCCtx1 x dom domIdx $ liftExpr body cod codIdx
      return Lam {argTy = Just (TV domIdx), bnd = abstract_ x body', ..}
    _ -> oops "Dependent lambda abstraction"
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
      tell [EqC fnIdx (sarrows_ (SV <$> domIds) (SV idx))]
      args' <- zipWith3M liftExpr args doms domIds
      return App {args = args', ..}
    _ -> oops "Dependent function application"
liftExpr Pair {..} Prod {olabel = PublicL} idx = do
  (_, leftIdx) <- lookupCCtx $ isV left
  (_, rightIdx) <- lookupCCtx $ isV right
  tell [EqC idx (SProd (SV leftIdx) (SV rightIdx))]
  return Pair {..}
liftExpr PMatch {pairKind = pairKind@PublicP, ..} t idx = do
  (condTy', condIdx) <- lookupCCtx $ isV cond
  let (leftTy, rightTy) = isProd condTy'
  leftIdx <- freshSV leftTy
  rightIdx <- freshSV rightTy
  tell [EqC condIdx (SProd (SV leftIdx) (SV rightIdx))]
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
liftExpr _ _ _ = errUnsupported

-- | Generate lifted definitions for the lifting preprocessors.
--
-- This function first generates partial definitions with type variables and
-- type constraints for all functions specified in the lifting preprocessors. It
-- then calls an external program to solve the constraints, and generates the
-- complete definitions by instantiating the type variables inside with the
-- models returned by the solver.
liftDefs :: Options -> GCtx Name -> Defs Name -> ExceptT Err IO (Defs Name)
liftDefs options@Options {..} gctx defs = do
  lifted <- lifting [] $ hashNub $ fst <$> goals
  let liftedDefs = secondF fst lifted
      liftedDefs' =
        fromClosedDefs $
          if optReadable then readableDefs liftedDefs else liftedDefs
      constraints = secondF snd lifted
      liftedDoc = cuteDefsDoc options liftedDefs'
      constraintsDoc = cuteNamedConstraintsDoc options constraints
  when optPrintLifted $ printDoc options liftedDoc
  writeDocOpt options "lifted.tpc" liftedDoc
  when optPrintConstraints $ printDoc options constraintsDoc
  writeDocOpt options "constraints.sexp" constraintsDoc
  oops "Not implemented yet"
  where
    goals = collectLifts $ snd <$> defs
    lifting done [] = return done
    lifting done fs = do
      lifted <- mapM go fs
      let fs' = hashNub $ fst <$> collectLifts [def | (_, (def, _)) <- lifted]
          done' = lifted <> done
      lifting done' [f | f <- fs', isNothing $ lookup f done']
    go name =
      (name,)
        <$> case lookupGCtx name gctx of
          Just FunDef {..} ->
            runLiftM Env {cctx = [], defName = name, defLoc = loc, ..} $
              do
                x <- freshSV ty
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

freshSV :: Ty Name -> LiftM Int
freshSV cls = do
  n <- get
  put (n + 1)
  cls' <- pubTyToSTy' cls
  tell [CompatibleC {idx = n, cls = cls'}]
  return n

freshTVs :: [Ty Name] -> LiftM [Int]
freshTVs = mapM freshSV

isV :: Expr a -> a
isV V {..} = name
isV _ = oops "Not a local variable"

isGV :: Expr a -> Text
isGV GV {..} = ref
isGV _ = oops "Not a global name"

isProd :: Expr a -> (Expr a, Expr a)
isProd Prod {olabel = PublicL, ..} = (left, right)
isProd _ = oops "Not a product"

collectLifts :: [Def Name] -> [(Text, Ty Name)]
collectLifts = runFreshM . foldMapM go
  where
    go def = do
      es <- universeBiM def
      return $ [(fn, ty) | Ppx {ppx = LiftPpx {..}} <- es]

pubTyToSTy :: Ty Name -> Maybe STy
pubTyToSTy TUnit = return SUnit
pubTyToSTy (TBool PublicL) = return $ SConst "bool"
pubTyToSTy (TInt PublicL) = return $ SConst "int"
pubTyToSTy GV {..} = return $ SConst ref
pubTyToSTy Prod {olabel = PublicL, ..} =
  SProd <$> pubTyToSTy left <*> pubTyToSTy right
pubTyToSTy t@Pi {} = do
  (dom, cod) <- isArrow1 t
  SArrow <$> pubTyToSTy dom <*> pubTyToSTy cod
pubTyToSTy _ = Nothing

pubTyToSTy' :: Ty Name -> LiftM STy
pubTyToSTy' t = case pubTyToSTy t of
  Just s -> return s
  _ -> errUnsupported

sarrows_ :: [STy] -> STy -> STy
sarrows_ = flip $ foldr SArrow

idxDoc :: Int -> Doc
idxDoc idx = "a" <> if idx == 0 then "" else pretty idx

instance Cute STy where
  cute SUnit = "unit"
  cute (SConst x) = cute x
  cute (SV idx) = return $ idxDoc idx
  cute t@(SProd l r) = cuteInfix t "*" l r
  cute t@(SArrow dom cod) = do
    domDoc <- cuteSub t dom
    codDoc <- cute cod
    return $ group domDoc <+> "->" <> line <> codDoc

instance HasPLevel STy where
  plevel = \case
    SUnit -> 0
    SConst _ -> 0
    SV _ -> 0
    SProd _ _ -> 20
    SArrow _ _ -> 90

instance Cute Constraint where
  cute c = parens . hang <$> go c
    where
      go EqC {..} = do
        rhsDoc <- cuteTy rhs
        return $ sep ["=", idxDoc lhs, rhsDoc]
      go CompatibleC {..} = do
        clsDoc <- cuteTy cls
        return $ sep ["compat", idxDoc idx, clsDoc]
      go IteC {..} = do
        return $ sep [pretty $ ppxName "if", idxDoc cond, idxDoc ret]
      go CtorC {..} = do
        return $ sep [pretty $ ppxName ctor, idxDoc ret, idsDoc args]
      go MatchC {..} = do
        return $
          sep
            [ pretty $ ppxName "match",
              idxDoc cond,
              idxDoc ret,
              idssDoc argss
            ]
      go BuiltinC {..} = do
        return $ sep [pretty $ ppxName fn, idxDoc ty]
      go CoerceC {..} = do
        return $ sep [pretty $ ppxName "coerce", idxDoc from, idxDoc to]
      go LiftC {..} = do
        return $ sep [pretty $ ppxName "lift", pretty fn, idxDoc ty]
      idsDoc as = parens $ align $ fillSep $ idxDoc <$> as
      idssDoc ass = parens $ align $ sep $ idsDoc <$> ass
      cuteTy t = do
        doc <- cuteSubAgg t
        return $ group doc

cuteNamedConstraintsDoc :: Options -> [(Text, Constraints)] -> Doc
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

errUnsupported :: LiftM a
errUnsupported =
  err "Lifting oblivious constructs or preprocessors is not supported"

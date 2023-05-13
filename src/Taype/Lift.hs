{-# LANGUAGE DerivingStrategies #-}
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
import Taype.Plate
import Taype.Prelude
import Taype.Syntax
import Prelude hiding (Constraint, group)

----------------------------------------------------------------
-- Environment for the lifting algorithm

data Constraint a
  = EqC {lhs :: Ty a, rhs :: Ty a}
  | CompatibleC {idx :: Int, cls :: Ty a}
  | IteC {cond :: Ty a, ret :: Ty a}
  | CtorC {ctor :: Text, ret :: Ty a, as :: [Int]}
  | MatchC {cond :: Ty a, ret :: Ty a, ass :: [[Int]]}
  | BuiltinC {fn :: Text, ty :: Ty a}
  | CoerceC {from :: Ty a, to :: Ty a}
  | LiftC {fn :: Text, ty :: Ty a}
  deriving stock (Functor, Foldable, Traversable)

type Constraints a = [Constraint a]

type CCtx a = [(a, (Ty a, Int))]

data Env = Env
  { options :: Options,
    gctx :: GCtx Name,
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
liftExpr e _ _ = return e

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
  let liftedDefs = secondF (fromClosed . fst) lifted
      constraints = secondF ((fromClosed <$>) . snd) lifted
      liftedDoc = cuteDefsDoc options liftedDefs
      constraintsDoc = cuteNamedConstraintsDoc options constraints
  when optPrintLifted $ printDoc options liftedDoc
  writeDocOpt options "lifted.tpc" liftedDoc
  when optPrintConstraints $ printDoc options constraintsDoc
  writeDocOpt options "constraints.sexp" constraintsDoc
  err "Not implemented yet"
  where
    lifts = collectLifts defs
    go name =
      (name,)
        <$> case lookupGCtx name gctx of
          Just FunDef {..} ->
            runLiftM Env {cctx = [], ..} $
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
        lhsDoc <- cuteTy lhs
        rhsDoc <- cuteTy rhs
        return $ sep ["=", lhsDoc, rhsDoc]
      go CompatibleC {..} = do
        clsDoc <- cuteTy cls
        return $ sep ["compat", aDoc idx, clsDoc]
      go IteC {..} = do
        condDoc <- cuteTy cond
        retDoc <- cuteTy ret
        return $ sep [pretty $ ppxName "if", condDoc, retDoc]
      go CtorC {..} = do
        retDoc <- cuteTy ret
        return $ sep [pretty $ ppxName ctor, retDoc, asDoc as]
      go MatchC {..} = do
        condDoc <- cuteTy cond
        retDoc <- cuteTy ret
        return $ sep [pretty $ ppxName "match", condDoc, retDoc, assDoc ass]
      go BuiltinC {..} = do
        tyDoc <- cuteTy ty
        return $ sep [pretty $ ppxName fn, tyDoc]
      go CoerceC {..} = do
        fromDoc <- cuteTy from
        toDoc <- cuteTy to
        return $ sep [pretty $ ppxName "coerce", fromDoc, toDoc]
      go LiftC {..} = do
        tyDoc <- cuteTy ty
        return $ sep [pretty $ ppxName "lift", pretty fn, tyDoc]
      aDoc idx = "a" <> if idx == 0 then "" else pretty idx
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
            </> parens (fillSep (runCuteM options . cute <$> cs))

err :: (MonadError Err m) => Doc -> m a
err errMsg =
  throwError
    Err
      { errCategory = "Lifting Error",
        errClass = ErrorC,
        errLoc = -1,
        ..
      }

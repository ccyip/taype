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
import Control.Monad.RWS.CPS
import Control.Monad.Writer.CPS
import Data.List (lookup, partition)
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

data STy a
  = SUnit
  | SConst Text
  | SV a
  | SProd (STy a) (STy a)
  | SArrow (STy a) (STy a)
  deriving stock (Eq, Show)

type STy1 = STy Int

type SName = (Int, Name)

type STy2 = STy SName

data Constraint
  = EqC {lhs :: Int, rhs :: STy1}
  | CompatibleC {idx :: Int, cls :: STy1}
  | IteC {cond :: Int, ret :: Int}
  | CtorC {ctor :: Text, ret :: Int, args :: [Int]}
  | MatchC {cond :: Int, ret :: Int, argss :: [[Int]]}
  | BuiltinC {fn :: Text, ty :: Int}
  | CoerceC {from :: Int, to :: Int}
  | LiftC {fn :: Text, ty :: Int}
  deriving stock (Show)

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

data OADTInfo = OADTInfo
  { oadts :: [Text],
    coerces :: [[STy2]],
    joins :: [STy2],
    ctors :: [(Text, [[STy2]])],
    matches :: ([[STy2]], [[STy2]])
  }
  deriving stock (Show)

type OCtx = [(Text, OADTInfo)]

data SConstraint
  = SEqC STy2 STy2
  | SLiftC Text [STy2]
  | SOrC [[SConstraint]]
  deriving stock (Show)

type SConstraints = [SConstraint]

type CompatCtx = [(SName, Text)]

type ACtx = [(Int, STy2)]

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
  tell1 $ EqC idx (fromJust (pubTyToSTy t))
  return e
liftExpr e@BLit {} t@(TBool PublicL) idx = do
  tell1 $ EqC idx (fromJust (pubTyToSTy t))
  return e
liftExpr e@ILit {} t@(TInt PublicL) idx = do
  tell1 $ EqC idx (fromJust (pubTyToSTy t))
  return e
liftExpr e@V {..} _ idx = do
  (_, idx') <- lookupCCtx name
  tell1 $ CoerceC {from = idx', to = idx}
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
      tell1 $ EqC idx (SArrow (SV domIdx) (SV codIdx))
      (x, body) <- unbind1 bnd
      body' <- extendCCtx1 x dom domIdx $ liftExpr body cod codIdx
      return Lam {argTy = Just (TV domIdx), bnd = abstract_ x body', ..}
    _ -> oops "Dependent lambda abstraction"
-- Must be a constructor application if the head is a global name.
liftExpr App {fn = GV {..}, ..} _ idx =
  lookupGDef ref >>= \case
    CtorDef {..} -> do
      domIds <- freshTVs paraTypes
      tell1 $ CtorC {ctor = ref, ret = idx, args = domIds}
      args' <- zipWith3M liftExpr args paraTypes domIds
      return $ Ppx (CtorPpx {ctor = ref, retTy = TV idx}) @@ [tuple_ args']
    _ -> oops "Not a constructor"
liftExpr App {..} _ idx = do
  (fnTy, fnIdx) <- lookupCCtx $ isV fn
  case isArrow fnTy of
    Just (dom, _) -> do
      let doms = take (length args) dom
      domIds <- freshTVs doms
      tell1 $ EqC fnIdx (sarrows_ (SV <$> domIds) (SV idx))
      args' <- zipWith3M liftExpr args doms domIds
      return App {args = args', ..}
    _ -> oops "Dependent function application"
liftExpr Pair {..} Prod {olabel = PublicL} idx = do
  (_, leftIdx) <- lookupCCtx $ isV left
  (_, rightIdx) <- lookupCCtx $ isV right
  tell1 $ EqC idx (SProd (SV leftIdx) (SV rightIdx))
  return Pair {..}
liftExpr PMatch {pairKind = pairKind@PublicP, ..} t idx = do
  (condTy', condIdx) <- lookupCCtx $ isV cond
  let (leftTy, rightTy) = isProd condTy'
  leftIdx <- freshSV leftTy
  rightIdx <- freshSV rightTy
  tell1 $ EqC condIdx (SProd (SV leftIdx) (SV rightIdx))
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
  tell1 $ IteC condIdx idx
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
      tell1 $ MatchC {cond = condIdx, ret = idx, argss = toList argss}
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
      tell1 $ BuiltinC {fn = ref, ty = idx}
      return $ Ppx (BuiltinPpx {fn = ref, ty = TV idx})
    FunDef {} -> do
      tell1 $ LiftC {fn = ref, ty = idx}
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
  let octx = buildOCtx defs
      scs = [(name, reduceConstraints gctx octx cs) | (name, cs) <- constraints]
  print scs
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

reduceConstraints ::
  GCtx Name -> OCtx -> Constraints -> (ACtx, CompatCtx, SConstraints)
reduceConstraints gctx octx cs = (actx, cctx, foldMap go cs')
  where
    (compatCs, cs') = partition isCompatC cs
    (actx, cctx) = reduceCompatC [(idx, t) | CompatibleC idx t <- compatCs]
    lookupACtx idx = fromJust $ lookup idx actx
    lookupOCtx x = fromJust $ lookup x octx
    compatCls x = fromJust $ lookup x cctx

    isCompatC (CompatibleC _ _) = True
    isCompatC _ = False

    subst (SV x) = lookupACtx x
    subst (SProd l r) = SProd (subst l) (subst r)
    subst (SArrow d c) = SArrow (subst d) (subst c)
    subst SUnit = SUnit
    subst (SConst x) = SConst x

    go CoerceC {..} =
      let gen t1 t2 =
            case (t1, t2) of
              (SProd l1 r1, SProd l2 r2) -> gen l1 l2 <> gen r1 r2
              (SArrow d1 c1, SArrow d2 c2) -> gen d2 d1 <> gen c1 c2
              (SV x1, SV x2) ->
                let OADTInfo {..} = lookupOCtx $ compatCls x1
                 in [ SOrC $
                        [SEqC (SV x1) (SV x2)]
                          : belongto [SV x1, SV x2] coerces
                    ]
              _ -> []
       in gen (lookupACtx from) (lookupACtx to)
    go IteC {..} =
      let gen t t' =
            [ SOrC
                [ [SEqC t (SConst "bool")],
                  [SEqC t (SConst $ oblivName "bool")] <> mergeable t'
                ]
            ]
       in gen (lookupACtx cond) (lookupACtx ret)
    go CtorC {..} =
      let ret' = lookupACtx ret
          args' = foldMap (decompose . lookupACtx) args
          OADTInfo {..} = lookupOCtx $ compatCls $ isSV ret'
       in [SOrC $ belongto (ret' : args') $ fromJust $ lookup ctor ctors]
    go MatchC {..} =
      let ret' = lookupACtx ret
          cond' = lookupACtx cond
          args' = foldMap (foldMap $ decompose . lookupACtx) argss
          OADTInfo {..} = lookupOCtx $ compatCls $ isSV cond'
       in [ SOrC
              [ [SOrC $ belongto (cond' : args') $ fst matches],
                [SOrC $ belongto (cond' : args') $ snd matches]
                  <> mergeable ret'
              ]
          ]
    go BuiltinC {..} =
      let tss =
            [ decompose $ tyToSTy $ arrows_ paraTypes resType
              | Just (BuiltinDef {..}) <-
                  flip lookupGCtx gctx <$> [fn, oblivName fn]
            ]
       in [SOrC $ belongto (decompose (lookupACtx ty)) tss]
    go EqC {..} =
      let lhss = decompose $ lookupACtx lhs
          rhss = decompose $ subst rhs
       in zipWith SEqC lhss rhss
    go LiftC {..} = [SLiftC fn $ decompose $ lookupACtx ty]
    go CompatibleC {} = oops "Found compatible constraint"

    mergeable (SProd l r) = mergeable l <> mergeable r
    mergeable (SArrow _ c) = mergeable c
    mergeable (SV x) =
      let OADTInfo {..} = lookupOCtx $ compatCls x
       in [SOrC $ one . SEqC (SV x) <$> joins]
    mergeable _ = []

reduceCompatC :: [(Int, STy1)] -> (ACtx, CompatCtx)
reduceCompatC cs = runWriter $ mapM go cs
  where
    go (idx, t) =
      let gen = \case
            SProd l r -> SProd <$> gen l <*> gen r
            SArrow dom cod -> SArrow <$> gen dom <*> gen cod
            SUnit -> return SUnit
            SConst cls -> do
              x <- (idx,) <$> fresh
              tell [(x, cls)]
              return $ SV x
            SV _ -> oops "Found a variable"
       in (idx,) <$> runFreshT (gen t)

belongto :: [STy2] -> [[STy2]] -> [[SConstraint]]
belongto ts tss = tss <&> zipWith SEqC ts

----------------------------------------------------------------
-- Auxiliaries

freshSV :: Ty Name -> LiftM Int
freshSV cls = do
  n <- get
  put (n + 1)
  cls' <- pubTyToSTy' cls
  tell1 $ CompatibleC {idx = n, cls = cls'}
  return n

freshTVs :: [Ty Name] -> LiftM [Int]
freshTVs = mapM freshSV

isV :: Expr a -> a
isV V {..} = name
isV _ = oops "Not a local variable"

isGV :: Expr a -> Text
isGV GV {..} = ref
isGV _ = oops "Not a global name"

isSV :: STy a -> a
isSV (SV x) = x
isSV _ = oops "Not a variable"

isProd :: Expr a -> (Expr a, Expr a)
isProd Prod {olabel = PublicL, ..} = (left, right)
isProd _ = oops "Not a product"

collectLifts :: [Def Name] -> [(Text, Ty Name)]
collectLifts = runFreshM . foldMapM go
  where
    go def = do
      es <- universeBiM def
      return $ [(fn, ty) | Ppx {ppx = LiftPpx {..}} <- es]

buildOCtx :: Defs Name -> OCtx
buildOCtx defs =
  [("bool", builtinInfo "bool"), ("int", builtinInfo "int")]
    <> [(name, go name (toList ctors)) | (name, ctors) <- adts]
  where
    builtinInfo name =
      OADTInfo
        { oadts = [oblivName name],
          coerces = [[SConst name, SConst $ oblivName name]],
          joins = [SConst $ oblivName name],
          ctors = [],
          matches = ([], [])
        }
    adts = [(name, ctors) | (name, ADTDef {..}) <- defs]
    go adt ctorDefs =
      let oadts = [name | (name, OADTDef {..}) <- defs, pubName == adt]
          coerces =
            [ [SConst adt, SConst oadtName]
              | (_, FunDef {attr = KnownInst (ViewInst {..})}) <- defs,
                oadtName `elem` oadts
            ]
              <> [ [SConst oadtName, SConst oadtTo]
                   | (_, FunDef {attr = KnownInst (CoerceInst {..})}) <- defs,
                     oadtName `elem` oadts
                 ]
          reshapes =
            [ oadtName
              | (_, FunDef {attr = KnownInst (ReshapeInst {..})}) <- defs,
                oadtName `elem` oadts
            ]
          joins =
            [ SConst oadtName
              | (_, FunDef {attr = KnownInst (JoinInst {..})}) <- defs,
                oadtName `elem` reshapes
            ]
          decomposeCtor ty =
            let (dom, cod) = fromJust (isArrow1 ty)
             in decompose (tyToSTy cod) <> decompose (tyToSTy dom)
          ctor1 ctorName ts =
            (SConst adt : decomposeMany (tyToSTy <$> ts))
              : [ decomposeCtor ty
                  | (_, FunDef {attr = KnownInst (CtorInst {..}), ..}) <- defs,
                    ctor == ctorName
                ]
          ctors = [(ctorName, ctor1 ctorName ts) | (ctorName, ts) <- ctorDefs]
          decomposeMatch ty =
            let dec psi alts =
                  decomposeMany $
                    tyToSTy
                      <$> (psi : [fst $ fromJust (isArrow1 alt) | alt <- alts])
             in case fromJust (isArrow ty) of
                  (psi@Psi {} : alts, _) -> dec psi alts
                  (_ : psi : alts, _) -> dec psi alts
                  _ -> oops "Match instance has the wrong type"
          (matchesMC, matchesUn) =
            partition
              ( \case
                  (PolyT MergeableC, _) -> True
                  _ -> False
              )
              [ (poly, ty)
                | (_, FunDef {attr = KnownInst (MatchInst {..}), ..}) <- defs,
                  oadtName `elem` oadts
              ]
          matches =
            ( ( SConst adt
                  : foldMap (\(_, ts) -> decomposeMany (tyToSTy <$> ts)) ctorDefs
              )
                : [decomposeMatch ty | (_, ty) <- matchesUn],
              [decomposeMatch ty | (_, ty) <- matchesMC]
            )
       in OADTInfo {..}

tyToSTy_ :: (Ty Name -> Maybe (STy a)) -> Ty Name -> Maybe (STy a)
tyToSTy_ base = go
  where
    go Prod {olabel = PublicL, ..} =
      SProd <$> go left <*> go right
    go t@Pi {} = do
      (dom, cod) <- isArrow1 t
      SArrow <$> go dom <*> go cod
    go t = base t

pubTyToSTyBase :: Ty Name -> Maybe (STy a)
pubTyToSTyBase TUnit = return SUnit
pubTyToSTyBase (TBool PublicL) = return $ SConst "bool"
pubTyToSTyBase (TInt PublicL) = return $ SConst "int"
pubTyToSTyBase GV {..} = return $ SConst ref
pubTyToSTyBase _ = Nothing

pubTyToSTy :: Ty Name -> Maybe (STy a)
pubTyToSTy = tyToSTy_ pubTyToSTyBase

pubTyToSTy' :: Ty Name -> LiftM (STy a)
pubTyToSTy' t = case pubTyToSTy t of
  Just s -> return s
  _ -> errUnsupported

tyToSTyBase :: Ty Name -> Maybe (STy a)
tyToSTyBase (TBool OblivL) = return $ SConst $ oblivName "bool"
tyToSTyBase (TInt OblivL) = return $ SConst $ oblivName "int"
tyToSTyBase Psi {..} = return $ SConst oadtName
tyToSTyBase t = pubTyToSTyBase t

tyToSTy :: Ty Name -> STy a
tyToSTy = fromJust . tyToSTy_ tyToSTyBase

decompose :: STy a -> [STy a]
decompose SUnit = []
decompose (SConst x) = [SConst x]
decompose (SV x) = [SV x]
decompose (SProd l r) = decompose l <> decompose r
decompose (SArrow dom cod) = decompose dom <> decompose cod

decomposeMany :: [STy a] -> [STy a]
decomposeMany = foldMap decompose

sarrows_ :: [STy a] -> STy a -> STy a
sarrows_ = flip $ foldr SArrow

tell1 :: (MonadWriter w m, One w) => OneItem w -> m ()
tell1 x = tell $ one x

idxDoc :: Int -> Doc
idxDoc idx = "a" <> if idx == 0 then "" else pretty idx

instance Cute STy1 where
  cute SUnit = "unit"
  cute (SConst x) = cute x
  cute (SV idx) = return $ idxDoc idx
  cute t@(SProd l r) = cuteInfix t "*" l r
  cute t@(SArrow dom cod) = do
    domDoc <- cuteSub t dom
    codDoc <- cute cod
    return $ group domDoc <+> "->" <> line <> codDoc

instance HasPLevel (STy a) where
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

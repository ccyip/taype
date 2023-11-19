{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

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
import Control.Monad.RWS.CPS hiding (pass)
import Control.Monad.Writer.CPS hiding (pass)
import Data.Array
import Data.Char
import Data.Graph
import Data.List (lookup, partition)
import Data.Maybe (fromJust)
import Data.Text qualified as T
import Prettyprinter.Render.Text
import Relude.Extra.Bifunctor (secondF)
import Relude.Extra.Foldable1 (maximum1)
import Relude.Extra.Tuple (fmapToSnd)
import System.Process.Typed
import Taype.Common
import Taype.Cute hiding (space)
import Taype.Environment (GCtx, LCtx, lookupGCtx, makeLCtx)
import Taype.Error
import Taype.Lexer qualified as TL
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Taype.Syntax
import Taype.TypeChecker (hasPartialSum)
import Text.Megaparsec hiding (label)
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import Prelude hiding (Constraint, Sum (..), group, many)

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
    cctx :: CCtx Name,
    octx :: OCtx
  }

type LiftM a = FreshT (RWST Env Constraints Int (ExceptT Err IO)) a

data OADTInfo = OADTInfo
  { oadts :: [(Text, Int)],
    coerces :: [[STy2]],
    joins :: [STy2],
    ctors :: [(Text, [[STy2]])],
    matches :: ([[STy2]], [[STy2]]),
    sums :: [(Text, Text)]
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
  let name = isGV condTy
  lookupGDef name >>= \case
    ADTDef {..} -> do
      Options {optFlagNoSum} <- asks options
      octx <- asks octx
      let OADTInfo {sums} = fromJust $ lookup name octx
          noSum = optFlagNoSum || null sums
          tss = snd <$> toList ctors
      argss1 <- mapM freshTVs tss
      argss2 <-
        if noSum
          then return []
          else mapM freshTVs tss
      tell1 $ MatchC {cond = condIdx, ret = idx, argss = argss1 <> argss2}
      alts1' <- zipWith3M go (toList alts) tss argss1
      alts2' <-
        if noSum
          then return []
          else zipWith3M go (toList alts) tss argss2
      return $
        Ppx (MatchPpx {condTy = TV condIdx, retTy = TV idx, dyn = noSum})
          @@ (cond : alts1' <> alts2')
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
      return $ Ppx (LiftPpx {fn = ref, to = Just (TV idx)})
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
  octx <- lift $ buildOCtx options gctx defs
  lifted <- lifting octx [] $ hashNub $ fst <$> goals
  let liftedDefs = secondF (snd . fst) lifted
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
  let lifted' =
        [ (name, (def, reduceConstraints gctx octx cs))
          | (name, (def, cs)) <- lifted
        ]
      inputDoc = makeSolverInput octx lctx lifted' goals
  when optPrintSolverInput $ printDoc options inputDoc
  (outFile, content) <- runSolver inputDoc
  when optPrintSolverOutput $ printDoc options $ pretty content
  models <-
    parseSolverOutput outFile content >>= \case
      Left refused ->
        errRefused
          refused
          [ (name, fromJust $ lookup a actx)
            | (name, ((a, _), (actx, _, _))) <- lifted'
          ]
      Right models -> return models
  let defs' =
        runFreshM $
          gen
            models
            [ (name, (def, actx))
              | (name, ((_, def), (actx, _, _))) <- lifted'
            ]
  return $ defs <> defs'
  where
    lctx = makeLCtx defs
    goals = collectLifts $ snd <$> defs
    lifting _ done [] = return done
    lifting octx done fs = do
      lifted <- mapM (go octx) fs
      let fs' = hashNub $ fst <$> collectLifts [def | (_, ((_, def), _)) <- lifted]
          done' = lifted <> done
      lifting octx done' [f | f <- fs', isNothing $ lookup f done']
    go octx name =
      (name,)
        <$> case lookupGCtx name gctx of
          Just FunDef {..} ->
            runLiftM Env {cctx = [], defName = name, defLoc = loc, ..} $
              do
                x <- freshSV ty
                expr' <- liftExpr expr ty x
                return
                  ( x,
                    FunDef
                      { loc = -1,
                        expr = expr',
                        ty = TV x,
                        ..
                      }
                  )
          _ -> oops "Not a function"
    gen models ctx =
      forM models $ \(name, model) -> do
        let (def, actx) = fromJust $ lookup name ctx
            actx' = secondF (substSTyToTy gctx model) actx
            subst (TV x) = return $ fromJust $ lookup x actx'
            subst e = return e
            def' = runFreshM $ transformBiM subst def
        x <- fresh
        return
          ( instName2 name "lift" (internalName (show x)),
            case def' of
              FunDef {..} -> FunDef {attr = KnownInst (LiftInst name), ..}
              _ -> oops "Not a function"
          )

    runSolver inputDoc = do
      let inFile = fileNameOpt options "solver.input.sexp"
          outFile = fileNameOpt options "solver.output.sexp"
          logFile = fileNameOpt options "solver.log"
          statFile = fileNameOpt options "solver.stat"
          logArg = if optNoSolverLog then [] else [logFile, statFile]
      (ec, content) <-
        if optNoFiles
          then do
            let pc =
                  setStdin
                    ( byteStringInput
                        ( encodeUtf8 $
                            renderLazy $
                              layoutPretty defaultLayoutOptions inputDoc
                        )
                    )
                    $ proc optSolverPath ["-in", "-out"]
            secondF toStrict $ readProcessStdout pc
          else do
            writeDoc inFile inputDoc
            ec <- runProcess $ proc optSolverPath $ [inFile, outFile] <> logArg
            content <- case ec of
              ExitSuccess -> readFileBS outFile
              _ -> return ""
            return (ec, content)
      case ec of
        ExitSuccess ->
          return
            ( if optNoFiles then "<none>" else outFile,
              decodeUtf8 content
            )
        ExitFailure c ->
          err_ (-1) $
            "Solver failed with exit code" <+> pretty c

    errRefused refused ctx = do
      let getModel sty = zipWith (\v t -> (isSV v, t)) $ decompose sty
          lookupSTy x = fromJust (lookup x ctx)
          allRefused =
            [ let sty = lookupSTy name
               in (name, substSTyToTy gctx (getModel sty ts) sty)
              | (name, ts) <- refused
            ]
          refusedGoals = [g | g <- goals, g `elem` allRefused]
          goalDocs gs =
            sepWith
              hardline
              [ let t' = Ppx $ LiftPpx {fn = name, to = Just ty}
                 in runCuteM options $ cute (fromClosed t' :: Ty Text)
                | (name, ty) <- gs
              ]
      err_ (-1) $
        "Cannot solve the lifting constraints;"
          <+> "the following goals were refused"
          </> goalDocs refusedGoals
          </> "Here are all refused subgoals"
          </> goalDocs allRefused

----------------------------------------------------------------
-- Reduction

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
-- Solving constraints

makeSolverInput ::
  OCtx ->
  LCtx Name ->
  [(Text, ((Int, Def Name), (ACtx, CompatCtx, SConstraints)))] ->
  [(Text, Ty Name)] ->
  Doc
makeSolverInput octx lctx lifted goals =
  goalsDoc </> clsDoc </> axDoc </> coerDoc </> defDoc <> hardline2
  where
    goalsDoc = clause "goals" $ goalDoc1 <$> goals
    clsDoc = clause "classes" $ clsDoc1 <$> octx
    axDoc =
      clause
        "axioms"
        $ axDoc1 <$> filter (isJust . flip lookup lifted . fst) lctx
    coerDoc =
      clause "coerces" $
        coerDoc1
          <$> concat [coerces | (_, OADTInfo {..}) <- octx]
    coerDoc1 ts = parens $ hsep (styDoc <$> ts)
    defDoc = clause "definitions" $ defDoc1 <$> lifted
    clause name xs = parens $ hang $ sep $ name : xs
    goalDoc1 (x, t) =
      let ts = decompose $ tyToSTy t
       in parens $ hang $ fillSep $ pretty x : (styDoc <$> ts)
    clsDoc1 (x, OADTInfo {oadts}) =
      parens $ align $ fillSep $ pairDoc <$> ((x, 0) : oadts)
    pairDoc (x, y) = parens $ hsep [pretty x, pretty y]
    axDoc1 (x, ts) =
      let tss = decompose . tyToSTy . fst <$> ts
       in clause (pretty x) $ tss <&> parens . align . fillSep . fmap styDoc
    defDoc1 (x, ((idx, _), (actx, cctx, cs))) =
      let t = fromJust $ lookup idx actx
       in clause
            (pretty x)
            [ compatCtxDoc cctx,
              signDoc t,
              argsDoc t,
              csDoc cs
            ]
    compatCtxDoc cctx =
      parens $
        align $
          fillSep $
            cctx <&> \(x, cls) ->
              parens $ styDoc (SV x) <+> pretty cls
    signDoc t =
      parens $
        align $
          fillSep
            [if s then "+" else "-" | s <- decomposeSign True t]
    argsDoc t =
      let ts = decompose t
       in parens $ align $ fillSep $ styDoc <$> ts
    csDoc cs =
      let (liftCs', cs') =
            partition
              ( \case
                  SLiftC _ _ -> True
                  _ -> False
              )
              cs
       in scDocs cs' <> line <> scDocs liftCs'

    styDoc :: STy2 -> Doc
    styDoc (SConst x) = pretty x
    styDoc (SV (x, y)) = pretty $ internalName $ show x <> "_" <> show y
    styDoc _ = oops "Not a base type"

    scDoc (SEqC t1 t2) = clause "=" [styDoc t1, styDoc t2]
    scDoc (SLiftC x ts) = clause (pretty x) (styDoc <$> ts)
    scDoc (SOrC css) =
      clause "or" $ scDocs <$> css
    scDocs cs = parens $ align $ lstDoc $ scDoc <$> cs

type Parser = TL.Parser

parseSolverOutput ::
  FilePath ->
  Text ->
  ExceptT Err IO (Either [(Text, [Text])] [(Text, [(SName, Text)])])
parseSolverOutput file content =
  case parse pOutput file content of
    Left e ->
      err_ (-1) $
        "Cannot parse solver output"
          </> pretty (errorBundlePretty e)
    Right r -> return r
  where
    space :: Parser ()
    space = L.space C.space1 empty empty
    lexeme :: Parser a -> Parser a
    lexeme = L.lexeme space
    symbol :: Text -> Parser Text
    symbol = L.symbol space
    pList :: Parser a -> Parser a
    pList = between (symbol "(") (symbol ")")
    pAtom :: Parser Text
    pAtom =
      lexeme
        ( takeWhile1P
            Nothing
            (\c -> not (isSpace c) && c /= '(' && c /= ')')
        )
    pAssn :: Parser (SName, Text)
    pAssn = pList $ do
      void $ chunk internalPrefix
      x <- L.decimal
      void $ single '_'
      y <- L.decimal
      space
      name <- pAtom
      return ((x, y), name)
    pModel :: Parser (Text, [(SName, Text)])
    pModel = pList $ do
      name <- pAtom
      void $ pList $ many pAtom
      assns <- many pAssn
      return (name, assns)
    pSolved :: Parser [(Text, [(SName, Text)])]
    pSolved = pList $ symbol "solved" *> many pModel
    pGoal :: Parser (Text, [Text])
    pGoal = pList $ (,) <$> pAtom <*> many pAtom
    pFailed :: Parser [(Text, [Text])]
    pFailed = pList $ symbol "failed" *> many pGoal
    pOutput = eitherP (try pFailed) pSolved

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
      return $ [(fn, ty) | Ppx {ppx = LiftPpx {to = Just ty, ..}} <- es]

buildOCtx :: Options -> GCtx Name -> Defs Name -> IO OCtx
buildOCtx options@Options {..} gctx defs = do
  oadtCtx <- forM adts $ \(name, ctors) -> (name,) <$> go name (toList ctors)
  return $ [("bool", builtinInfo "bool"), ("int", builtinInfo "int")] <> oadtCtx
  where
    builtinInfo name =
      OADTInfo
        { oadts = [(oblivName name, 1)],
          coerces = [[SConst name, SConst $ oblivName name]],
          joins = [SConst $ oblivName name],
          ctors = [],
          matches = ([], []),
          sums = []
        }
    adts = [(name, ctors) | (name, ADTDef {..}) <- defs]
    go adt ctorDefs = do
      ctors <- forM ctorDefs $ \(ctorName, ts) ->
        (ctorName,) <$> ctor1 ctorName ts
      return
        OADTInfo
          { oadts = oadts <> oadts',
            joins = SConst <$> (joins <> (fst <$> oadts')),
            ..
          }
      where
        oadtNames = [name | (name, OADTDef {..}) <- defs, pubName == adt]
        userCoerces =
          [ (oadtName, oadtTo)
            | (_, FunDef {attr = KnownInst (CoerceInst {..})}) <- defs,
              oadtName `elem` oadtNames
          ]
        reshapes =
          [ oadtName
            | (_, FunDef {attr = KnownInst (ReshapeInst {..})}) <- defs,
              oadtName `elem` oadtNames
          ]
        joins =
          [ oadtName
            | (_, FunDef {attr = KnownInst (JoinInst {..})}) <- defs,
              oadtName `elem` reshapes
          ]
        sums =
          if optFlagNoSum
            then []
            else
              [ (from, to)
                | (from, to) <- userCoerces,
                  from `notElem` joins,
                  to `elem` joins
              ]
        oadts =
          secondF (* 2) $
            inferCosts optReverseCost adt oadtNames $
              [(adt, oadtName) | oadtName <- oadtNames] <> userCoerces
        oadts' =
          [ ( sumName left right,
              (fromJust (lookup left oadts) + fromJust (lookup right oadts))
                `div` 2
            )
            | (left, right) <- sums
          ]
        coerces =
          [ [SConst adt, SConst oadtName]
            | (_, FunDef {attr = KnownInst (ViewInst {..})}) <- defs,
              oadtName `elem` oadtNames
          ]
            <> [[SConst from, SConst to] | (from, to) <- userCoerces]
            <> concat
              [ let sname = sumName from to
                 in [ [SConst adt, SConst sname],
                      [SConst from, SConst sname],
                      [SConst sname, SConst to]
                    ]
                      <> [[SConst to, SConst sname] | not optFlagStrictCoerce]
                | (from, to) <- sums
              ]
        lookupCtor ctorName name =
          [ fst $ fromJust $ isArrow1 ty
            | (_, FunDef {attr = KnownInst (CtorInst {..}), ..}) <- defs,
              oadtName == name,
              ctor == ctorName
          ]
        decomposeCtor name ty =
          let ts = decompose (tyToSTy ty)
           in SConst name : ts
        sumCtor ctorName =
          forM
            [ (sumName from to, fromTy, toTy)
              | (from, to) <- sums,
                fromTy <- lookupCtor ctorName from,
                toTy <- lookupCtor ctorName to
            ]
            $ \(name, from, to) ->
              runMaybeT $
                exceptToMaybeT $
                  (name,) <$> hasPartialSum options gctx from to
        ctor1 ctorName ts = do
          sumCtors <- sumCtor ctorName
          return $
            (SConst adt : decomposeMany (tyToSTy <$> ts))
              : [ decomposeCtor oadt ty
                  | oadt <- oadtNames,
                    ty <- lookupCtor ctorName oadt
                ]
                <> [decomposeCtor name ty | Just (name, ty) <- sumCtors]
        argOfAlts alts = [fst $ fromJust (isArrow1 alt) | alt <- alts]
        lookupMatch name =
          [ ( case poly of
                PolyT MergeableC -> True
                _ -> False,
              case fromJust (isArrow ty) of
                (Psi {} : alts, _) -> argOfAlts alts
                (_ : _ : alts, _) -> argOfAlts alts
                _ -> oops "Match instance has the wrong type"
            )
            | (_, FunDef {attr = KnownInst (MatchInst {..}), ..}) <- defs,
              oadtName == name
          ]
        decomposeMatch name ty ty' =
          let ts = decomposeMany (tyToSTy <$> ty)
              ts' = decomposeMany (tyToSTy <$> ty')
           in SConst name : ts <> ts'
        (matchesMC, matchesUn) =
          partition
            fst
            $ [ (mc, (oadt, ty, ty))
                | oadt <- oadtNames,
                  (mc, ty) <- lookupMatch oadt
              ]
              <> [ (fromMC || toMC, (sumName from to, fromTy, toTy))
                   | (from, to) <- sums,
                     (fromMC, fromTy) <- lookupMatch from,
                     (toMC, toTy) <- lookupMatch to
                 ]
        matches =
          ( ( let ts =
                    foldMap
                      (\(_, ty) -> decomposeMany (tyToSTy <$> ty))
                      ctorDefs
               in SConst adt : ts <> ts
            )
              : [decomposeMatch name ty ty' | (_, (name, ty, ty')) <- matchesUn],
            [decomposeMatch name ty ty' | (_, (name, ty, ty')) <- matchesMC]
          )

sumName :: Text -> Text -> Text
sumName x y = x <> "+" <> y

-- The first argument allows the costs to be reversed, so we can see how the
-- cost assignment may affect the performance. It is a placeholder for now, not
-- implemented yet.
inferCosts :: Bool -> Text -> [Text] -> [(Text, Text)] -> [(Text, Int)]
inferCosts _ adt oadts coerces =
  let costs = go sorted $ graph $> 0
   in fmapToSnd (\k -> costs ! fromJust (toVertex k)) oadts
  where
    -- Edges are reversed.
    (graph, _, toVertex) =
      graphFromEdges $
        (adt : oadts)
          <&> \v -> (v, v, [from | (from, to) <- coerces, to == v])
    sorted = reverseTopSort graph
    -- Calculate the longest pathes.
    go [] tbl = tbl
    go (v : vs) tbl =
      let incomings = graph ! v
          costs = (tbl !) <$> incomings
          tbl' = tbl // [(v, 1 + maximum1 (-1 :| costs))]
       in go vs tbl'

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
tyToSTyBase Sum {left = Psi {..}, right = Psi {oadtName = oadtName'}} =
  return $ SConst (sumName oadtName oadtName')
tyToSTyBase t = pubTyToSTyBase t

tyToSTy :: Ty Name -> STy a
tyToSTy = fromJust . tyToSTy_ tyToSTyBase

substSTyToTy :: GCtx a -> [(SName, Text)] -> STy2 -> Ty a
substSTyToTy gctx model = go
  where
    go SUnit = TUnit
    go (SConst x) = base x
    go (SProd l r) = Prod {olabel = PublicL, left = go l, right = go r}
    go (SArrow d c) = arrow_ (go d) (go c)
    go (SV x) = base $ fromJust $ lookup x model

    base x | x == "bool" = TBool PublicL
    base x | x == oblivName "bool" = TBool OblivL
    base x | x == "int" = TInt PublicL
    base x | x == oblivName "int" = TInt OblivL
    base (T.splitOn "+" -> [left, right]) =
      Sum {olabel = PublicL, left = base left, right = base right}
    base x = case lookupGCtx x gctx of
      Just ADTDef {} -> GV x
      Just OADTDef {viewTy} -> Psi {oadtName = x, viewTy = Just viewTy}
      _ -> oops $ "Unknown name " <> x

decompose :: STy a -> [STy a]
decompose SUnit = []
decompose (SConst x) = [SConst x]
decompose (SV x) = [SV x]
decompose (SProd l r) = decompose l <> decompose r
decompose (SArrow dom cod) = decompose dom <> decompose cod

decomposeMany :: [STy a] -> [STy a]
decomposeMany = foldMap decompose

decomposeSign :: Bool -> STy a -> [Bool]
decomposeSign s = \case
  SUnit -> []
  SConst _ -> [s]
  SV _ -> [s]
  SProd l r -> decomposeSign s l <> decomposeSign s r
  SArrow dom cod -> decomposeSign (not s) dom <> decomposeSign s cod

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
            </> parens (align (lstDoc (runCuteM options . cute <$> cs)))

lstDoc :: [Doc] -> Doc
lstDoc [] = mempty
lstDoc (doc : docs) = doc <> foldMap sep1 docs

err_ :: (MonadError Err m) => Int -> Doc -> m a
err_ errLoc errMsg = do
  throwError
    Err
      { errCategory = "Lifting Error",
        errClass = ErrorC,
        ..
      }

err :: Doc -> LiftM a
err errMsg = do
  Env {..} <- ask
  err_ defLoc $
    "Cannot lift function"
      <+> pretty defName
      </> errMsg

errUnsupported :: LiftM a
errUnsupported =
  err
    "Do not support lifting oblivious constructs, preprocessors, \
    \or polymorphic equality (except for integer equality)"

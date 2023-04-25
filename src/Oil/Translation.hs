{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Translate taype to OIL.
module Oil.Translation (toOilProgram) where

import Data.Graph (graphFromEdges, reachable)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (member)
import Data.List (partition)
import Data.Maybe (fromJust)
import Oil.Optimization
import Oil.Syntax
import Relude.Extra.Bifunctor
import Taype.Binder
import Taype.Common
import Taype.Environment (GCtx (..))
import Taype.Name
import Taype.Plate
import Taype.Prelude
import Taype.Syntax qualified as T

----------------------------------------------------------------
-- Environment for translation

newtype Env = Env
  { -- Whether the translation is in the reveal phase
    revealing :: Bool
  }

-- | The translation monad
type TslM = FreshT (Reader Env)

runTslM :: Env -> TslM a -> a
runTslM env m = runReader (runFreshT m) env

----------------------------------------------------------------
-- Translating expressions and types

-- | Translate a taype expression to the corresponding OIL expression.
--
-- The taype expression is well-typed and in core taype, but not necessarily in
-- ANF.
--
-- The resulting OIL expression should be typed by the corresponding translated
-- OIL type, under the (implicit) translated typing context. The types and
-- context are translated according to 'toOilTy'.
--
-- The resulting OIL expression should also be behaviorally equivalent to the
-- taype expression.
toOilExpr :: T.Expr Name -> TslM (Expr Name)
toOilExpr T.V {..} = return V {..}
toOilExpr T.GV {..} = return GV {..}
-- Unit value is an empty oblivious array.
toOilExpr T.VUnit = return $ GV aNew @@ [ILit 0]
toOilExpr T.BLit {..} = return $ if bLit then GV "True" else GV "False"
toOilExpr T.ILit {..} = return ILit {..}
toOilExpr T.Lam {..} = do
  (x, body) <- unbind1 bnd
  body' <- toOilExpr body
  return $ lamB x binder body'
toOilExpr T.App {..} = do
  fn' <- toOilExpr fn
  args' <- mapM toOilExpr args
  return $ fn' @@ args'
toOilExpr T.Let {..} = do
  rhs' <- toOilExpr rhs
  (x, body) <- unbind1 bnd
  body' <- toOilExpr body
  return $ letB x binder rhs' body'
toOilExpr T.Ite {..} = do
  cond' <- toOilExpr cond
  left' <- toOilExpr left
  right' <- toOilExpr right
  return $ ite_ cond' left' right'
toOilExpr T.Match {..} = do
  cond' <- toOilExpr cond
  alts' <- mapM go (toList alts)
  return $ matchB cond' alts'
  where
    go MatchAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- toOilExpr body
      return (ctor, zip xs binders, body')
toOilExpr T.OIte {..} = do
  cond' <- toOilExpr cond
  left' <- toOilExpr left
  right' <- toOilExpr right
  revealing <- asks revealing
  return $
    if revealing
      then
        ite_
          ( GV (retractionName (oblivName "bool"))
              @@ [cond']
          )
          left'
          right'
      else GV aMux @@ [cond', left', right']
toOilExpr T.Pair {..} = do
  let fn = case pairKind of
        OblivP -> GV aConcat
        _ -> GV "(,)"
  args <- mapM toOilExpr [left, right]
  return $ fn @@ args
toOilExpr T.PMatch {..} = do
  cond' <- toOilExpr cond
  ((xl, xr), body) <- unbind2 bnd2
  body' <- toOilExpr body
  case pairKind of
    OblivP -> do
      let (leftTy, rightTy) = fromJust condTy
      lSize <- toOilSize leftTy
      rSize <- toOilSize rightTy
      return $
        letsB
          [ (xl, lBinder, GV aSlice @@ [cond', ILit 0, lSize]),
            (xr, rBinder, GV aSlice @@ [cond', lSize, rSize])
          ]
          body'
    _ ->
      return $
        matchB
          cond'
          [("(,)", [(xl, lBinder), (xr, rBinder)], body')]
toOilExpr T.OInj {..} = do
  expr' <- toOilExpr expr
  let (leftTy, rightTy) = fromJust injTy
  lSize <- toOilSize leftTy
  rSize <- toOilSize rightTy
  return $
    GV (oblivName $ if tag then "inl" else "inr")
      @@ [lSize, rSize, expr']
toOilExpr T.OProj {..} = do
  expr' <- toOilExpr expr
  let (leftTy, rightTy) = fromJust projTy
  tSize <- toOilSize $ T.TBool OblivL
  lSize <- toOilSize leftTy
  rSize <- toOilSize rightTy
  return $ case projKind of
    TagP -> GV aSlice @@ [expr', ILit 0, tSize]
    LeftP -> GV aSlice @@ [expr', tSize, lSize]
    RightP -> GV aSlice @@ [expr', tSize, rSize]
toOilExpr T.Arb {..} = do
  let ty = fromJust oblivTy
  size <- toOilSize ty
  return $ GV aNew @@ [size]
toOilExpr _ = oops "Not a term in core taype ANF"

-- | Translate a taype oblivious type to the OIL expression representing its
-- size.
--
-- The taype type is obliviously kinded and in core taype ANF.
--
-- The resulting OIL expression should be typed by 'sizeTy' under the (implicit)
-- translated typing context, according to 'toOilTy'.
--
-- For a taype term typed by the given oblivious taype type, its translated OIL
-- term (according to 'toOilExpr') is an oblivious array of the size indicated
-- by the resulting OIL expression. In particular, if this taype term is closed,
-- the computed OIL expression is exactly the integer for the size of the
-- computed array.
toOilSize :: T.Ty Name -> TslM (Expr Name)
toOilSize T.TUnit = return $ ILit 0
-- Oblivious boolean is the same as oblivious integer in OIL.
toOilSize (T.TBool OblivL) = return $ ILit 1
toOilSize (T.TInt OblivL) = return $ ILit 1
toOilSize T.Prod {olabel = OblivL, ..} = do
  lSize <- toOilSize left
  rSize <- toOilSize right
  return $ GV "+" @@ [lSize, rSize]
toOilSize T.OSum {..} = do
  lSize <- toOilSize left
  rSize <- toOilSize right
  return $ GV "+" @@ [ILit 1, GV (internalName "max") @@ [lSize, rSize]]
toOilSize T.App {fn = T.GV {..}, ..} = do
  args' <- mapM toOilExpr args
  return $ GV ref @@ args'
toOilSize T.Let {..} = do
  rhs' <- toOilExpr rhs
  (x, body) <- unbind1 bnd
  body' <- toOilSize body
  return $ letB x binder rhs' body'
toOilSize T.Ite {..} = do
  cond' <- toOilExpr cond
  left' <- toOilSize left
  right' <- toOilSize right
  return $ ite_ cond' left' right'
toOilSize T.PMatch {..} = do
  cond' <- toOilExpr cond
  ((xl, xr), body) <- unbind2 bnd2
  body' <- toOilSize body
  return $
    matchB
      cond'
      [("(,)", [(xl, lBinder), (xr, rBinder)], body')]
toOilSize T.Match {..} = do
  cond' <- toOilExpr cond
  alts' <- mapM go (toList alts)
  return $ matchB cond' alts'
  where
    go MatchAlt {..} = do
      (xs, body) <- unbindMany (length binders) bnd
      body' <- toOilSize body
      return (ctor, zip xs binders, body')
toOilSize _ = oops "Not an oblivious type"

-- | Translate a taype type to the corresponding OIL type.
--
-- The taype type is well-kinded and in core taype ANF. If the taype type is
-- obliviously kinded, then the result should be oblivious array.
--
-- Two equivalent taype type should be translated to the same OIL type.
toOilTy :: T.Ty Name -> Ty
toOilTy (T.TBool PublicL) = tGV "bool"
toOilTy (T.TInt PublicL) = TInt
toOilTy T.GV {..} = tGV ref
toOilTy T.Prod {..} = prod_ (toOilTy left) (toOilTy right)
-- NOTE: Psi type is translated to a pair for now. This may change in the
-- future.
toOilTy T.Psi {..} = prod_ (toOilTy (fromJust viewTy)) OArray
toOilTy T.Pi {..} =
  let dom = toOilTy ty
      -- We instantiate the pi type argument with some arbitrary term, as the
      -- type translation does not care about the type index.
      body = instantiateName badName bnd
      cod = toOilTy body
   in Arrow {..}
toOilTy T.TV = TV
-- Oblivious types, including type level computation, are translated into
-- oblivious array.
toOilTy _ = OArray

-- | Build a boolean section function.
boolSection :: Expr Name
boolSection = runFreshM $ do
  b <- fresh
  return $
    lamB b (Just "b") $
      GV (sectionName (oblivName "int")) @@ [ite_ (V b) (ILit 1) (ILit 0)]

-- | Build a boolean retraction function.
boolRetraction :: Expr Name
boolRetraction = runFreshM $ do
  a <- fresh
  return $
    lamB a (Just "a") $
      GV "not"
        @@ [ GV "=="
               @@ [ GV (retractionName (oblivName "int")) @@ [V a],
                    ILit 0
                  ]
           ]

-- | Build an oblivious injection.
--
-- The argument indicates whether it is left or right injection.
oblivInjDef :: Bool -> Expr Name
oblivInjDef tag = runFreshM $ do
  m <- fresh
  n <- fresh
  a <- fresh
  d <- fresh
  t <- fresh
  return
    $ lamsB
      ( if tag
          then
            [ (m, Just "m"),
              (n, Just "n"),
              (a, Just "a")
            ]
          else
            [ (n, Just "n"),
              (m, Just "m"),
              (a, Just "a")
            ]
      )
    $ letsB
      [ ( d,
          Just "d",
          ite_
            (GV "<=" @@ [V n, V m])
            (V a)
            (GV aConcat @@ [V a, GV aNew @@ [GV "-" @@ [V n, V m]]])
        ),
        ( t,
          Just "t",
          GV (sectionName (oblivName "int")) @@ [if tag then ILit 1 else ILit 0]
        )
      ]
    $ GV aConcat @@ [V t, V d]

----------------------------------------------------------------
-- Translating definitions

-- | Translate taype definitions to the corresponding OIL definitions.
--
-- The result contains 3 sets of definitions: the safe OIL definitions for the
-- oblivious computation phase, the section functions with their dependencies
-- for the conceal phase, and the leaky functions (e.g., retractions) for the
-- reveal phase.
toOilProgram :: Options -> GCtx Name -> T.Defs Name -> IO Program
toOilProgram options@Options {..} gctx defs = do
  mainDefs' <- goOpt $ go False mainDefs
  concealDefs' <- goOpt $ go False concealDefs
  revealDefs' <- goOpt $ go True revealDefs
  return
    Program
      { mainDefs = fromClosedDefs $ simp mainDefs',
        concealDefs = fromClosedDefs $ simp concealDefs',
        revealDefs = fromClosedDefs $ simp revealDefs',
        ..
      }
  where
    go revealing =
      secondF $ unfoldBuiltin . runTslM Env {..} . toOilDef
    (mainDefs, revealDefs) = partition (isSafe . snd) defs
    concealDefs = filterConceal defs oadts
    goOpt = optimize options actx
    actx = flip HM.mapMaybe (unGCtx gctx) $ \case
      T.FunDef {attr = KnownInst inst} -> Just inst
      _ -> Nothing

    oadts =
      [ OADTInfo
          { section = sectionName oadtName,
            retraction = retractionName oadtName,
            ..
          }
        | (oadtName, T.OADTDef {}) <- defs
      ]

    isSafe T.FunDef {label = LeakyL} = False
    isSafe _ = True

    simp =
      secondF $ (if optReadable then readableDef else id) . simpDef

-- | Translate a taype definition to the corresponding OIL definition.
toOilDef :: T.Def Name -> TslM (Def Name)
toOilDef T.FunDef {..} = do
  let ty' = toOilTy ty
  expr' <- toOilExpr expr
  return FunDef {ty = ty', expr = expr'}
toOilDef T.OADTDef {..} = do
  let viewTy' = toOilTy viewTy
  (x, body) <- unbind1 bnd
  body' <- toOilSize body
  return
    FunDef
      { ty = Arrow viewTy' sizeTy,
        expr = lamB x binder body'
      }
toOilDef T.ADTDef {..} = do
  let ctors' = secondF (toOilTy <$>) $ toList ctors
  return ADTDef {ctors = ctors'}
toOilDef _ = oops "Translating constructor or builtin definitions"

filterConceal :: T.Defs Name -> [OADTInfo] -> T.Defs Name
filterConceal allDefs oadts = [def | def@(name, _) <- defs, name `member` concealSet]
  where
    defs = [def | def@(_, T.FunDef {}) <- allDefs]
    (graph, fromVertex, toVertex) = graphFromEdges $ mkDepGraph defs
    sectionDefs = [section | OADTInfo {..} <- oadts]
    reachableSet name =
      fromList $ maybe [] (toNames . reachable graph) $ toVertex name
    toNames vs = [name | (_, name, _) <- fromVertex <$> vs]
    concealSet = fromList sectionDefs <> foldMap reachableSet sectionDefs

mkDepGraph :: T.Defs Name -> [(T.NamedDef Name, Text, [Text])]
mkDepGraph defs =
  let depss = runFreshM $ mapM (go . snd) defs
   in zipWith (\def deps -> (def, fst def, deps)) defs depss
  where
    go T.FunDef {..} = do
      deps <- universeM expr
      return $ hashNub [x | T.GV x <- deps]
    go _ = return []

-- | Unfold all builtin definitions that are not primitive.
unfoldBuiltin :: Def Name -> Def Name
unfoldBuiltin = runFreshM . transformBiM go
  where
    go e@App {fn = GV {..}, ..} =
      if
          | ref == sectionName (oblivName "bool") -> unfoldWith boolSection
          | ref == retractionName (oblivName "bool") -> unfoldWith boolRetraction
          | ref == oblivName "inl" -> unfoldWith $ oblivInjDef True
          | ref == oblivName "inr" -> unfoldWith $ oblivInjDef False
          | otherwise -> return e
      where
        unfoldWith e' = do
          x <- fresh
          return $
            letB x (Just (toBinder ref)) e' $
              V x @@ args
    go e = return e

----------------------------------------------------------------
-- Simplification of OIL expressions

-- | Simplify OIL expressions.
--
-- This function performs various simplifcation such as let flattening and
-- application collapsing.
simpDef :: Def Name -> Def Name
simpDef = runFreshM . transformBiM go
  where
    go App {args = [], ..} = return fn
    go App {fn = App {..}, args = args'} =
      return $ fn @@ args <> args'
    go e@Let {..} = case rhs of
      V {..} -> return $ instantiateName name bnd
      GV {..} -> return $ instantiate_ GV {..} bnd
      ILit {..} -> return $ instantiate_ ILit {..} bnd
      Let {binder = binderN, rhs = rhsN, bnd = bndN} -> do
        (x, bodyN) <- unbind1 bndN
        body' <- go Let {rhs = bodyN, ..}
        return $ letB x binderN rhsN body'
      _ -> do
        (x, body) <- unbind1 bnd
        case body of
          V y | y == x -> return rhs
          _ -> return e
    go e = return e

-- | Make the generated OIL programs more readable.
--
-- This function subsitutes all let bindings that do not have a named binder.
readableDef :: Def Name -> Def Name
readableDef = runFreshM . transformBiM go
  where
    go :: Expr Name -> FreshM (Expr Name)
    go Let {binder = Nothing, ..} = return $ instantiate_ rhs bnd
    go e = return e

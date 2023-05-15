{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
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
-- Bidirectional type checker for the taype language.
--
-- The expressions or types may be required to be in some particular forms, as
-- outlined below.
--
--   - WHNF: weak head normal form. Unlike standard WHNF, global variables are
--     not unfolded until type equivalence check, to avoid a class of divergence
--     likely caused by ANF. Applications with no arguments are reduced to only
--     the head, and nested applications are flatterned to a single head with a
--     list of arguments. Builtin functions are not normalized at the moment
--     although it is possible (e.g., addition with two integer literals).
--     Oblivious constructs such as boolean section are not normalized either.
--     While possible, it is mostly unnecessary in practice.
--
--   - ANF: administrative normal form. In addition to the standard ANF, we also
--     require the constructors are always in application form, even if they
--     have no argument. Worth noting is that global names (including builtin
--     ones) should be in standalone let bindings, i.e. applications only
--     contain local variables, and the last expression of a let binding must be
--     a variable.
--
--   - Core taype: an expression is in core taype, if
--
--     * It is fully annotated. This includes type annotations and annotations
--       specific to certain constructs, e.g., discriminee types in oblivious
--       sum elimination.
--
--     * No ascription, location, oblivious sum pattern matching or
--       preprocessors.
--
--     * The alternatives in all pattern matchings are in the canonical order,
--       i.e. the order in the corresponding ADT signature.
--
-- We maintain a few invariants throughout the type checking process.
--
--   - Types in the global typing context must be well-kinded and in core taype
--     ANF. It includes the signatures of function definitions, constructor
--     arguments and OADT arguments.
--
--   - Definitions in the global definition context must be well-typed or
--     well-kinded (against their signatures in typing context). They must also
--     be in core taype ANF.
--
--   - Types in the local typing context must be well-kinded and in core taype
--     ANF.
--
-- Other invariants for each procedure are documented in that procedure.
module Taype.TypeChecker (checkDefs, elabPpxDefs) where

import Algebra.Lattice
import Algebra.PartialOrd
import Bound
import Control.Monad.Error.Class
import Data.Char
import Data.List (lookup, partition)
import Data.Maybe (fromJust)
import Data.Text qualified as T
import Relude.Extra.Bifunctor
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.NonEmpty qualified as NE
import Taype.Plate
import Taype.Prelude
import Taype.Syntax

----------------------------------------------------------------
-- Bidirectional type and kind checkers

-- | Type check an expression bidirectionally.
--
-- The second argument is the type that this expression is checked against if
-- present. Otherwise, the type of the expression is being inferred. This
-- function returns the expression's type and its full elaboration.
--
-- The given type must be well-kinded and in core taype ANF.
--
-- The returned type must be well-kinded and in core taype ANF. It is also
-- equivalent to the given type if in type checking mode.
--
-- The returned expression must be in core taype ANF. Of course, it must also be
-- typed by the returned type, and equivalent to the given expression.
typing ::
  Expr Name ->
  Maybe (Ty Name) ->
  TcM (Ty Name, Expr Name)
typing e@VUnit Nothing = mkLet' TUnit e
typing e@BLit {} Nothing = mkLet' (TBool PublicL) e
typing e@ILit {} Nothing = mkLet' (TInt PublicL) e
typing e@V {..} Nothing =
  lookupTy name >>= \case
    Just t -> return (t, e)
    -- The expression is locally closed before type checking, so open local
    -- variables are not possible.
    _ -> oops $ "Local variable not in scope: " <> show name
typing e@GV {..} Nothing =
  lookupGSig ref >>= \case
    Just FunDef {..} -> do
      checkLabel label
      case poly of
        PolyT _ ->
          err
            [ [ DD "Type polymorphic functions (OADT match instances)",
                DD "are not allowed to be called directly (yet)"
              ]
            ]
        _ -> pass
      mkLet' ty e
    Just CtorDef {..} -> do
      checkArity CtorApp ref [] paraTypes
      -- All constructors are in application form even if they have zero
      -- argument.
      mkLet' (GV dataType) (e @@ [])
    Just BuiltinDef {..} -> do
      checkLabel label
      mkLet' (arrows_ paraTypes resType) e
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not a term"]]
    _ ->
      err [[DD "Variable", DQ ref, DD "is not in scope"]]
typing Lam {argTy = Just argTy, ..} Nothing = do
  argTy' <- kinded argTy
  (x, body) <- unbind1 bnd
  (bodyTy', body') <-
    extendCtx1 x argTy' binder $ infer body
  mkLet'
    Pi
      { ty = argTy',
        bnd = abstract_ x bodyTy',
        ..
      }
    Lam
      { argTy = Just argTy',
        bnd = abstract_ x body',
        ..
      }
typing Lam {..} (Just t) = do
  (argTy', _, bndTy') <- isPi t
  whenJust argTy $ \ty -> do
    ty' <- kinded ty
    -- If the argument type is given in the lambda term, it has to agree with
    -- the one in the pi-type.
    withLoc_ ty $ equate argTy' ty'
  (x, body, bodyTy') <- unbind1With bnd bndTy'
  body' <- extendCtx1 x argTy' binder $ check body bodyTy'
  mkLet'
    Pi
      { ty = argTy',
        bnd = abstract_ x bodyTy',
        ..
      }
    Lam
      { argTy = Just argTy',
        bnd = abstract_ x body',
        ..
      }
typing App {..} Nothing =
  maybeGV fn >>= \case
    -- Constructors have to be fully applied.
    Just (ctor, CtorDef {..}) ->
      typeCtorApp ctor paraTypes (GV dataType)
    _ -> typeFnApp
  where
    -- Application for constructors
    typeCtorApp f paraTypes resType = do
      checkArity CtorApp f args paraTypes
      args' <- zipWithM check args paraTypes
      xs <- freshes $ length args'
      let bindings = zip3 xs paraTypes args'
      secondF (lets' bindings) $ mkLet' resType $ f @@@ V <$> xs
    -- Application for functions
    typeFnApp = do
      (fnTy', fn') <- infer fn
      (bindings, t') <- go args fnTy'
      x <- fresh
      secondF (lets' ((x, fnTy', fn') : bindings)) $
        mkLet' t' $
          V x @@ [V a | (a, _, _) <- bindings]
    -- @t@ must be well-kinded and in core taype ANF.
    go [] t = return ([], t)
    go (arg : args') t = do
      (argTy', _, bndTy) <- isPi t
      arg' <- check arg argTy'
      -- Unfortunately, we have to kind the pi-type body again here even though
      -- it was in good form, because it may not be in core taype ANF anymore
      -- after instantiation.
      bodyTy' <- kinded $ instantiate_ arg' bndTy
      (res, t') <- go args' bodyTy'
      x <- fresh
      return ((x, argTy', arg') : res, t')

-- NOTE: checking mode for let is possible, but it requires a local definition
-- context.
typing Let {..} Nothing = do
  mt <- mapM kinded rhsTy
  (rhsTy', rhs') <- typing rhs mt
  (x, body) <- unbind1 bnd
  (t, body') <- extendCtx1 x rhsTy' binder $ infer body
  -- Unfortunately, we have to kind @t@ again even though it is kinded, because
  -- it may not be in core taype ANF after substitution.
  t' <- kinded $ substitute x rhs' t
  return
    ( t',
      Let
        { rhsTy = Just rhsTy',
          rhs = rhs',
          bnd = abstract_ x body',
          ..
        }
    )
typing Ite {..} mt = do
  cond' <- check cond $ TBool PublicL
  let ctxs = NE.fromList [[], []]
      argss = NE.fromList [[], []]

      -- Typing without dependent types
      typeNoDep = do
        (t', left') <- typing left mt
        right' <- check right t'
        return (left', right', t')

      -- Infer a dependent type.
      inferDep = do
        (leftTy', left') <- infer left
        (rightTy', right') <- infer right
        t' <- depGen gen ctxs argss (NE.fromList [leftTy', rightTy'])
        return (left', right', t')

      -- Check a dependent type.
      checkDep t' = do
        (leftTy', rightTy') <-
          depMatch match ctxs argss t' >>= \case
            leftTy' :| [rightTy'] -> return (leftTy', rightTy')
            _ -> depBrOops
        left' <- check left leftTy'
        right' <- check right rightTy'
        return (left', right', t')

      -- Generator
      gen (leftTy' :| [rightTy']) = do
        x <- fresh
        return $
          lets'
            [(x, TBool PublicL, cond')]
            Ite {cond = V x, left = leftTy', right = rightTy'}
      gen _ = depBrOops

      -- Matcher
      match Ite {cond = condQ, left = leftQ, right = rightQ} = do
        equate cond' condQ
        return $ NE.fromList [leftQ, rightQ]
      match t = depMatchErr t

  (left', right', t') <-
    depType typeNoDep inferDep checkDep mt $ \(_, _, t) -> t
  x <- fresh
  secondF (let' x (TBool PublicL) cond') $
    mkLet'
      t'
      Ite
        { cond = V x,
          left = left',
          right = right'
        }
typing Pair {pairKind = pairKind@PsiP, ..} (Just t) = do
  (argTy, oadtName) <- isPsi t
  let app x = oadtName @@@ [V x]
  left' <- check left argTy
  xl <- fresh
  right' <- check right $ let' xl argTy left' $ app xl
  xr <- fresh
  secondF (lets' [(xl, argTy, left'), (xr, app xl, right')]) $
    mkLet' t Pair {left = V xl, right = V xr, ..}
typing Pair {pairKind, ..} mt | pairKind == OblivP || pairKind == PublicP = do
  (mLeftTy, mRightTy) <- NE.unzip <$> mapM (isProdLike pairKind) mt
  (leftTy', left') <- typing left mLeftTy
  (rightTy', right') <- typing right mRightTy
  when (pairKind == OblivP && isNothing mt) $ do
    oblivKinded leftTy'
    oblivKinded rightTy'
  xl <- fresh
  xr <- fresh
  secondF (lets' [(xl, leftTy', left'), (xr, rightTy', right')]) $
    mkLet'
      Prod
        { olabel = olabelOfPairKind pairKind,
          left = leftTy',
          right = rightTy'
        }
      Pair {left = V xl, right = V xr, ..}
typing PMatch {pairKind = pairKind@PublicP, ..} mt = do
  (condTy', cond') <- infer cond
  (leftTy', rightTy') <- withLoc_ cond $ isProd condTy'
  ((xl, xr), body) <- unbind2 bnd2

  let ctxs = NE.fromList [[]]
      argss =
        NE.fromList
          [ [ (xl, leftTy', lBinder),
              (xr, rightTy', rBinder)
            ]
          ]

      -- Typing without dependent types
      typeNoDep = do
        (bodyTy', body') <- typeBody mt
        -- @t'@ cannot refer to @xl@ or @xr@, otherwise it would be dependent
        -- type.
        notAppearIn bodyTy' $ head argss
        return (body', bodyTy')

      -- Infer a dependent type.
      inferDep = do
        (bodyTy', body') <- typeBody Nothing
        t' <- depGen gen ctxs argss (NE.fromList [bodyTy'])
        return (body', t')

      -- Check a dependent type.
      checkDep t' = do
        bodyTy' <-
          depMatch match ctxs argss t' >>= \case
            bodyTy' :| [] -> return bodyTy'
            _ -> depBrOops
        (_, body') <- typeBody (Just bodyTy')
        return (body', t')

      -- Generator
      gen (bodyTy' :| []) = do
        x <- fresh
        return $
          lets'
            [(x, condTy', cond')]
            PMatch
              { cond = V x,
                bnd2 = abstract_ (xl, xr) bodyTy',
                ..
              }
      gen _ = depBrOops

      -- Matcher
      match PMatch {pairKind = PublicP, cond = condQ, bnd2 = bnd2Q} = do
        equate cond' condQ
        return $ instantiateName (xl, xr) bnd2Q :| []
      match t = depMatchErr t

      -- Type check the body.
      typeBody mt' = extendCtx (head argss) $ typing body mt'

  (body', t') <- depType typeNoDep inferDep checkDep mt snd
  x <- fresh
  secondF
    (let' x Prod {olabel = PublicL, left = leftTy', right = rightTy'} cond')
    $ mkLet'
      t'
      PMatch
        { condTy = Nothing,
          cond = V x,
          bnd2 = abstract_ (xl, xr) body',
          ..
        }
typing PMatch {pairKind = pairKind@OblivP, ..} mt = do
  (t, cond') <- infer cond
  (leftTy', rightTy') <- withLoc_ cond $ isOProd t
  ((xl, xr), body) <- unbind2 bnd2
  let ctx = [(xl, leftTy', lBinder), (xr, rightTy', rBinder)]
  (bodyTy', body') <- extendCtx ctx $ typing body mt
  notAppearIn bodyTy' ctx
  let condTy' = Prod {olabel = OblivL, left = leftTy', right = rightTy'}
  x <- fresh
  secondF (let' x condTy' cond') $
    mkLet'
      bodyTy'
      PMatch
        { condTy = Just (leftTy', rightTy'),
          cond = V x,
          bnd2 = abstract_ (xl, xr) body',
          ..
        }
-- NOTE: Technically the type of a Psi type elimination can depend on the
-- discriminee, just like the public product elimination. But it does not seem
-- necessary in the current use of Psi type.
typing PMatch {pairKind = pairKind@PsiP, ..} mt = do
  (t, cond') <- infer cond
  (argTy, oadtName) <- withLoc_ cond $ isPsi t
  ((xl, xr), body) <- unbind2 bnd2
  let ctx = [(xl, argTy, lBinder), (xr, oadtName @@@ [V xl], rBinder)]
  (bodyTy', body') <- extendCtx ctx $ typing body mt
  notAppearIn bodyTy' ctx
  x <- fresh
  secondF (let' x t cond') $
    mkLet'
      bodyTy'
      PMatch
        { condTy = Nothing,
          cond = V x,
          bnd2 = abstract_ (xl, xr) body',
          ..
        }
typing Match {..} mt = do
  (condTy', cond') <- infer cond
  (ref, ctors) <- isMatchCond cond condTy'
  joinedAlts <- joinAlts alts ctors

  res <-
    forM joinedAlts $ \(ctor, paraTypes, binders, bnd) -> do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      return (ctor, body, zip3 xs paraTypes binders)

  let ctxs = joinedAlts $> []
      (ctorNames, bodies, argss) = NE.unzip3 res

      -- Typing without dependent types
      typeNoDep = do
        let (args0 :| argsRest) = argss
            (body0 :| bodyRest) = bodies
        (bodyTy', body0') <- typeAlt mt args0 body0
        (bodyTyRest', bodyRest') <-
          unzip <$> zipWithM (typeAlt (Just bodyTy')) argsRest bodyRest
        let bodyTs' = bodyTy' :| bodyTyRest'
            bodies' = body0' :| bodyRest'
        -- The type of each branch cannot refer to the pattern variables,
        -- otherwise it would be dependent type.
        NE.zipWithM_ notAppearIn bodyTs' argss
        return (bodies', bodyTy')

      -- Infer a dependent type.
      inferDep = do
        (bodyTs', bodies') <-
          NE.unzip <$> NE.zipWithM (typeAlt Nothing) argss bodies
        t' <- depGen gen ctxs argss bodyTs'
        return (bodies', t')

      -- Check a dependent type.
      checkDep t' = do
        bodyTs <- depMatch match ctxs argss t'
        (_, bodies') <-
          NE.unzip <$> NE.zipWith3M (typeAlt . Just) bodyTs argss bodies
        return (bodies', t')

      -- Generator
      gen bodyTs = do
        let tyAlts = NE.zipWith3 mkMatchAlt ctorNames argss bodyTs
        x <- fresh
        return $
          lets'
            [(x, condTy', cond')]
            Match {cond = V x, alts = tyAlts}

      -- Matcher
      match Match {cond = condQ, alts = altsQ} = do
        equate cond' condQ
        -- Because the input type is in core taype, the constructors are in the
        -- canonical order.
        return $
          NE.zipWith
            ( \args MatchAlt {bnd} ->
                let xs = [x | (x, _, _) <- args]
                 in instantiateName xs bnd
            )
            argss
            altsQ
      match t = depMatchErr t

      -- Type check an alternative.
      typeAlt mt' args body = extendCtx args $ typing body mt'

  (bodies', t') <- depType typeNoDep inferDep checkDep mt snd
  let alts' = NE.zipWith3 mkMatchAlt ctorNames argss bodies'
  x <- fresh
  secondF (let' x (GV ref) cond') $ mkLet' t' Match {cond = V x, alts = alts'}
  where
    mkMatchAlt ctor args body =
      let xs = [x | (x, _, _) <- args]
          binders = [binder | (_, _, binder) <- args]
       in MatchAlt {bnd = abstract_ xs body, ..}
typing OIte {..} mt = do
  cond' <- check cond $ TBool OblivL
  (t', left') <- typing left mt
  right' <- check right t'
  mkOIteExpr cond' left' right' t'
typing OInj {..} (Just t) = do
  (leftTy', rightTy') <- isOSum t
  let injTy' = if tag then leftTy' else rightTy'
  e' <- check expr injTy'
  x <- fresh
  secondF (let' x injTy' e') $
    mkLet' t OInj {injTy = Just (leftTy', rightTy'), expr = V x, ..}
typing OProj {..} Nothing = do
  (t, e') <- infer expr
  (leftTy', rightTy') <- withLoc_ expr $ isOSum t
  let t' = case projKind of
        TagP -> TBool OblivL
        LeftP -> leftTy'
        RightP -> rightTy'
  x <- fresh
  secondF (let' x t e') $
    mkLet' t' OProj {projTy = Just (leftTy', rightTy'), expr = V x, ..}
typing OMatch {..} mt = do
  (t, cond') <- infer cond
  (leftTy', rightTy') <- withLoc_ cond $ isOSum t
  (xl, lBody) <- unbind1 lBnd
  (xr, rBody) <- unbind1 rBnd
  (t', lBody') <-
    extendCtx1 xl leftTy' lBinder $
      typing lBody mt
  rBody' <-
    extendCtx1 xr rightTy' rBinder $
      check rBody t'
  x <- fresh
  let projTy = Just (leftTy', rightTy')
      condTy' = OSum {left = leftTy', right = rightTy'}
      expr = V x
  secondF
    ( lets'
        [ (x, condTy', cond'),
          (xl, leftTy', OProj {projKind = LeftP, ..}),
          (xr, rightTy', OProj {projKind = RightP, ..})
        ]
    )
    $ mkOIteExpr (OProj {projKind = TagP, ..}) lBody' rBody' t'
typing Arb {oblivTy = Nothing} (Just t) = do
  oblivKinded t
  mkLet' t Arb {oblivTy = Just t}
typing Ppx {..} Nothing = do
  get >>= \case
    PolyT _ ->
      err
        [ [ DD $
              "Preprocessors are not allowed"
                <+> "in polymorphic functions (OADT match instances) yet"
          ]
        ]
    MonoT -> pass
  ppx' <- biplateM kinded ppx
  t' <- typingPpx ppx'
  mkLet' t' Ppx {ppx = ppx'}
typing Loc {..} mt = withLoc loc $ withCur expr $ typing expr mt
typing Asc {..} Nothing = do
  ty' <- kinded ty
  e' <-
    if trustMe
      then do
        (infTy, e') <- infer expr
        equate_ infTy ty' `catchError` \_ ->
          warn
            [ [DD "Assumed type equivalence"],
              [DH "Inferred", DC infTy],
              [DH "Assumed", DC ty']
            ]
        return e'
      else check expr ty'
  return (ty', e')

-- Check type.
typing e (Just t) = do
  (t', e') <- infer e
  equate t t'
  return (t', e')

-- Failed to infer the type.
typing _ Nothing =
  err
    [ [DD "Could not infer the type"],
      [DD "Perhaps you should add some type annotations"]
    ]

mkOIteExpr ::
  Expr Name -> Expr Name -> Expr Name -> Ty Name -> TcM (Ty Name, Expr Name)
mkOIteExpr cond left right retTy = case retTy of
  TV {..} -> do
    checkPoly
    put $ PolyT MergeableC
    xl <- fresh
    xr <- fresh
    x <- fresh
    secondF
      ( lets'
          [ (x, TBool OblivL, cond),
            (xl, arrow_ TUnit TV {..}, thunk_ left),
            (xr, arrow_ TUnit TV {..}, thunk_ right)
          ]
      )
      $ mkLet' retTy (V uniqName @@ [V x, V xl, V xr])
  _ -> do
    let label = if isOblivKinded retTy then SafeL else LeakyL
    checkLabel label
    x <- fresh
    secondF (let' x (TBool OblivL) cond) $
      mkLet' retTy OIte {cond = V x, ..}

-- | Assemble the types of all branches in a dependent case-like expression into
-- a single well-kinded type.
--
-- This function is used in type inference mode for dependent case analysis,
-- conditional and pair elimination.
--
-- The first argument is a dependent expression generator, taking a list of
-- branch types. These branch types have to be well-kinded (under the context
-- extended with the second and third arguments) and in core taype ANF. The
-- generated dependent expression is also well-kinded and in core taype ANF.
--
-- The second argument is the extended contexts, one for each branch. It is used
-- to collect the variables arisen from pi-type. Types in this context are
-- well-kinded and in core taype ANF.
--
-- The third argument is the contexts of pattern variables, one for each branch.
-- The types are well-kinded and in core taype ANF.
--
-- The last argument is the list of branch types. They are well-kinded (under
-- the extended context) and in core taype ANF.
--
-- This function returns a single type that can type check the whole dependent
-- expression. It is also well-kinded and in core taype ANF.
depGen ::
  (NonEmpty (Ty Name) -> TcM (Ty Name)) ->
  NonEmpty [(Name, Ty Name, Maybe Binder)] ->
  NonEmpty [(Name, Ty Name, Maybe Binder)] ->
  NonEmpty (Ty Name) ->
  TcM (Ty Name)
-- Do not need to perform 'whnf' or strip 'Loc' for product and pi-types,
-- because they are not oblivious types, and @bodyTy0@ is in core taype ANF.
depGen gen ctxs argss branchTs@(Prod {olabel = olabel@PublicL} :| _) = do
  (leftTs, rightTs) <- NE.unzip <$> mapM isProd branchTs
  left <- depGen gen ctxs argss leftTs
  right <- depGen gen ctxs argss rightTs
  return Prod {..}
depGen gen ctxs argss branchTs@(Pi {binder} :| _) = do
  res <- mapM isPi branchTs
  let (argTs, _, bnds) = NE.unzip3 res
  x <- fresh
  argTy <- depGen gen ctxs argss argTs
  let bodies = instantiateName x <$> bnds
      ctxs' =
        NE.zipWith
          (\(ty, b, _) ctx -> (x, ty, b) : ctx)
          res
          ctxs
  body <- depGen gen ctxs' argss bodies
  return Pi {ty = argTy, bnd = abstract_ x body, ..}
depGen gen ctxs argss branchTs = genSingle `catchError` const genDep
  where
    genSingle = do
      equateSome branchTs
      NE.zipWithM_ notAppearIn branchTs argss
      return $ head branchTs
    genDep = do
      NE.zipWith3M_ goDep branchTs ctxs argss
      gen branchTs
    goDep t ctx args = extendCtx ctx $ extendCtx args $ checkKind t OblivK

-- | Dissemble a single type into a list of types for all branches in a
-- dependent case-like expression.
--
-- This function is used in type checking mode for dependent case analysis,
-- conditional and pair elimination.
--
-- The first argument is a matcher that matches the input type with the
-- dependent expression and returns a list of branch types. The input type must
-- be well-kinded (in the extended context) and in core taype WHNF. The output
-- list of types do not need to be in core taype, WHNF or ANF.
--
-- The second argument is the extended contexts, similar to the one for
-- 'depGen'.
--
-- The third argument is the contexts of pattern variables, similar to the one
-- for 'depGen'.
--
-- The last argument is the type given to check. It must be well-kinded and in
-- core taype ANF.
--
-- This function returns a list of branch types, ready for checking each branch
-- in the dependent expression. They are well-kinded and in core taype ANF.
depMatch ::
  (Ty Name -> TcM (NonEmpty (Ty Name))) ->
  NonEmpty [(Name, Ty Name, Maybe Binder)] ->
  NonEmpty [(Name, Ty Name, Maybe Binder)] ->
  Ty Name ->
  TcM (NonEmpty (Ty Name))
-- Similar to 'depGen', do not need to perform 'whnf' or strip 'Loc' for
-- product and pi-types.
depMatch match ctxs argss Prod {olabel = PublicL, ..} = do
  leftTs <- depMatch match ctxs argss left
  rightTs <- depMatch match ctxs argss right
  return $ NE.zipWith (Prod PublicL) leftTs rightTs
depMatch match ctxs argss Pi {..} = do
  argTs <- depMatch match ctxs argss ty
  (x, body) <- unbind1 bnd
  let ctxs' =
        NE.zipWith
          (\argTy ctx -> (x, argTy, binder) : ctx)
          argTs
          ctxs
  bodies <- depMatch match ctxs' argss body
  return $
    NE.zipWith
      ( \argTy body' ->
          Pi
            { ty = argTy,
              bnd = abstract_ x body',
              ..
            }
      )
      argTs
      bodies
depMatch match ctxs argss ty = do
  matchDep `catchError` const (return $ argss $> ty)
  where
    matchDep = do
      nf <- whnf_ ty
      branchTs <- match nf
      NE.zipWith3M goDep branchTs ctxs argss
    goDep t ctx args = extendCtx ctx $ extendCtx args $ kinded t

-- | Type check an expression by first trying nondependent checker and then
-- dependent checkers.
--
-- The first argument types an expression without dependent types.
--
-- The second argument infers the dependent type of an expression.
--
-- The third argument checks the dependent type of an expression.
--
-- The fourth argument indicates if it is in inference mode or checking mode.
--
-- The last argument is a projection function that extracts the type of the
-- whole expression. This type must be in core taype.
depType ::
  TcM a ->
  TcM a ->
  (Ty Name -> TcM a) ->
  Maybe (Ty Name) ->
  (a -> Ty Name) ->
  TcM a
depType typeNoDep inferDep checkDep mt proj =
  typeNoDep `catchError` \noDepErr ->
    case mt of
      Just t ->
        checkDep t `catchError` \checkErr ->
          ( do
              a <- inferDep
              equate t (proj a)
              return a
          )
            `catchError` \_ -> throwError checkErr
      _ -> inferDep `catchError` \_ -> throwError noDepErr

-- | Infer the type of an expression.
infer :: Expr Name -> TcM (Ty Name, Expr Name)
infer e = typing e Nothing

-- | Check the type of an expression.
check :: Expr Name -> Ty Name -> TcM (Expr Name)
check e t = typing e (Just t) <&> snd

checkArity :: AppKind -> Text -> [b] -> [c] -> TcM ()
checkArity appKind ref args paraTypes =
  let m = length args
      n = length paraTypes
   in unless (m == n) $ errArity appKind ref m n

-- | Kind check a type bidirectionally.
--
-- It is in inference mode if the second argument is 'Nothing', otherwise in
-- checking mode. This function returns the type's kind and its full
-- elaboration.
--
-- The returned kind must be the same as the given kind if in checking mode.
--
-- The returned type must be in core taype ANF. Of course, it must also be
-- kinded by the returned kind.
kinding :: Ty Name -> Maybe Kind -> TcM (Kind, Ty Name)
kinding TUnit Nothing = return (AnyK, TUnit)
kinding ty@TBool {..} Nothing = return (kindOfOLabel olabel, ty)
kinding ty@TInt {..} Nothing = return (kindOfOLabel olabel, ty)
kinding ty@GV {..} Nothing =
  lookupGSig ref >>= \case
    Just ADTDef {} -> return (PublicK, ty)
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not an ADT"]]
    _ ->
      err [[DD "Type", DQ ref, DD "is not in scope"]]
kinding Psi {oadtName} Nothing = do
  lookupGSig oadtName >>= \case
    Just OADTDef {..} -> return (MixedK, Psi {viewTy = Just viewTy, ..})
    Just _ -> err [[DD "Definition", DQ oadtName, DD "is not an OADT"]]
    _ -> err [[DD "Definition", DQ oadtName, DD "is not in scope"]]
kinding Prod {olabel = olabel@PublicL, ..} Nothing = do
  (leftK, left') <- inferKind left
  (rightK, right') <- inferKind right
  return (leftK \/ rightK \/ PublicK, Prod {left = left', right = right', ..})
kinding Prod {olabel = olabel@OblivL, ..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, Prod {left = left', right = right', ..})
kinding OSum {..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, OSum {left = left', right = right'})
kinding Pi {..} Nothing = do
  ty' <- kinded ty
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x ty' binder $ kinded body
  return (MixedK, Pi {ty = ty', bnd = abstract_ x body', ..})
kinding App {..} Nothing = do
  (ref, argTy) <-
    maybeGV fn >>= \case
      Just (ref, OADTDef {..}) -> return (ref, viewTy)
      Just (ref, _) ->
        err [[DD "Definition", DQ ref, DD "is not an oblivious ADT"]]
      _ -> err [[DH "Not an oblivious ADT or not in scope", DC fn]]
  -- Currently we only support a single argument for OADTs.
  arg <- case args of
    [arg] -> return arg
    _ -> errArity TypeApp ref (length args) 1
  arg' <- check arg argTy
  x <- fresh
  return
    ( OblivK,
      lets'
        [(x, argTy, arg')]
        (ref @@@ [V x])
    )
kinding Let {..} Nothing = do
  mt <- mapM kinded rhsTy
  (rhsTy', rhs') <- typing rhs mt
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x rhsTy' binder $ checkKind body OblivK
  return
    ( OblivK,
      Let
        { rhsTy = Just rhsTy',
          rhs = rhs',
          bnd = abstract_ x body',
          ..
        }
    )
kinding Ite {..} Nothing = do
  cond' <- check cond $ TBool PublicL
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  x <- fresh
  return
    ( OblivK,
      lets'
        [(x, TBool PublicL, cond')]
        Ite {cond = V x, left = left', right = right'}
    )
kinding PMatch {pairKind = pairKind@PublicP, ..} Nothing = do
  (condTy', cond') <- infer cond
  (leftTy', rightTy') <- withLoc_ cond $ isProd condTy'
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCtx [(xl, leftTy', lBinder), (xr, rightTy', rBinder)] $
      checkKind body OblivK
  x <- fresh
  return
    ( OblivK,
      lets'
        [(x, Prod {olabel = PublicL, left = leftTy', right = rightTy'}, cond')]
        PMatch {cond = V x, bnd2 = abstract_ (xl, xr) body', ..}
    )
kinding Match {..} Nothing = do
  (condTy', cond') <- infer cond
  (ref, ctors) <- isMatchCond cond condTy'
  joinedAlts <- joinAlts alts ctors
  alts' <- mapM kindMatchAlt joinedAlts
  x <- fresh
  return
    ( OblivK,
      lets'
        [(x, GV ref, cond')]
        Match {cond = V x, alts = alts'}
    )
  where
    -- Kind check an alternative.
    kindMatchAlt (ctor, paraTypes, binders, bnd) = do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      body' <-
        extendCtx (zip3 xs paraTypes binders) $
          checkKind body OblivK
      return MatchAlt {bnd = abstract_ xs body', ..}
kinding Loc {..} mk = withLoc loc $ withCur expr $ kinding expr mk
kinding TV {..} Nothing = do
  checkPoly
  return (MixedK, TV {..})
-- Check kind.
kinding t (Just k) = do
  (k', t') <- inferKind t
  unless (k' `leq` k) $
    err
      [ [DH "Could not match kind", DC t],
        [DH "Expected", DC k'],
        [DH "Got", DC k]
      ]
  return (k, t')

-- Failed to infer kind.
kinding _ Nothing =
  err
    [ [DD "Could not infer the kind"],
      [DD "Are you sure this is a type?"]
    ]

-- | Infer the kind of a type.
inferKind :: Ty Name -> TcM (Kind, Ty Name)
inferKind t = kinding t Nothing

-- | Check the kind of a type.
checkKind :: Ty Name -> Kind -> TcM (Ty Name)
checkKind t k = kinding t (Just k) <&> snd

-- | Make sure a type is kinded, but do not care what the kind is.
kinded :: Ty Name -> TcM (Ty Name)
kinded t = inferKind t <&> snd

-- | Type check and elaborate a preprocessor.
--
-- The type parameters of the preprocessors must be well-kinded and in core
-- Taype ANF.
--
-- The returned type and elaborated expressions are well-kinded / well-typed and
-- in core Taype. However, they are not in ANF.
--
-- In addition, the elaborated expressions must no longer contain any
-- preprocessors.
processPpx :: LCtx Name -> Ppx Name -> TcM (Ty Name, Expr Name)
processPpx ctx = go
  where
    go ItePpx {..} = do
      let t' = typeOfItePpx condTy retTy
      case condTy of
        TBool {olabel = PublicL} -> do
          b <- fresh
          f1 <- fresh
          f2 <- fresh
          let e' =
                mkLam b f1 f2 condTy retTy $
                  ite_ (V b) (V f1 @@ [VUnit]) (V f2 @@ [VUnit])
          return (t', e')
        TBool {olabel = OblivL} -> do
          e' <- goOIte retTy
          return (t', e')
        _ -> errFst "condition" (TBool PublicL) condTy
    go CtorPpx {..} =
      lookupGSig ctor >>= \case
        Just CtorDef {..} -> case retTy of
          GV {..} -> do
            unless (ref == dataType) $
              err
                [ [ DC ctor,
                    DD "is not a constructor of",
                    DC ref
                  ]
                ]
            let argTy = prod_ paraTypes
                t' = arrow_ argTy retTy
            xs <- freshes $ length paraTypes
            let xts = zipWith (\x t -> (x, Nothing, t)) xs paraTypes
            e' <- lamP xts $ GV ctor @@ (V <$> xs)
            return (t', e')
          Psi {..} ->
            resolveCtor ctor oadtName >>= \case
              Just (x, ty) -> return (ty, GV x)
              _ ->
                err
                  [ [ DD "Constructor instance",
                      DC ctor,
                      DD "of OADT",
                      DC oadtName,
                      DD "is missing"
                    ]
                  ]
          _ -> err [[DD "The type argument is not an ADT or Psi type"]]
        _ -> err [[DC ctor, DD "is not a constructor"]]
    go BuiltinPpx {..} =
      lookupGSig fn >>= \case
        Just BuiltinDef {..}
          | arrows_ paraTypes resType == ty ->
              return (ty, GV fn)
        Just BuiltinDef {} ->
          lookupGSig (oblivName fn) >>= \case
            Just BuiltinDef {..}
              | arrows_ paraTypes resType == ty ->
                  return (ty, GV (oblivName fn))
            _ -> err [[DD "Cannot resolve builtin operation"]]
        _ -> err [[DC fn, DD "is not a builtin operation"]]
    go MatchPpx {..} = case condTy of
      GV {..} ->
        lookupGSig ref >>= \case
          Just ADTDef {..} -> goMatch ref (toList ctors) retTy
          _ -> oops "Not an ADT"
      Psi {..} -> do
        resolveMatch oadtName >>= \case
          Just (x, t, c) -> goMatchPsi x t c retTy
          _ ->
            err
              [ [ DD "Match instance of OADT",
                  DC oadtName,
                  DD "is missing"
                ]
              ]
      _ ->
        err
          [ [ DD "The first type argument (discriminee)",
              DD "is not an ADT or Psi type"
            ]
          ]
    go CoercePpx {..} = do
      let t' = arrow_ fromTy toTy
      e' <- goCoerce fromTy toTy
      return (t', e')
    go LiftPpx {..} =
      case lookupLCtx fn ty ctx of
        Just name -> return (ty, GV name)
        _ ->
          lookupGSig fn >>= \case
            Just FunDef {ty = ty', ..} -> do
              unlessM (compatible ty ty') $
                err
                  [ [ DD "The lifting type is not compatible with",
                      DD $ "the type of function" <+> pretty fn
                    ],
                    [DH "Expected a type compatible with", DC ty'],
                    [DH "Got", DC ty]
                  ]
              unless (attr == NotAnInst) $
                err [[DD "Do not support lifting instances"]]
              unless (poly == MonoT) $
                err [[DD "Do not support lifting polymorphic functions"]]
              unless (label == SafeL) $
                err [[DD "Do not support lifting leaky functions"]]
              return (ty, oops "Lifting instance not available")
            _ ->
              err
                [ [ DD $
                      "Definition"
                        <+> pretty fn
                        <+> "is not in scope or not a function"
                  ]
                ]

    mkLam b f1 f2 condTy retTy =
      lams'
        [ (b, condTy),
          (f1, arrow_ TUnit retTy),
          (f2, arrow_ TUnit retTy)
        ]
    goOIte ty = do
      b <- fresh
      f1 <- fresh
      f2 <- fresh
      body <- goOIte_ b f1 f2 ty
      return $ mkLam b f1 f2 (TBool OblivL) ty body
    goOIte_ b f1 f2 = \case
      Psi {..} -> do
        (joinName, reshapeName) <-
          resolveJoin oadtName >>= \case
            Just p -> return p
            _ ->
              err
                [ [ DD $
                      pretty oadtName
                        <+> "does not have join and reshape instances"
                  ]
                ]
        k1 <- fresh
        k2 <- fresh
        k <- fresh
        x1 <- fresh
        x2 <- fresh
        return $
          pmatch' PsiP (V f1 @@ [VUnit]) k1 x1 $
            pmatch' PsiP (V f2 @@ [VUnit]) k2 x2 $
              let' k (fromJust viewTy) (GV joinName @@ [V k1, V k2]) $
                Pair
                  { pairKind = PsiP,
                    left = V k,
                    right =
                      mux_
                        (V b)
                        (GV reshapeName @@ [V k1, V k, V x1])
                        (GV reshapeName @@ [V k2, V k, V x2])
                  }
      Prod {olabel = PublicL, ..} -> do
        lIte <- goOIte left
        rIte <- goOIte right
        xl1 <- fresh
        xl2 <- fresh
        xr1 <- fresh
        xr2 <- fresh
        return $
          pmatch' PublicP (V f1 @@ [VUnit]) xl1 xr1 $
            pmatch' PublicP (V f2 @@ [VUnit]) xl2 xr2 $
              Pair
                { pairKind = PublicP,
                  left =
                    lIte
                      @@ [ V b,
                           thunk_ (V xl1),
                           thunk_ (V xl2)
                         ],
                  right =
                    rIte
                      @@ [ V b,
                           thunk_ (V xr1),
                           thunk_ (V xr2)
                         ]
                }
      ty@Pi {} -> case isArrow ty of
        Just (argTs, retTy) -> do
          rIte <- goOIte retTy
          xs <- freshes $ length argTs
          return $
            lams' (zip xs argTs) $
              rIte
                @@ [ V b,
                     thunk_ $ V f1 @@ (VUnit : (V <$> xs)),
                     thunk_ $ V f2 @@ (VUnit : (V <$> xs))
                   ]
        _ -> errSnd "cannot be a dependent type" ty
      ty | isOblivKinded ty -> do
        return $ mux_ (V b) (V f1 @@ [VUnit]) (V f2 @@ [VUnit])
      ty -> errSnd "is not mergeable" ty

    goMatch adtName ctors retTy = do
      let altTs = ctors <&> \(_, ts) -> arrow_ (prod_ ts) retTy
          t' = arrows_ (GV adtName : altTs) retTy
      x <- fresh
      as <- freshes (length ctors)
      alts <- zipWithM goAlt as ctors
      let e' =
            lams' ((x, GV adtName) : zip as altTs) $
              match' (V x) (fromList alts)
      return (t', e')
      where
        goAlt x (ctor, paraTypes) = do
          xs <- freshes (length paraTypes)
          return (ctor, xs, V x @@ [tuple_ (V <$> xs)])

    goMatchPsi name ty constraint retTy = case constraint of
      UnrestrictedC -> do
        t' <- substTV ty
        return (t', GV name)
      MergeableC -> do
        -- The first argument is an if preprocessor.
        (_, ite) <- go ItePpx {condTy = TBool OblivL, ..}
        t' <- substTV $ snd $ fromJust $ isArrow1 ty
        return (t', GV name @@ [ite])
      where
        substTV = transformM $ \case
          TV 0 -> return retTy
          e -> return e

    goCoerce t t' | t == t' = do
      x <- fresh
      return $ lam' x t (V x)
    goCoerce Psi {oadtName} Psi {oadtName = oadtName'} =
      resolveCoerce oadtName oadtName' >>= \case
        Just name -> return $ GV name
        _ ->
          err
            [ [ DD "Coerce instance from",
                DC oadtName,
                DD "to",
                DC oadtName',
                DD "is missing"
              ]
            ]
    goCoerce from@GV {..} Psi {..} = do
      pubName <- pubNameOfOADTName oadtName
      unless (pubName == ref) $
        err
          [ [ DC pubName,
              DD "is not the public ADT of OADT",
              DC oadtName
            ]
          ]
      view <-
        resolveView oadtName >>= \case
          Just name -> return $ GV name
          _ -> err [[DD "View instance of", DC oadtName, DD "is missing"]]
      x <- fresh
      k <- fresh
      return $
        lam' x from $
          let' k (fromJust viewTy) (view @@ [V x]) $
            Pair
              { pairKind = PsiP,
                left = V k,
                right = GV (sectionName oadtName) @@ [V k, V x]
              }
    goCoerce (TBool PublicL) (TBool OblivL) = do
      x <- fresh
      return $
        lam' x (TBool PublicL) $
          GV (sectionName (oblivName "bool")) @@ [V x]
    goCoerce (TInt PublicL) (TInt OblivL) = do
      x <- fresh
      return $
        lam' x (TInt PublicL) $
          GV (sectionName (oblivName "int")) @@ [V x]
    goCoerce
      from@Prod {olabel = PublicL, left, right}
      Prod {olabel = PublicL, left = left', right = right'} = do
        lCoer <- goCoerce left left'
        rCoer <- goCoerce right right'
        p <- fresh
        xl <- fresh
        xr <- fresh
        return $
          lam' p from $
            pmatch' PublicP (V p) xl xr $
              Pair
                { pairKind = PublicP,
                  left = lCoer @@ [V xl],
                  right = rCoer @@ [V xr]
                }
    goCoerce from@Pi {} to@Pi {} = case (isArrow from, isArrow to) of
      (Just (argTs, retTy), Just (argTs', retTy')) ->
        if length argTs == length argTs'
          then do
            rCoer <- goCoerce retTy retTy'
            -- Contravariant
            aCoer <- zipWithM goCoerce argTs' argTs
            f <- fresh
            xs <- freshes $ length argTs
            return $
              lams' ((f, from) : zip xs argTs') $
                rCoer @@ [V f @@ zipWith (\c x -> c @@ [V x]) aCoer xs]
          else
            err
              [ [ DD
                    "Coercing between functions with \
                    \different number of arguments"
                ]
              ]
      _ -> err [[DD "Type arguments to coercion cannot be dependent types"]]
    goCoerce _ _ = err [[DD "Cannot resolve coercion"]]

    errFst :: Doc -> Ty Name -> Ty Name -> TcM a
    errFst what ty ty' =
      err
        [ [ DH $
              "The first type argument"
                <+> parens what
                <+> "is not compatible with",
            DC ty
          ],
          [DH "Got", DC ty']
        ]
    errSnd :: Doc -> Ty Name -> TcM a
    errSnd wrong ty' =
      err
        [ [ DD $
              "The second type argument (return type)" <+> wrong
          ],
          [DH "Got", DC ty']
        ]

typingPpx :: Ppx Name -> TcM (Ty Name)
typingPpx ppx = fst <$> processPpx [] ppx

elabPpx :: LCtx Name -> Ppx Name -> TcM (Expr Name)
elabPpx ctx ppx = snd <$> processPpx ctx ppx

-- | Elaborate all preprocessors in the definitions.
--
-- Although this function returns an exception monad, it should not fail if the
-- definitions are well-typed.
--
-- All polymorphic definitions are removed, as they are inlined and cannot be
-- handled further.
elabPpxDefs :: Options -> GCtx Name -> Defs Name -> ExceptT Err IO (Defs Name)
elabPpxDefs options gctx defs =
  forM defs $ \(name, def) ->
    (name,)
      <$> runTcM
        (initEnv options name gctx gctx)
        (transformBiM go def)
  where
    go Ppx {..} = elabPpx ctx ppx
    go e = return e
    ctx = makeLCtx defs

typeOfItePpx :: Ty Name -> Ty Name -> Ty Name
typeOfItePpx condTy retTy =
  arrows_ [condTy, arrow_ TUnit retTy, arrow_ TUnit retTy] retTy

----------------------------------------------------------------
-- OADT instance resolution

resolve1 :: (MonadReader Env m) => Text -> Text -> m (Maybe (Text, Ty Name))
resolve1 inst oadtName =
  let name = instName1 oadtName inst
   in lookupGSig name >>= \case
        Just FunDef {..} -> return $ Just (name, ty)
        _ -> return Nothing

resolve1' :: (MonadReader Env m) => Text -> Text -> m (Maybe Text)
resolve1' inst oadtName = fst <<$>> resolve1 inst oadtName

resolveCtor :: (MonadReader Env m) => Text -> Text -> m (Maybe (Text, Ty Name))
resolveCtor = resolve1

resolveMatch ::
  (MonadReader Env m) =>
  Text ->
  m (Maybe (Text, Ty Name, PolyConstraint))
resolveMatch oadtName =
  let name = instName1 oadtName "match"
   in -- NOTE: we have to look up match instance in the definition context but
      -- not the signature context, because the correct polymorphism attribute
      -- is only available in definition context. As a result, match instances
      -- have to be defined before their uses.
      lookupGDef name >>= \case
        Just FunDef {..} ->
          case poly of
            PolyT c -> return $ Just (name, ty, c)
            MonoT -> oops "Monomorphic match"
        _ -> return Nothing

resolveJoin :: (MonadReader Env m) => Text -> m (Maybe (Text, Text))
resolveJoin oadtName = do
  joinName <- resolve1' "join" oadtName
  reshapeName <- resolve1' "reshape" oadtName
  return $ (,) <$> joinName <*> reshapeName

resolveCoerce :: (MonadReader Env m) => Text -> Text -> m (Maybe Text)
resolveCoerce from to =
  let name = instName2 from to "coerce"
   in (name <$) <$> lookupGSig name

resolveView :: (MonadReader Env m) => Text -> m (Maybe Text)
resolveView = resolve1' "view"

----------------------------------------------------------------
-- Equality check

-- | Check the equivalence of two expressions.
--
-- They must be already well-kinded or well-typed, and in core taype.
equate :: Expr Name -> Expr Name -> TcM ()
equate e e' =
  equate_ e e' `catchError` \_ ->
    err
      [ [DD "Could not match types"],
        [DH "Expected", DC e],
        [DH "Got", DC e']
      ]

-- | Check the equivalence of two expressions.
--
-- They must be already well-kinded or well-typed, and in core taype.
equate_ :: Expr Name -> Expr Name -> TcM ()
equate_ e e' | e == e' = pass
equate_ e e' = do
  nf <- whnf e
  nf' <- whnf e'
  go nf nf'
  where
    go nf@GV {} nf' = equateGV nf nf'
    go nf nf'@GV {} = equateGV nf nf'
    go nf@App {} nf' = equateApp nf nf'
    go nf nf'@App {} = equateApp nf nf'
    go Pi {ty, bnd} Pi {ty = ty', bnd = bnd'} = do
      equate_ ty ty'
      (_, body, body') <- unbind1With bnd bnd'
      equate_ body body'
    go Lam {bnd} Lam {bnd = bnd'} = do
      (_, body, body') <- unbind1With bnd bnd'
      equate_ body body'
    go Let {rhs, bnd} Let {rhs = rhs', bnd = bnd'} = do
      equate_ rhs rhs'
      (_, body, body') <- unbind1With bnd bnd'
      equate_ body body'
    go
      Ite {cond, left, right}
      Ite {cond = cond', left = left', right = right'} = do
        equate_ cond cond'
        equate_ left left'
        equate_ right right'
    go Match {cond, alts} Match {cond = cond', alts = alts'}
      | length alts == length alts' = do
          equate_ cond cond'
          -- Since both match expressions are in core taype, the alternatives are
          -- in canonical order.
          NE.zipWithM_ goAlt alts alts'
      where
        goAlt
          MatchAlt {ctor, binders, bnd}
          MatchAlt {ctor = ctor', binders = binders', bnd = bnd'}
            | ctor == ctor' && length binders == length binders' = do
                let n = length binders
                (_, body, body') <- unbindManyWith n bnd bnd'
                equate_ body body'
        goAlt _ _ = errDummy
    go
      OIte {cond, left, right}
      OIte {cond = cond', left = left', right = right'} = do
        equate_ cond cond'
        equate_ left left'
        equate_ right right'
    go
      Prod {olabel, left, right}
      Prod {olabel = olabel', left = left', right = right'}
        | olabel == olabel' = do
            equate_ left left'
            equate_ right right'
    go
      Pair {pairKind, left, right}
      Pair {pairKind = pairKind', left = left', right = right'}
        | pairKind == pairKind' = do
            equate_ left left'
            equate_ right right'
    go
      PMatch {pairKind, cond, bnd2}
      PMatch {pairKind = pairKind', cond = cond', bnd2 = bnd2'}
        | pairKind == pairKind' = do
            equate_ cond cond'
            (_, body, body') <- unbind2With bnd2 bnd2'
            equate_ body body'
    go OSum {left, right} OSum {left = left', right = right'} = do
      equate_ left left'
      equate_ right right'
    go OInj {tag, expr} OInj {tag = tag', expr = expr'}
      | tag == tag' = equate_ expr expr'
    go OProj {projKind, expr} OProj {projKind = projKind', expr = expr'}
      | projKind == projKind' = equate_ expr expr'
    go nf nf' | nf == nf' = pass
    go _ _ = errDummy

    -- Equate two expressions with at least one being global variable.
    equateGV nf nf' | nf == nf' = pass
    equateGV nf nf' =
      tryUnfold nf >>= \case
        Just expr -> equate_ expr nf'
        _ ->
          tryUnfold nf' >>= \case
            Just expr' -> equate_ nf expr'
            _ -> errDummy

    -- Equate two expressions with at least one being application.
    equateApp :: Expr Name -> Expr Name -> TcM ()
    equateApp nf nf' = do
      equateApp_ nf nf' `catchError` \_ ->
        tryUnfoldApp nf >>= \case
          Just expr -> equate_ expr nf'
          _ ->
            tryUnfoldApp nf' >>= \case
              Just expr' -> equate_ nf expr'
              _ -> errDummy

    equateApp_ App {fn, args} App {fn = fn', args = args'}
      | length args == length args' = do
          equate_ fn fn'
          zipWithM_ equate_ args args'
    equateApp_ _ _ = errDummy

equateSome :: NonEmpty (Expr Name) -> TcM ()
equateSome (e :| es) = forM_ es $ equate e

tryUnfold :: Expr Name -> TcM (Maybe (Expr Name))
tryUnfold GV {..} =
  lookupGDef ref >>= \case
    Just FunDef {..} -> return $ Just expr
    _ -> return Nothing
tryUnfold _ = return Nothing

tryUnfoldApp :: Expr Name -> TcM (Maybe (Expr Name))
tryUnfoldApp App {..} = case fn of
  GV {..} ->
    lookupGDef ref >>= \case
      Just FunDef {..} -> return $ Just App {fn = expr, ..}
      Just OADTDef {..} -> return $
        case args of
          [arg] -> Just $ instantiate_ arg bnd
          _ -> Nothing
      _ -> return Nothing
  _ -> return Nothing
tryUnfoldApp _ = return Nothing

-- | Weak head normal form
--
-- This function never fails. It also never unfolds global definitions.
--
-- The expression is not necessarily in core taype. However, this property is
-- preserved, i.e. if the input expression is in core taype, the output is in
-- core taype too.
whnf :: Expr Name -> TcM (Expr Name)
whnf App {args = [], ..} = whnf fn
whnf App {args = args@(arg : args'), ..} = do
  nf <- whnf fn
  case nf of
    Lam {..} ->
      whnf App {fn = instantiate_ arg bnd, args = args', ..}
    App {fn = nfN, args = argsN} ->
      return App {fn = nfN, args = argsN <> args, ..}
    _ -> return App {fn = nf, ..}
whnf Let {..} = whnf $ instantiate_ rhs bnd
whnf Ite {..} = do
  nf <- whnf cond
  case nf of
    BLit {..} -> if bLit then whnf left else whnf right
    _ -> return Ite {cond = nf, ..}
whnf Match {..} = do
  nf <- whnf cond
  let fb = Match {cond = nf, ..}
  case nf of
    App {fn = GV {..}, ..} -> go ref args fb
    GV {..} -> go ref [] fb
    _ -> return fb
  where
    go ref args fb =
      case find (\MatchAlt {..} -> ctor == ref) alts of
        Just MatchAlt {ctor = _, ..}
          | length binders == length args ->
              whnf $ instantiate_ args bnd
        _ -> return fb
whnf PMatch {..} = do
  nf <- whnf cond
  case nf of
    Pair {pairKind = pairKind', ..}
      | pairKind == pairKind' ->
          whnf $ instantiate_ (left, right) bnd2
    _ -> return PMatch {cond = nf, ..}
whnf Loc {..} = whnf expr
whnf Asc {..} = whnf expr
whnf e = return e

-- | Weak head normal form but also unfold global definitions
--
-- The result is still technically in weak head normal form.
whnf_ :: Expr Name -> TcM (Expr Name)
whnf_ e = do
  nf <- whnf e
  tryUnfold nf >>= \case
    Just e' -> whnf_ e'
    _ ->
      tryUnfoldApp nf >>= \case
        Just e' -> whnf_ e'
        _ -> return nf

----------------------------------------------------------------
-- Helper functions

kindOfOLabel :: OLabel -> Kind
kindOfOLabel PublicL = PublicK
kindOfOLabel OblivL = OblivK

maybeGV :: (MonadReader Env m) => Expr Name -> m (Maybe (NamedDef Name))
maybeGV GV {..} = (ref,) <<$>> lookupGSig ref
maybeGV Loc {..} = maybeGV expr
maybeGV _ = return Nothing

checkDefLabel :: Int -> Text -> LLabel -> LLabel -> TcM ()
checkDefLabel loc name l l' = do
  when (l < l') $
    err_ loc $
      "Definition" <+> pretty name <+> "cannot be" <+> show l'

checkLabel :: LLabel -> TcM ()
checkLabel l' = do
  Env {..} <- ask
  when (label < l') $
    err
      [ [DD $ "Used a" <+> show l' <+> "expression"],
        [ DD $
            "But the definition" <+> pretty defName <+> "cannot be" <+> show l'
        ]
      ]

checkPoly :: TcM ()
checkPoly =
  get >>= \case
    PolyT _ -> pass
    MonoT -> do
      defName <- asks defName
      err
        [ [DD $ "Type polymorphism is not allowed in function" <+> pretty defName],
          [DD "Only OADT match instances can be polymorphic at the moment"]
        ]

-- | Check if a type is a pi-type and return its components.
--
-- Unlike other dependent type theory, we do not perform weak head normalization
-- here because it is unnecessary in our case: dependent types can only be
-- kinded as oblivious while pi-type is kinded as mixed. On the other hand, if
-- the given type is in core taype ANF, the returned types are also in core
-- taype ANF.
isPi :: Ty Name -> TcM (Ty Name, Maybe Binder, Scope () Ty Name)
isPi Pi {..} = return (ty, binder, bnd)
isPi Loc {..} = isPi expr
isPi t =
  err
    [ [DD "Expecting a function"],
      [DH "But instead got", DC t]
    ]

-- | Check if a type is a product type and return its components.
--
-- Similar to 'isPi', product types are never oblivious types, so weak head
-- normalization is unnecessary. The returned types are in core taype ANF if the
-- given type is so.
isProd :: Ty Name -> TcM (Ty Name, Ty Name)
isProd Prod {olabel = PublicL, ..} = return (left, right)
isProd Loc {..} = isProd expr
isProd t =
  err
    [ [DD "Expecting a pair"],
      [DH "But instead got", DC t]
    ]

-- | Check if a type is an oblivious product type and return its components.
--
-- The returned types are in core Taype ANF if the given type is in core Taype.
-- Unfortunately sometimes this introduces unnecesary kinding.
isOProd :: Ty Name -> TcM (Ty Name, Ty Name)
isOProd t = do
  (leftTy, rightTy) <- isOProd_ t
  leftTy' <- checkKind leftTy OblivK
  rightTy' <- checkKind rightTy OblivK
  return (leftTy', rightTy')

-- | Check if a type is an oblivious product type and return its components.
--
-- The return types are not necessarily in ANF.
isOProd_ :: Ty Name -> TcM (Ty Name, Ty Name)
isOProd_ t = do
  nf <- whnf_ t
  case nf of
    Prod {olabel = OblivL, ..} -> return (left, right)
    _ ->
      err
        [ [DD "Expecting an oblivious product"],
          [DH "But instead got", DC t]
        ]

-- | Check if a type is a Psi type and return its components.
isPsi :: Ty Name -> TcM (Ty Name, Text)
isPsi Psi {..} = return (fromJust viewTy, oadtName)
isPsi Loc {..} = isPsi expr
isPsi t =
  err
    [ [DD "Expecting a dependent pair (Psi type)"],
      [DH "But instead got", DC t]
    ]

-- | Check if a type is product-like and return its components.
isProdLike :: PairKind -> Ty Name -> TcM (Ty Name, Ty Name)
isProdLike PublicP = isProd
isProdLike OblivP = isOProd
isProdLike _ = oops "Psi type"

-- | Check if a type is an oblivious sum type and return its components.
--
-- The returned types are in core Taype ANF if the given type is in core Taype.
-- Unfortunately sometimes this introduces unnecesary kinding.
isOSum :: Ty Name -> TcM (Ty Name, Ty Name)
isOSum t = do
  (leftTy, rightTy) <- isOSum_ t
  leftTy' <- checkKind leftTy OblivK
  rightTy' <- checkKind rightTy OblivK
  return (leftTy', rightTy')

-- | Check if a type is an oblivious sum type and return its components.
--
-- The return types are not necessarily in ANF.
isOSum_ :: Ty Name -> TcM (Ty Name, Ty Name)
isOSum_ t = do
  nf <- whnf_ t
  case nf of
    OSum {..} -> return (left, right)
    _ ->
      err
        [ [DD "Expecting an oblivious sum"],
          [DH "But instead got", DC t]
        ]

-- | Check if an expression with its type is a discriminee to an ADT case
-- analysis, and return the ADT name and the constructors.
isMatchCond :: Expr Name -> Ty Name -> TcM (Text, NonEmpty (Text, [Expr Name]))
isMatchCond cond condTy =
  maybeGV condTy >>= \case
    Just (ref, ADTDef {..}) -> return (ref, ctors)
    _ ->
      withLoc_ cond $
        err
          [ [ DH "The discriminee to the pattern matching is not an ADT",
              DC cond
            ],
            [DH "It has type", DC condTy]
          ]

-- | Check if a well-kinded type in core Taype ANF is oblivious.
isOblivKinded :: Ty Name -> Bool
isOblivKinded = \case
  TUnit -> True
  TBool {olabel = OblivL} -> True
  TInt {olabel = OblivL} -> True
  Pair {pairKind = OblivP} -> True
  OSum {} -> True
  Let {} -> True
  Ite {} -> True
  Match {} -> True
  PMatch {} -> True
  _ -> False

oblivKinded :: Ty Name -> TcM ()
oblivKinded t =
  unless (isOblivKinded t) $
    err [[DH "Expected an oblivious type", DC t]]

-- | Join the pattern matching alternatives and the corresponding ADT's
-- constructors list.
--
-- Each entry of the returned list, when succeeds, consists of the constructor's
-- name, its parameter types, binders and pattern matching body. The order of
-- this list follows that in the ADT signature.
--
-- The two input lists must match exactly, i.e. no constructors that are missing
-- or do not belong to the corresponding ADT. The number of arguments of each
-- alternative also needs to match the number of parameters of the corresponding
-- constructor.
joinAlts ::
  NonEmpty (MatchAlt Expr a) ->
  NonEmpty (Text, [Ty a]) ->
  TcM (NonEmpty (Text, [Ty a], [Maybe Binder], Scope Int Expr a))
joinAlts alts ctors =
  let (result, missing, rest) = foldr go ([], [], toList alts) ctors
      (dups, unknowns) =
        partition
          (isJust . (`lookup` toList ctors))
          [ctor | MatchAlt {..} <- rest]
   in case nonEmpty result of
        Just r | null missing && null rest -> do
          forM_ r $ \(ctor, paraTypes, binders, _) ->
            checkArity CtorApp ctor binders paraTypes
          return r
        _ ->
          err $
            [ [ DH "Some constructors are missing from this pattern matching",
                DD $ andList missing
              ]
              | not $ null missing
            ]
              <> [ [ DH "This pattern matching has some duplicate constructors",
                     DD $ andList dups
                   ]
                   | not $ null dups
                 ]
              <> [ [ DH "Some constructors do not belong to this ADT",
                     DD $ andList unknowns
                   ]
                   | not $ null unknowns
                 ]
  where
    go (ctor, paraTypes) (result, missing, rest) =
      case findAndDel (match ctor) rest of
        Just (MatchAlt {ctor = _, ..}, rest') ->
          ((ctor, paraTypes, binders, bnd) : result, missing, rest')
        _ -> (result, ctor : missing, rest)
    match key MatchAlt {..} = ctor == key

peekLoc :: Expr Name -> Maybe Int
peekLoc Loc {..} = Just loc
peekLoc _ = Nothing

withLoc_ :: (MonadReader Env m) => Expr Name -> m a -> m a
withLoc_ e = mayWithLoc (peekLoc e)

notAppearIn :: Ty Name -> [(Name, Ty Name, Maybe Binder)] -> TcM ()
notAppearIn ty args = do
  Env {options} <- ask
  let xs =
        [ nameOrBinder options x binder
          | (x, _, binder) <- args,
            x `elem` ty
        ]
  unless (null xs) $
    err
      [ [DH "Some free variables appear in the inferred type", DC ty],
        [DH "These variables are", DD $ andList xs],
        [DD "Could not type this expression without dependent types"]
      ]

mkLet :: (MonadFresh m) => Ty Name -> Expr Name -> m (Expr Name)
mkLet t e = do
  x <- fresh
  return $ let' x t e (V x)

mkLet' :: (MonadFresh m) => Ty Name -> Expr Name -> m (Ty Name, Expr Name)
mkLet' t e = (t,) <$> mkLet t e

depBrOops :: a
depBrOops = oops "The number of branches do not match"

depMatchErr :: Ty Name -> TcM a
depMatchErr t =
  err
    [ [ DH "Dependent type does not match the expression",
        DC t
      ]
    ]

pubNameOfOADTName :: Text -> TcM Text
pubNameOfOADTName name =
  lookupGSig name >>= \case
    Just OADTDef {pubName} -> return pubName
    _ -> oops "OADT definition is missing"

-- | Compute the given type's compatible class if it has one.
--
-- The given type must be well-kinded. The returned compatible class is the
-- canonical public type as the representative of this class.
compatibleClass :: Ty Name -> TcM (Maybe (Ty Name))
compatibleClass Prod {olabel = PublicL, ..} = do
  left' <- compatibleClass left
  right' <- compatibleClass right
  return $ Prod PublicL <$> left' <*> right'
compatibleClass Pi {..} = do
  ty' <- compatibleClass ty
  (_, body) <- unbind1 bnd
  body' <- compatibleClass body
  return $ arrow_ <$> ty' <*> body'
compatibleClass GV {..} = return $ Just GV {..}
compatibleClass TUnit = return $ Just TUnit
compatibleClass TBool {} = return $ Just TBool {olabel = PublicL}
compatibleClass TInt {} = return $ Just TInt {olabel = PublicL}
compatibleClass Psi {..} = do
  ref <- pubNameOfOADTName oadtName
  return $ Just GV {..}
compatibleClass Loc {..} = compatibleClass expr
compatibleClass _ = return Nothing

compatible :: Ty Name -> Ty Name -> TcM Bool
compatible t1 t2 = do
  mt1 <- compatibleClass t1
  mt2 <- compatibleClass t2
  case (mt1, mt2) of
    (Just t1', Just t2') -> return $ t1' == t2'
    _ -> return False

----------------------------------------------------------------
-- Definitions checker

-- | Type check all global definitions.
checkDefs :: Options -> Defs Name -> ExceptT Err IO (GCtx Name, Defs Name)
checkDefs options@Options {..} defs = runDcM options $ do
  gsctx <- preCheckDefs defs
  gdctx <- go gsctx mempty defs
  let gctx = mapGCtxDef simp gdctx <> gsctx
  return (gctx, defsFromGCtx gctx (fst <$> defs))
  where
    -- Type checking definitions are done in the order of the given definitions.
    -- They can freely refer to the signatures of all definitions, allowing for
    -- (mutual) recursion. However, the definitions that have not been checked
    -- yet will not be unfolded during type equivalence check.
    go _ gdctx [] = return gdctx
    go gsctx gdctx ((name, _) : defs') = do
      -- use the definition in the signature context because the signatures
      -- there have already been checked.
      def' <- lift $ runTcM (initEnv options name gsctx gdctx) $ checkDef name
      gdctx' <- extendGCtx1 gdctx name def'
      go gsctx gdctx' defs'
    simp def = if optNoFlattenLets then def else flattenLets def

-- | Type check a global definition.
--
-- The signature of this definition must be checked already.
--
-- The returned definition must be in core taype ANF.
checkDef :: Text -> TcM (Def Name)
checkDef name =
  getGSig name >>= \case
    FunDef {..} -> withLabel label $ do
      put poly
      expr0 <- check expr ty
      poly' <- get
      let (ty', expr') = case poly' of
            PolyT MergeableC ->
              -- If a polymorphic function has mergeable constraint, it takes an
              -- extra argument for the if preprocessor which will get resolved
              -- when the type variable is instantiated.
              let ppxTy = typeOfItePpx (TBool OblivL) (TV 0)
               in ( arrow_ ppxTy ty,
                    lam' uniqName ppxTy expr0
                  )
            _ -> (ty, expr0)
      return FunDef {poly = poly', expr = expr', ty = ty', ..}
    OADTDef {..} -> do
      (x, body) <- unbind1 bnd
      body' <- extendCtx1 x viewTy binder $ checkKind body OblivK
      return OADTDef {bnd = abstract_ x body', ..}
    -- 'ADTDef' and 'CtorDef' have been checked in pre-checker, and 'BuiltinDef'
    -- does not need to be checked.
    def -> return def

-- | Pre-check all global signatures to ensure they are well-formed, and their
-- types are well-kinded and in core taype ANF.
preCheckDefs :: Defs Name -> DcM (GCtx Name)
preCheckDefs allDefs = do
  -- First we check if the definition names and binder names follow our naming
  -- rules.
  mapM_ preCheckName allDefs
  -- We need to pre-check all ADTs first, because they can mutually refer to
  -- each other but do not contain dependent types.
  let (adtDefs, otherDefs) = partition isADTDef allDefs
  options <- ask
  -- Note that @gctx0@ trivially satisfies the invariant for global signature
  -- context, because it only contains ADTs (and prelude) at the moment.
  gctx0 <- extendGCtx preludeGCtx adtDefs
  adtDefs' <-
    lift $
      forM adtDefs $ \(name, def) ->
        (name,)
          <$> runTcM
            (initEnv options name gctx0 mempty)
            (preCheckDef allDefs name def)
  -- Extend global signature context with the ADTs and their constructors. Note
  -- that the types of all constructors are already in the right form after
  -- pre-check.
  gctx <- extendGCtx preludeGCtx $ foldMap adtWithCtors adtDefs'
  -- Now we pre-check the rest of signatures in order.
  go gctx otherDefs
  where
    isADTDef (_, ADTDef {}) = True
    isADTDef _ = False
    adtWithCtors (name, def@ADTDef {..}) =
      let ctorDefs =
            ctors <&> second (\paraTypes -> CtorDef {dataType = name, ..})
       in (name, def) : toList ctorDefs
    adtWithCtors (_, _) = oops "Not an ADT definition"
    -- Pre-checking signatures except for ADTs is done in the order of the given
    -- definitions. While mutual recursion is allowed, the type of a definition
    -- should not refer to this definition itself, directly or transitively.
    go gctx [] = return gctx
    go gctx ((name, def) : defs) = do
      options <- ask
      def' <-
        lift $
          runTcM (initEnv options name gctx mempty) $
            preCheckDef allDefs name def
      gctx' <- extendGCtx1 gctx name def'
      go gctx' defs

-- | Check the definition and binder names.
preCheckName :: NamedDef Name -> DcM ()
preCheckName (defName, def) = do
  void $ runFreshT $ transformBiM go def
  case def of
    FunDef {..} -> checkLower defName loc "Function"
    ADTDef {..} -> do
      unless (isLower $ T.head defName) $
        err_ loc "ADT name should start with a lower case letter"
      forM_ ctors $ \(ctor, _) ->
        unless (isUpper $ T.head ctor) $
          err_ loc "Constructor name should start with a upper case letter"
    OADTDef {..} -> checkLower defName loc "OADT"
    _ -> pass
  where
    mayStripPrefix prefix s = fromMaybe s $ T.stripPrefix prefix s
    checkLower name loc what = do
      let name' =
            mayStripPrefix oblivAccent $ mayStripPrefix internalPrefix name
      unless (isLower $ T.head name') $
        err_ loc $
          what
            <+> "name should start with a lower case letter, possibly with a"
            <+> dquotes (pretty oblivAccent)
            <+> "prefix"
    checkBinder binder =
      whenJust binder $ \case
        Named loc name -> checkLower name loc "Binder"
        _ -> pass
    errConflict :: (MonadError Err m) => Binder -> m ()
    errConflict = \case
      Named loc name ->
        err_ loc $
          "Found conflicting pattern variables: " <> pretty name
      _ -> oops "Anonymous binders cannot be duplicate"
    go :: (MonadError Err m) => Expr Name -> m (Expr Name)
    go e@Match {..} = do
      forM_ alts $ \MatchAlt {..} -> do
        mapM_ checkBinder binders
        whenJust (findDupBinderName (catMaybes binders)) errConflict
      return e
    go e@Pi {..} = checkBinder binder >> return e
    go e@Lam {..} = checkBinder binder >> return e
    go e@Let {..} = checkBinder binder >> return e
    go e@PMatch {..} = do
      checkBinder lBinder
      checkBinder rBinder
      whenJust (findDupBinderName (catMaybes [lBinder, rBinder])) errConflict
      return e
    go e@OMatch {..} = checkBinder lBinder >> checkBinder rBinder >> return e
    go e = return e

-- | Pre-check a global definition signature.
--
-- The first argument is the definitions for peeking ahead.
--
-- This routine also ensures all OADT structures are well-formed. First, all
-- instances of an OADT structure should be present. Second, these instances
-- should have the right types and labels. Finally, there should not be any
-- unrecognized instances.
preCheckDef :: Defs Name -> Text -> Def Name -> TcM (Def Name)
preCheckDef defs name def = do
  let attr' = attrOfName name
  checkAttr attr'
  case def of
    FunDef {..} -> withLabel label $ do
      case attr' of
        KnownInst inst -> put $ polyOfInst inst
        _ -> pass
      ty' <- kinded ty
      case attr' of
        KnownInst inst -> do
          preCheckInst loc name inst ty'
          -- Check label against OADT instance signature.
          checkDefLabel loc name (labelOfInst inst) label
        _ -> pass
      poly' <- get
      return FunDef {ty = ty', attr = attr', poly = poly', ..}
    ADTDef {..} -> do
      ctors' <- forM ctors $ secondM $ mapM (`checkKind` PublicK)
      return ADTDef {ctors = ctors', ..}
    OADTDef {..} -> do
      viewTy' <- checkKind viewTy PublicK
      checkAvailInsts loc
      pubName' <- inferPubName loc
      return OADTDef {pubName = pubName', viewTy = viewTy', ..}
    _ -> oops "Pre-checking constructor or builtin definitions"
  where
    inferPubName loc = do
      t <-
        inferPubTy `catchError` \_ ->
          err_ loc $
            "The type of section function"
              <+> pretty (sectionName name)
              <+> "is ill-formed"
      maybeGV t >>= \case
        Just (ref, ADTDef {}) -> return ref
        _ ->
          errPlain
            loc
            [ [ DH $
                  "The source type of section function"
                    <+> pretty (sectionName name)
                    <+> "is not an ADT",
                DC t
              ]
            ]
    inferPubTy =
      case lookup (sectionName name) defs of
        Just FunDef {..} -> do
          (_, _, bnd) <- isPi ty
          (_, body) <- unbind1 bnd
          (t, _, _) <- isPi body
          return t
        _ -> oops "Section instance does not exist"

    checkAttr UnknownInst =
      err_ (getDefLoc def) $
        "Definition" <+> pretty name <+> "cannot be recognized as an instance"
    checkAttr _ = pass

    checkAvailInsts loc = do
      let missing = filter (isNothing . flip lookup defs) $ instNamesOfOADT name
      unless (null missing) $
        err_ loc $
          "OADT definition"
            <+> pretty name
            <+> "lacks some instances:"
              <> softline
              <> andList missing

    labelOfInst RetractionInst {} = LeakyL
    labelOfInst _ = SafeL
    polyOfInst MatchInst {} = PolyT UnrestrictedC
    polyOfInst _ = MonoT

-- | Check the type of the given OADT instance is well-formed.
preCheckInst :: Int -> Text -> OADTInst -> Ty Name -> TcM ()
preCheckInst loc name LiftInst {..} ty =
  lookupGSig fn >>= \case
    Just FunDef {ty = ty'} -> do
      unlessM (compatible ty ty') $
        errPlain
          loc
          [ [ DD $
                "The type of function"
                  <+> pretty name
                  <+> "is not compatible with the type of function"
                  <+> pretty fn
            ],
            [DH "Expected a type compatible with", DC ty'],
            [DH "Got", DC ty]
          ]
    _ ->
      err_ loc $
        "Function"
          <+> pretty name
          <+> "is a lifting of"
          <+> pretty fn
          <+> "which is not in scope or not a function"
preCheckInst loc name inst ty = isOADTDef (oadtNameOfInst inst) >>= go
  where
    go (pubName, viewTy) = case inst of
      SectionInst {..} -> do
        k <- fresh
        equateSig $
          pi' k viewTy $
            arrow_ (GV pubName) $
              oadtName @@@ [V k]
      RetractionInst {..} -> do
        k <- fresh
        equateSig $
          pi' k viewTy $
            arrow_ (oadtName @@@ [V k]) $
              GV pubName
      ViewInst {} -> equateSig $ arrow_ (GV pubName) viewTy
      JoinInst {} -> equateSig $ arrows_ [viewTy, viewTy] viewTy
      ReshapeInst {..} -> do
        k <- fresh
        k' <- fresh
        equateSig $
          pi' k viewTy $
            pi' k' viewTy $
              arrow_ (oadtName @@@ [V k]) (oadtName @@@ [V k'])
      CoerceInst {..} -> do
        (pubName', viewTy') <- isOADTDef oadtTo
        unless (pubName == pubName') $
          err_ loc $
            "Function"
              <+> pretty name
              <+> "coerces between incompatible types"
        equateSig $
          arrows_
            [Psi {viewTy = Just viewTy, oadtName = oadtName}]
            Psi {viewTy = Just viewTy', oadtName = oadtTo}
      CtorInst {..} -> do
        argTy <-
          mustBeArrow ty >>= \case
            (argTs, Psi {oadtName = oadtName'})
              | oadtName == oadtName' ->
                  case argTs of
                    [t] -> return t
                    _ ->
                      err_ loc $
                        "Function"
                          <+> pretty name
                          <+> "should have exactly one argument, but got"
                          <+> pretty (length argTs)
            (_, t) ->
              errReturnType
                ("Function" <+> pretty name)
                []
                Psi {viewTy = Nothing, ..}
                t
        lookupGSig ctor >>= \case
          Just (CtorDef {..})
            | dataType == pubName -> do
                let paraType = prod_ paraTypes
                unlessM (compatible paraType argTy) $
                  errCompatible
                    ("The argument type of function" <+> pretty name)
                    ctor
                    []
                    paraType
                    argTy
          _ ->
            err_ loc $
              "Function"
                <+> pretty name
                <+> "is a constructor instance of the OADT"
                <+> pretty oadtName <> ", but"
                <+> pretty ctor
                <+> "is not a constructor of the ADT"
                <+> pretty pubName
      MatchInst {..} -> do
        argTs <-
          mustBeArrow ty >>= \case
            (argTs, TV {}) -> return argTs
            (_, t) ->
              errReturnType
                ("Function" <+> pretty name)
                []
                (TV 0)
                t
        case argTs of
          [] ->
            err_ loc $ "Function" <+> pretty name <+> "has no argument"
          Psi {oadtName = oadtName'} : altTs
            | oadtName == oadtName' -> checkAlts pubName altTs
          t : _ ->
            errPlain
              loc
              [ [ DD $
                    "The first argument of function"
                      <+> pretty name
                      <+> "has the wrong type"
                ],
                [DH "Expected", DC (Psi {viewTy = Nothing, ..} :: Ty Name)],
                [DH "Got", DC t]
              ]

    -- Check type against OADT instance signature.
    equateSig instTy =
      equate instTy ty `catchError` \_ ->
        errPlain
          loc
          [ [ DD $
                "Function"
                  <+> pretty name
                  <+> "has the wrong type"
            ],
            [DH "Expected", DC instTy],
            [DH "Got", DC ty]
          ]

    checkAlts pubName altTs = do
      argTs <- forM altTs $ \altTy ->
        mustBeArrow altTy >>= \case
          (argTs, TV {}) ->
            case argTs of
              [t] -> return (altTy, t)
              _ ->
                errPlain
                  loc
                  [ [ DD $
                        "All alternatives of function"
                          <+> pretty name
                          <+> "should have exactly one argument,"
                          <+> "but one alternative got"
                          <+> pretty (length argTs)
                    ],
                    [DH "Alternative", DC altTy]
                  ]
          (_, t) ->
            errReturnType
              ("An alternative of function" <+> pretty name)
              [[DH "Alternative", DC altTy]]
              (TV 0)
              t
      ctors <-
        lookupGSig pubName >>= \case
          Just ADTDef {ctors} -> return $ toList ctors
          _ -> oops "ADT definition is missing"
      unless (length argTs == length ctors) $
        err_ loc $
          "Function"
            <+> pretty name
            <+> "has"
            <+> pretty (length argTs)
            <+> "alternative arguments, but ADT"
            <+> pretty pubName
            <+> "has"
            <+> pretty (length ctors)
            <+> "constructors"
      flip2 zipWithM_ argTs ctors $ \(altTy, argTy) (ctor, paraTypes) -> do
        let paraType = prod_ paraTypes
        unlessM (compatible argTy paraType) $
          errCompatible
            ("The argument type of an alternative of function" <+> pretty name)
            ctor
            [[DH "Alternative", DC altTy]]
            paraType
            argTy

    isOADTDef oadtName =
      lookupGSig oadtName >>= \case
        Just OADTDef {pubName, viewTy} -> return (pubName, viewTy)
        _ ->
          err_ loc $
            "Function"
              <+> pretty name
              <+> "is an instance of"
              <+> pretty oadtName <> ", but"
              <+> pretty oadtName
              <+> "is not an OADT or not in scope"
    mustBeArrow t = case isArrow t of
      Just r -> return r
      _ ->
        err_ loc $
          "Function"
            <+> pretty name
            <+> "cannot have a dependent function type"
    errReturnType :: Doc -> [[D]] -> Ty Name -> Ty Name -> TcM a
    errReturnType what msg expected got =
      errPlain
        loc
        $ [[DD what, DD "has the wrong return type"]]
          <> msg
          <> [ [DH "Expected", DC expected],
               [DH "Got", DC got]
             ]
    errCompatible what ctor msg expected got =
      errPlain
        loc
        $ [ [ DD what,
              DD $
                "is not compatible with the parameters of constructor"
                  <+> pretty ctor
            ]
          ]
          <> msg
          <> [ [DH "Expected a type compatible with", DC expected],
               [DH "Got", DC got]
             ]

extendGCtx1 ::
  (MonadError Err m, MonadReader Options m) =>
  GCtx Name ->
  Text ->
  Def Name ->
  m (GCtx Name)
extendGCtx1 gctx name def =
  case lookupGCtx name gctx of
    Just def' -> do
      Options {optFile = file, optCode = code} <- ask
      err_ (getDefLoc def) $
        "Definition"
          <+> dquotes (pretty name)
          <+> "has already been defined at"
          </> pretty (renderFancyLocation file code (getDefLoc def'))
    _ -> return $ insertGCtx name def gctx

extendGCtx ::
  (MonadError Err m, MonadReader Options m) =>
  GCtx Name ->
  Defs Name ->
  m (GCtx Name)
extendGCtx = foldlM $ uncurry . extendGCtx1

getGSig :: (MonadReader Env m) => Text -> m (Def Name)
getGSig x =
  lookupGSig x
    <&> fromMaybe (oops $ "Definition " <> x <> " does not exist")

-- | Flatten all nested let bindings and remove single variable bindings.
--
-- If the input is in core taype ANF, the result must still be in core taype
-- ANF.
flattenLets :: Def Name -> Def Name
flattenLets = runFreshM . transformBiM go
  where
    go e@Let {..} = case rhs of
      V {..} -> return $ instantiateName name bnd
      Let
        { rhsTy = rhsTyN,
          rhs = rhsN,
          binder = binderN,
          bnd = bndN
        } -> do
          (x, bodyN) <- unbind1 bndN
          body' <- go Let {rhs = bodyN, ..}
          return
            Let
              { rhsTy = rhsTyN,
                rhs = rhsN,
                binder = binderN,
                bnd = abstract_ x body'
              }
      _ -> return e
    go e = return e

----------------------------------------------------------------
-- Error reporting

type D = Disp TcM

instance MonadCute TcM Int

instance MonadCute TcM Text

instance MonadCute TcM Kind where
  cutie k = return $ show k <+> parens (pretty k)

instance MonadCute TcM (Expr Text)

instance MonadCute TcM (TCtx Text)

instance MonadCute TcM (Expr Name) where
  cutie = cutie <=< mapM renderName <=< readableExpr

instance MonadCute TcM (TCtx Int) where
  cutie = cutie <=< mapM renderName <=< biplateM readableExpr

err_ :: (MonadError Err m) => Int -> Doc -> m a
err_ errLoc errMsg =
  throwError
    Err
      { errCategory = "Typing Error",
        errClass = ErrorC,
        ..
      }

errPlain :: Int -> [[D]] -> TcM a
errPlain loc dss = do
  doc <- cutie dss
  err_ loc doc

errDummy :: TcM a
errDummy = err_ (-1) ""

err :: [[D]] -> TcM a
err dss = do
  Env {..} <- ask
  doc <- reportDoc dss
  err_ loc doc

warn :: [[D]] -> TcM ()
warn dss =
  ask >>= \Env {..} -> unless (optQuiet options) $ do
    doc <- reportDoc dss
    printDoc options $
      runCuteM options $
        cute $
          Err
            { errCategory = "Warning",
              errClass = WarningC,
              errLoc = loc,
              errMsg = doc
            }

reportDoc :: [[D]] -> TcM Doc
reportDoc dss = do
  Env {..} <- ask
  doc <- cutie dss
  curDoc <- cutie (DC cur :: D)
  tctxDoc <- cutie tctx
  return $
    doc
      <//> hang ("When checking expression" <> colon <> sep1 curDoc)
      <//> tctxDoc

renderName :: Name -> TcM Text
renderName x = do
  binder <- lookupBinder x
  Env {options} <- ask
  return $ nameOrBinder options x binder

errArity :: AppKind -> Text -> Int -> Int -> TcM a
errArity appKind ref actual expected =
  let what = case appKind of
        CtorApp -> "constructor"
        BuiltinApp -> "builtin function"
        TypeApp -> "oblivious ADT"
        FunApp -> "function"
   in err
        [ [ DD "The",
            DD what,
            DQ ref,
            DD "should have",
            DC expected,
            DD $ plural "argument," "arguments," expected,
            DD "but got",
            DC actual
          ],
          [ DD
              "Constructors, builtin functions, and oblivious ADTs \
              \are required to be fully applied"
          ]
        ]

andList :: [Text] -> Doc
andList [] = "<empty>"
andList [x] = pretty x
andList [x, y] = fillSep [pretty x, "and", pretty y]
andList (x : xs) = pretty (x <> ",") <> softline <> andList xs

-- | The definition checking monad
type DcM = ReaderT Options (ExceptT Err IO)

runDcM :: Options -> DcM a -> ExceptT Err IO a
runDcM = usingReaderT

-- | The type checking monad
newtype TcM a = TcM (FreshT (StateT PolyType (ReaderT Env (ExceptT Err IO))) a)
  deriving newtype
    ( Functor,
      Applicative,
      Monad,
      MonadFresh,
      MonadReader Env,
      MonadState PolyType,
      MonadError Err,
      MonadIO
    )

runTcM :: Env -> TcM a -> ExceptT Err IO a
runTcM env (TcM m) = runReaderT (evalStateT (runFreshT m) MonoT) env

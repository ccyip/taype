{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
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
--     require the constructors and builtin functions are always in application
--     form, even if they have no argument.
--
--   - Core taype: an expression is in core taype, if it is
--
--     * fully annotated. This includes type and label annotations, as well as
--       annotations specific to certain constructs, e.g., application kinds in
--       applications and return types in conditionals.
--
--     * No ascription or location constructs.
--
--     * Use explicit label promotion. The implicit label conversion is disabled
--       in the typing rules for core taype. Various constructs also require
--       their subcomponents to have the same label, e.g., arguments of a
--       constructor.
--
--     * The alternatives in all pattern matchings are in the canonical order,
--       i.e. the order in the corresponding ADT signature.
--
-- We maintain a few invariants throughout the type checking process.
--
--   - Types in the global typing context must be well-kinded and in core taype
--     ANF. It includes the signatures of function definitions, constructor
--     arguments and OADT arguments. The function signatures should also conform
--     to their attributes.
--
--   - Definitions in the global definition context must be well-typed or
--     well-kinded (against their signatures in typing context). They must also
--     be in core taype ANF.
--
--   - Types in the local typing context must be well-kinded and in core taype
--     ANF.
--
-- Other invariants for each procedure are documented in that procedure.
module Taype.TypeChecker (checkDefs) where

import Algebra.Lattice
import Algebra.PartialOrd
import Bound
import Control.Monad.Error.Class
import Data.List (lookup, partition, zip4, zipWith3)
import Data.Maybe (fromJust)
import Taype.Binder
import Taype.Common
import Taype.Cute
import Taype.Environment
import Taype.Error
import Taype.Name
import qualified Taype.NonEmpty as NE
import Taype.Plate
import Taype.Prelude
import Taype.Syntax

----------------------------------------------------------------
-- Bidirectional type and kind checkers

-- | Type check an expression bidirectionally.
--
-- Both types (the second argument) and labels (the third argument) may be
-- inferred or checked. They are in inference mode if they are 'Nothing', or in
-- checking mode otherwise. This function returns the expression's type, label
-- and its full elaboration.
--
-- The given type must be well-kinded and in core taype ANF.
--
-- The returned type must be well-kinded and in core taype ANF. It is also
-- equivalent to the given type if in type checking mode.
--
-- The returned label must be the same as the given label if in label checking
-- mode.
--
-- The returned expression must be in core taype ANF. Of course, it must also be
-- typed by the returned type and label, and equivalent to the given expression.
typing ::
  Expr Name ->
  Maybe (Ty Name) ->
  Maybe Label ->
  TcM (Ty Name, Label, Expr Name)
typing e@VUnit Nothing Nothing = return (TUnit, SafeL, e)
typing e@BLit {} Nothing Nothing = return (TBool, SafeL, e)
typing e@ILit {} Nothing Nothing = return (TInt, SafeL, e)
typing e@V {..} Nothing Nothing =
  lookupTy name >>= \case
    Just (t, l) -> return (t, l, e)
    -- The expression is locally closed before type checking, so open local
    -- variables are not possible.
    _ -> oops $ "Local variable not in scope: " <> show name
typing e@GV {..} Nothing Nothing =
  lookupGSig ref >>= \case
    Just FunDef {..} -> return (ty, fromJust label, e)
    Just CtorDef {..} -> do
      checkArity CtorApp ref [] paraTypes
      return
        ( GV dataType,
          SafeL,
          -- All constructors are in application form even if they have zero
          -- argument.
          App {fn = e, args = [], appKind = Just CtorApp}
        )
    Just BuiltinDef {..} -> do
      checkArity BuiltinApp ref [] paraTypes
      return
        ( resType,
          SafeL,
          -- All builtin functions are in application form even if they have
          -- zero argument.
          App {fn = e, args = [], appKind = Just BuiltinApp}
        )
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not a term"]]
    _ ->
      err [[DD "Variable", DQ ref, DD "is not in scope"]]
typing Lam {mTy = Just binderTy, ..} Nothing ml = do
  -- Note that this is the label of the binder, not the label of the whole
  -- lambda.
  binderLabel <- labeling label
  binderTy' <- kinded binderTy
  (x, body) <- unbind1 bnd
  (tBody', l', body') <-
    extendCtx1 x binderTy' binderLabel binder $ infer_ body ml
  return
    ( Pi
        { ty = binderTy',
          label = Just binderLabel,
          bnd = abstract_ x tBody',
          ..
        },
      l',
      Lam
        { mTy = Just binderTy',
          label = Just binderLabel,
          bnd = abstract_ x body',
          ..
        }
    )
typing Lam {..} (Just t) ml = do
  (binderTy', binderLabel, _, tBnd') <- isPi t
  let binderLabel' = fromJust binderLabel
  -- If the binder label is given in the lambda term, it has to agree with the
  -- one in the pi-type.
  checkLabel label binderLabel'
  whenJust mTy $ \binderTy -> do
    t' <- kinded binderTy
    -- If the binder type is given in the lambda term, it has to agree with the
    -- one in the pi-type.
    mayWithLoc (peekLoc binderTy) $
      equate binderTy' t'
  (x, body, tBody') <- unbind1With bnd tBnd'
  (l, body') <-
    extendCtx1 x binderTy' binderLabel' binder $
      check_ body tBody' ml
  return
    ( Pi
        { ty = binderTy',
          label = Just binderLabel',
          bnd = abstract_ x tBody',
          ..
        },
      l,
      Lam
        { mTy = Just binderTy',
          label = Just binderLabel',
          bnd = abstract_ x body',
          ..
        }
    )
typing App {..} Nothing ml =
  maybeGV fn >>= \case
    -- Constructors and builtin functions have to be fully applied, and the
    -- resulting label is determined by their label polymorphism strategies.
    Just (ctor, CtorDef {..}) ->
      typePolyApp ctor paraTypes (GV dataType) JoinStrategy CtorApp
    Just (f, BuiltinDef {..}) ->
      typePolyApp f paraTypes resType strategy BuiltinApp
    _ -> typeFnApp
  where
    -- Application for constructors and builtin functions
    typePolyApp f paraTypes resType strat appKind' = do
      checkArity appKind' f args paraTypes
      let argLabel = case strat of
            -- In join strategy, argument labels are either inferred or the
            -- given one.
            JoinStrategy -> ml
            -- In other strategies, argument labels must be safe.
            _ -> Just SafeL
      argRes <-
        zipWithM (\arg t -> typing arg (Just t) argLabel) args paraTypes
      let (argTs', argLs, _) = unzip3 argRes
          argLabel' = case strat of
            JoinStrategy -> fromMaybe (foldl' (\/) SafeL argLs) argLabel
            _ -> SafeL
      -- Promote all arguments to the right labels.
      args' <- forM argRes $ uncurry3 $ mayPromote argLabel'
      xs <- freshes $ length argRes
      let bindings = zipWith3 (\x t e -> (x, t, argLabel', e)) xs argTs' args'
          minLabel = case strat of
            JoinStrategy -> argLabel'
            LeakyStrategy -> LeakyL
            SafeStrategy -> SafeL
          -- The resulting label of this expression is either the given one, or
          -- the minimal label.
          l' = fromMaybe minLabel ml
      -- Promote the resulting expression.
      e' <-
        mayPromote l' resType minLabel $
          lets_
            bindings
            App
              { fn = GV f,
                args = V <$> xs,
                appKind = Just appKind'
              }
      return (resType, l', e')
    -- Application for functions
    typeFnApp = do
      (fnTy', l', fn') <- infer_ fn ml
      (argRes, t') <- go args fnTy'
      xs <- freshes (length args)
      let bindings = zipWith (\x (t, l, e) -> (x, t, l, e)) xs argRes
      x <- fresh
      return
        ( t',
          l',
          lets_
            ((x, fnTy', l', fn') : bindings)
            App
              { fn = V x,
                args = V <$> xs,
                appKind = Just FunApp
              }
        )
    -- @t@ must be well-kinded and in core taype ANF.
    go [] t = return ([], t)
    go (arg : args') t = do
      (argTy', argLabel, _, bnd) <- isPi t
      let argLabel' = fromJust argLabel
      arg' <- check arg argTy' argLabel'
      -- Unfortunately, we have to kind the pi-type body again here even though
      -- it was in good form, because it may not be in core taype ANF anymore
      -- after instantiation.
      body' <- kinded $ instantiate_ arg' bnd
      (res, t') <- go args' body'
      return ((argTy', argLabel', arg') : res, t')

-- NOTE: checking mode for let is possible, but it requires a local definition
-- context.
typing Let {..} Nothing ml = do
  (rhsTy', rhsLabel', rhs') <- typing rhs mTy label
  (x, body) <- unbind1 bnd
  (t, l', body') <- extendCtx1 x rhsTy' rhsLabel' binder $ infer_ body ml
  -- Unfortunately, we have to kind @t@ again even though it is kinded, because
  -- it may not be in core taype ANF after substitution.
  t' <- kinded $ substitute x rhs' t
  return
    ( t',
      l',
      Let
        { mTy = Just rhsTy',
          label = Just rhsLabel',
          rhs = rhs',
          bnd = abstract_ x body',
          ..
        }
    )
typing Ite {..} mt ml = do
  (condLabel, cond') <- check_ cond TBool Nothing
  let ctxs = NE.fromList [[], []]
      argss = NE.fromList [[], []]

      -- Typing without dependent types
      typeNoDep = do
        (t', leftLabel, left') <- typing left mt ml
        (rightLabel, right') <- check_ right t' ml
        return (left', t', leftLabel, right', t', rightLabel, t')

      -- Infer a dependent type.
      inferDep = do
        checkLabel (Just condLabel) SafeL
        (leftTy', leftLabel, left') <- infer_ left ml
        (rightTy', rightLabel, right') <- infer_ right ml
        t' <- depGen gen ctxs argss (NE.fromList [leftTy', rightTy'])
        return (left', leftTy', leftLabel, right', rightTy', rightLabel, t')

      -- Check a dependent type.
      checkDep t' = do
        checkLabel (Just condLabel) SafeL
        (leftTy', rightTy') <-
          depMatch match ctxs argss t' >>= \case
            leftTy' :| [rightTy'] -> return (leftTy', rightTy')
            _ -> depOops
        (leftLabel, left') <- check_ left leftTy' ml
        (rightLabel, right') <- check_ right rightTy' ml
        return (left', leftTy', leftLabel, right', rightTy', rightLabel, t')

      -- Generator
      gen (leftTy' :| [rightTy']) = do
        x <- fresh
        return $
          lets_
            [(x, TBool, SafeL, cond')]
            Ite {cond = V x, left = leftTy', right = rightTy', mTy = Nothing}
      gen _ = depOops

      -- Matcher
      match Ite {cond = condQ, left = leftQ, right = rightQ} = do
        equate cond' condQ
        return $ NE.fromList [leftQ, rightQ]
      match t = depMatchErr t

  (left', leftTy', leftLabel, right', rightTy', rightLabel, t') <-
    depType typeNoDep inferDep checkDep mt (\(_, _, _, _, _, _, t) -> t)
  let l' = condLabel \/ leftLabel \/ rightLabel
  left'' <- mayPromote l' leftTy' leftLabel left'
  right'' <- mayPromote l' rightTy' rightLabel right'
  x <- fresh
  return
    ( t',
      l',
      lets_
        [(x, TBool, condLabel, cond')]
        Ite
          { mTy = Just t',
            cond = V x,
            left = left'',
            right = right''
          }
    )
typing Pair {..} mt ml = do
  (mLeftTy, mRightTy) <- mapM isProd mt <&> NE.unzip
  (leftTy', leftLabel, left') <- typing left mLeftTy ml
  (rightTy', rightLabel, right') <- typing right mRightTy ml
  let l' = leftLabel \/ rightLabel
  left'' <- mayPromote l' leftTy' leftLabel left'
  right'' <- mayPromote l' rightTy' rightLabel right'
  xl <- fresh
  xr <- fresh
  return
    ( Prod {left = leftTy', right = rightTy'},
      l',
      lets_
        [ (xl, leftTy', l', left''),
          (xr, rightTy', l', right'')
        ]
        Pair {left = V xl, right = V xr}
    )
typing PCase {..} mt ml = do
  (condTy', condLabel, cond') <- infer cond
  (leftTy', rightTy') <- mayWithLoc (peekLoc cond) $ isProd condTy'
  ((xl, xr), body) <- unbind2 bnd2

  let ctxs = NE.fromList [[]]
      argss =
        NE.fromList
          [ [ (xl, leftTy', condLabel, lBinder),
              (xr, rightTy', condLabel, rBinder)
            ]
          ]

      -- Typing without dependent types
      typeNoDep = do
        (bodyTy', bodyLabel, body') <- typeBody mt
        -- @t'@ cannot refer to @xl@ or @xr@, otherwise it would be dependent
        -- type.
        notAppearIn bodyTy' $ head argss
        return (body', bodyTy', bodyLabel, bodyTy')

      -- Infer a dependent type.
      inferDep = do
        checkLabel (Just condLabel) SafeL
        (bodyTy', bodyLabel, body') <- typeBody Nothing
        t' <- depGen gen ctxs argss (NE.fromList [bodyTy'])
        return (body', bodyTy', bodyLabel, t')

      -- Check a dependent type.
      checkDep t' = do
        checkLabel (Just condLabel) SafeL
        bodyTy' <-
          depMatch match ctxs argss t' >>= \case
            bodyTy' :| [] -> return bodyTy'
            _ -> depOops
        (_, bodyLabel, body') <- typeBody (Just bodyTy')
        return (body', bodyTy', bodyLabel, t')

      -- Generator
      gen (bodyTy' :| []) = do
        x <- fresh
        return $
          lets_
            [(x, condTy', SafeL, cond')]
            PCase
              { cond = V x,
                bnd2 = abstract_ (xl, xr) bodyTy',
                mTy = Nothing,
                ..
              }
      gen _ = depOops

      -- Matcher
      match PCase {cond = condQ, bnd2 = bnd2Q} = do
        equate cond' condQ
        return $ instantiateName (xl, xr) bnd2Q :| []
      match t = depMatchErr t

      -- Type check the body.
      typeBody mt' = extendCtx (head argss) $ typing body mt' ml

  (body', bodyTy', bodyLabel, t') <-
    depType typeNoDep inferDep checkDep mt (\(_, _, _, t) -> t)
  let l' = condLabel \/ bodyLabel
  body'' <- mayPromote l' bodyTy' bodyLabel body'
  x <- fresh
  return
    ( t',
      l',
      lets_
        [(x, Prod {left = leftTy', right = rightTy'}, condLabel, cond')]
        PCase
          { mTy = Just t',
            cond = V x,
            bnd2 = abstract_ (xl, xr) body'',
            ..
          }
    )
typing Case {..} mt ml = do
  (condTy', condLabel, cond') <- infer cond
  (ref, ctors) <- isCaseCond cond condTy'
  joinedAlts <- joinAlts alts ctors

  res <-
    forM joinedAlts $ \(ctor, paraTypes, binders, bnd) -> do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      return (ctor, body, zip4 xs paraTypes (replicate n condLabel) binders)

  let ctxs = joinedAlts $> []
      (ctorNames, bodies, argss) = NE.unzip3 res

      -- Typing without dependent types
      typeNoDep = do
        let (args0 :| argsRest) = argss
            (body0 :| bodyRest) = bodies
        altRes0@(bodyTy', _, _) <- typeAlt mt args0 body0
        altResRest <- zipWithM (typeAlt (Just bodyTy')) argsRest bodyRest
        let altRes = altRes0 :| altResRest
        -- The type of each branch cannot refer to the pattern variables,
        -- otherwise it would be dependent type.
        NE.zipWithM_ (\(t, _, _) args -> notAppearIn t args) altRes argss
        return (altRes, bodyTy')

      -- Infer a dependent type.
      inferDep = do
        checkLabel (Just condLabel) SafeL
        altRes <- NE.zipWithM (typeAlt Nothing) argss bodies
        t' <- depGen gen ctxs argss $ altRes <&> \(t, _, _) -> t
        return (altRes, t')

      -- Check a dependent type.
      checkDep t' = do
        checkLabel (Just condLabel) SafeL
        bodyTs <- depMatch match ctxs argss t'
        altRes <- NE.zipWith3M (typeAlt . Just) bodyTs argss bodies
        return (altRes, t')

      -- Generator
      gen bodyTs = do
        let tyAlts = NE.zipWith3 mkCaseAlt ctorNames argss bodyTs
        x <- fresh
        return $
          lets_
            [(x, condTy', SafeL, cond')]
            Case {cond = V x, alts = tyAlts, mTy = Nothing}

      -- Matcher
      match Case {cond = condQ, alts = altsQ} = do
        equate cond' condQ
        -- Because the input type is in core taype, the constructors are in the
        -- canonical order.
        return $
          NE.zipWith
            ( \args CaseAlt {bnd} ->
                let xs = [x | (x, _, _, _) <- args]
                 in instantiateName xs bnd
            )
            argss
            altsQ
      match t = depMatchErr t

      -- Type check an alternative.
      typeAlt mt' args body = extendCtx args $ typing body mt' ml

  (altRes, t') <- depType typeNoDep inferDep checkDep mt snd
  let l' = flipfoldl' (\(_, l, _) -> (l \/)) condLabel altRes
  alts' <- NE.zipWith3M (promoteAlt l') ctorNames argss altRes
  x <- fresh
  return
    ( t',
      l',
      lets_
        [(x, GV ref, condLabel, cond')]
        Case
          { mTy = Just t',
            cond = V x,
            alts = alts'
          }
    )
  where
    mkCaseAlt ctor args body =
      let xs = [x | (x, _, _, _) <- args]
          binders = [binder | (_, _, _, binder) <- args]
       in CaseAlt {bnd = abstract_ xs body, ..}
    promoteAlt l' ctor args (bodyTy', bodyLabel, body') = do
      body'' <- mayPromote l' bodyTy' bodyLabel body'
      return $ mkCaseAlt ctor args body''
typing Mux {..} mt Nothing = do
  cond' <- check cond OBool SafeL
  (t', _, left') <- typing left mt (Just SafeL)
  right' <- check right t' SafeL
  void $ checkKind t' OblivK
  x <- fresh
  xl <- fresh
  xr <- fresh
  return
    ( t',
      SafeL,
      lets_
        [ (x, OBool, SafeL, cond'),
          (xl, t', SafeL, left'),
          (xr, t', SafeL, right')
        ]
        Mux {cond = V x, left = V xl, right = V xr}
    )
typing OIte {..} mt Nothing = do
  cond' <- check cond OBool SafeL
  (t', _, left') <- typing left mt (Just LeakyL)
  right' <- check right t' LeakyL
  x <- fresh
  xl <- fresh
  xr <- fresh
  return
    ( t',
      LeakyL,
      lets_
        [ (x, OBool, SafeL, cond'),
          (xl, t', LeakyL, left'),
          (xr, t', LeakyL, right')
        ]
        OIte {cond = V x, left = V xl, right = V xr}
    )
typing OPair {..} mt Nothing = do
  (mLeftTy, mRightTy) <- mapM isOProd mt <&> NE.unzip
  (leftTy', _, left') <- typing left mLeftTy (Just SafeL)
  (rightTy', _, right') <- typing right mRightTy (Just SafeL)
  void $ checkKind leftTy' OblivK
  void $ checkKind rightTy' OblivK
  xl <- fresh
  xr <- fresh
  return
    ( OProd {left = leftTy', right = rightTy'},
      SafeL,
      lets_
        [ (xl, leftTy', SafeL, left'),
          (xr, rightTy', SafeL, right')
        ]
        OPair {left = V xl, right = V xr}
    )
typing OPCase {..} mt ml = do
  (condTy', _, cond') <- infer_ cond (Just SafeL)
  (leftTy', rightTy') <- mayWithLoc (peekLoc cond) $ isOProd condTy'
  ((xl, xr), body) <- unbind2 bnd2
  (bodyTy', bodyLabel, body') <-
    extendCtx
      [ (xl, leftTy', SafeL, lBinder),
        (xr, rightTy', SafeL, rBinder)
      ]
      $ typing body mt ml
  x <- fresh
  return
    ( bodyTy',
      bodyLabel,
      lets_
        [(x, OProd {left = leftTy', right = rightTy'}, SafeL, cond')]
        OPCase
          { cond = V x,
            bnd2 = abstract_ (xl, xr) body',
            ..
          }
    )
typing OInj {mTy = Just t, ..} Nothing Nothing = do
  (left, right) <- mayWithLoc (peekLoc t) $ isOSum t
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  let injTy' = if tag then left' else right'
  inj' <- check inj injTy' SafeL
  let t' = OSum {left = left', right = right'}
  x <- fresh
  return
    ( t',
      SafeL,
      lets_
        [(x, injTy', SafeL, inj')]
        OInj {mTy = Just t', inj = V x, ..}
    )
typing OInj {..} (Just t') Nothing = do
  whenJust mTy $ \t -> do
    t'' <- checkKind t OblivK
    equate t' t''
  (left, right) <- isOSum t'
  -- We have to check @t'@ again because @left@ and @right@ may not be in core
  -- taype ANF, after normalization (in 'isOSum').
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  let injTy' = if tag then left' else right'
  inj' <- check inj injTy' SafeL
  x <- fresh
  return
    ( t',
      SafeL,
      lets_
        [(x, injTy', SafeL, inj')]
        -- The type annotation in oblivious injection is always in an oblivious
        -- sum form for convenience.
        OInj {mTy = Just (OSum {left = left', right = right'}), inj = V x, ..}
    )
typing OCase {..} mt Nothing = do
  (condTy', _, cond') <- infer_ cond (Just SafeL)
  (left, right) <- mayWithLoc (peekLoc cond) $ isOSum condTy'
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  (xl, lBody) <- unbind1 lBnd
  (xr, rBody) <- unbind1 rBnd
  (bodyTy', _, lBody') <-
    extendCtx1 xl left' SafeL lBinder $
      typing lBody mt (Just LeakyL)
  rBody' <-
    extendCtx1 xr right' SafeL rBinder $
      check rBody bodyTy' LeakyL
  x <- fresh
  return
    ( bodyTy',
      LeakyL,
      lets_
        [(x, OSum {left = left', right = right'}, SafeL, cond')]
        OCase
          { mTy = Just bodyTy',
            cond = V x,
            lBnd = abstract_ xl lBody',
            rBnd = abstract_ xr rBody',
            ..
          }
    )
typing Tape {..} mt Nothing = do
  (t', _, e') <- typing expr mt (Just LeakyL)
  void $ checkKind t' OblivK
  x <- fresh
  return
    ( t',
      SafeL,
      lets_
        [(x, t', LeakyL, e')]
        Tape {expr = V x}
    )
typing Loc {..} mt ml = withLoc loc $ withCur expr $ typing expr mt ml
typing Asc {..} Nothing ml = do
  ty' <- kinded ty
  (l, e') <- check_ expr ty' ml
  return (ty', l, e')

-- Check label.
typing e mt (Just l') = do
  -- Note that we never try to infer type while checking label, if both type and
  -- label are given. We assume no rule only does that.
  (t', l, e') <- typing e mt Nothing
  (t',l',) <$> mayPromote l' t' l e'

-- Check type but infer label.
typing e (Just t) Nothing = do
  (t', l', e') <- infer e
  equate t t'
  return (t', l', e')

-- Failed to infer the type.
typing _ Nothing Nothing =
  err
    [ [DD "Could not infer the type"],
      [DD "Perhaps you should add some type annotations"]
    ]

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
  NonEmpty [(Name, Ty Name, Label, Maybe Binder)] ->
  NonEmpty [(Name, Ty Name, Label, Maybe Binder)] ->
  NonEmpty (Ty Name) ->
  TcM (Ty Name)
-- Do not need to perform 'whnf' or strip 'Loc' for product and pi-types,
-- because they are not oblivious types, and @bodyTy0@ is in core taype ANF.
depGen gen ctxs argss branchTs@(Prod {} :| _) = do
  (leftTs, rightTs) <- NE.unzip <$> mapM isProd branchTs
  left <- depGen gen ctxs argss leftTs
  right <- depGen gen ctxs argss rightTs
  return Prod {..}
depGen gen ctxs argss branchTs@(Pi {label, binder} :| _) = do
  res <- mapM isPi branchTs
  let (argTs, labels, _, bnds) = NE.unzip4 res
      binderLabel = fromJust label
  unless (all (label ==) labels) $
    err
      [ [ DD "All branches are functions,",
          DD "but some function arguments have different leakage labels"
        ]
      ]
  x <- fresh
  argTy <- depGen gen ctxs argss argTs
  let bodies = instantiateName x <$> bnds
      ctxs' =
        NE.zipWith
          (\(ty, _, b, _) ctx -> (x, ty, binderLabel, b) : ctx)
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
  NonEmpty [(Name, Ty Name, Label, Maybe Binder)] ->
  NonEmpty [(Name, Ty Name, Label, Maybe Binder)] ->
  Ty Name ->
  TcM (NonEmpty (Ty Name))
-- Similar to 'depGen', do not need to perform 'whnf' or strip 'Loc' for
-- product and pi-types.
depMatch match ctxs argss Prod {..} = do
  leftTs <- depMatch match ctxs argss left
  rightTs <- depMatch match ctxs argss right
  return $ NE.zipWith Prod leftTs rightTs
depMatch match ctxs argss Pi {..} = do
  argTs <- depMatch match ctxs argss ty
  (x, body) <- unbind1 bnd
  let binderLabel = fromJust label
      ctxs' =
        NE.zipWith
          (\argTy ctx -> (x, argTy, binderLabel, binder) : ctx)
          argTs
          ctxs
  bodies <- depMatch match ctxs' argss body
  return $
    NE.zipWith
      ( \argTy body' ->
          Pi
            { ty = argTy,
              label = Just binderLabel,
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
  typeNoDep `catchError` \Err {errMsg = noDepMsg} ->
    case mt of
      Just t ->
        checkDep t `catchError` \Err {errMsg = checkMsg} ->
          ( do
              a <- inferDep
              equate t (proj a)
              return a
          )
            `catchError` \Err {errMsg = inferMsg} ->
              err $
                [ noDepMsgH,
                  [DD noDepMsg],
                  []
                ]
                  <> checkMsgHs t
                  <> [ [DD checkMsg],
                       [],
                       inferMsgH,
                       [DD inferMsg],
                       [],
                       gaveupMsg
                     ]
      _ ->
        inferDep `catchError` \Err {errMsg = inferMsg} ->
          err
            [ noDepMsgH,
              [DD noDepMsg],
              [],
              inferMsgH,
              [DD inferMsg],
              [],
              gaveupMsg
            ]
  where
    noDepMsgH =
      [DD "Tried to type the expression without dependent types, but:"]
    checkMsgHs t =
      [ [ DH "Tried to check the expression against the dependent type",
          DC t
        ],
        [DD "But"]
      ]
    inferMsgH =
      [DD "Tried to infer a dependent type for the expression, but:"]
    gaveupMsg = [DD "Gave up after all attemps"]

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
kinding TBool Nothing = return (PublicK, TBool)
kinding OBool Nothing = return (OblivK, OBool)
kinding TInt Nothing = return (PublicK, TInt)
kinding OInt Nothing = return (OblivK, OInt)
kinding GV {..} Nothing =
  lookupGSig ref >>= \case
    Just ADTDef {} -> return (PublicK, GV {..})
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not an ADT"]]
    _ ->
      err [[DD "Type", DQ ref, DD "is not in scope"]]
kinding Prod {..} Nothing = do
  (leftKind, left') <- inferKind left
  (rightKind, right') <- inferKind right
  return (leftKind \/ rightKind \/ PublicK, Prod {left = left', right = right'})
kinding OProd {..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, OProd {left = left', right = right'})
kinding OSum {..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, OSum {left = left', right = right'})
kinding Pi {..} Nothing = do
  ty' <- kinded ty
  (x, body) <- unbind1 bnd
  l <- labeling label
  body' <- extendCtx1 x ty' l binder $ kinded body
  return (MixedK, Pi {ty = ty', label = Just l, bnd = abstract_ x body', ..})
kinding App {..} Nothing = do
  (ref, ty) <-
    maybeGV fn >>= \case
      Just (ref, OADTDef {..}) -> return (ref, ty)
      Just (ref, _) ->
        err [[DD "Definition", DQ ref, DD "is not an oblivious ADT"]]
      _ -> err [[DH "Type application is not an oblivious ADT", DC fn]]
  -- Currently we only support a single argument for OADTs.
  arg <- case args of
    [arg] -> return arg
    _ -> errArity TypeApp ref (length args) 1
  arg' <- check arg ty SafeL
  x <- fresh
  return
    ( OblivK,
      lets_
        [(x, ty, SafeL, arg')]
        App {fn = GV ref, args = [V x], appKind = Just TypeApp}
    )
kinding Let {..} Nothing = do
  checkLabel label SafeL
  mTy' <- mapM kinded mTy
  (rhsTy', _, rhs') <- typing rhs mTy' (Just SafeL)
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x rhsTy' SafeL binder $ checkKind body OblivK
  return
    ( OblivK,
      Let
        { mTy = Just rhsTy',
          label = Just SafeL,
          rhs = rhs',
          bnd = abstract_ x body',
          ..
        }
    )
kinding Ite {..} Nothing = do
  cond' <- check cond TBool SafeL
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  x <- fresh
  return
    ( OblivK,
      lets_
        [(x, TBool, SafeL, cond')]
        Ite {cond = V x, left = left', right = right', ..}
    )
kinding PCase {..} Nothing = do
  (condTy', _, cond') <- infer_ cond (Just SafeL)
  (left', right') <- mayWithLoc (peekLoc cond) $ isProd condTy'
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCtx [(xl, left', SafeL, lBinder), (xr, right', SafeL, rBinder)] $
      checkKind body OblivK
  x <- fresh
  return
    ( OblivK,
      lets_
        [(x, Prod {left = left', right = right'}, SafeL, cond')]
        PCase {cond = V x, bnd2 = abstract_ (xl, xr) body', ..}
    )
kinding Case {..} Nothing = do
  (condTy', _, cond') <- infer_ cond (Just SafeL)
  (ref, ctors) <- isCaseCond cond condTy'
  joinedAlts <- joinAlts alts ctors
  alts' <- mapM kindCaseAlt joinedAlts
  x <- fresh
  return
    ( OblivK,
      lets_
        [(x, GV ref, SafeL, cond')]
        Case {cond = V x, alts = alts', ..}
    )
  where
    -- Kind check an alternative.
    kindCaseAlt (ctor, paraTypes, binders, bnd) = do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      body' <-
        extendCtx (zip4 xs paraTypes (replicate n SafeL) binders) $
          checkKind body OblivK
      return CaseAlt {bnd = abstract_ xs body', ..}
kinding Loc {..} mt = withLoc loc $ withCur expr $ kinding expr mt
-- Check kind.
kinding t (Just k) = do
  (k', t') <- inferKind t
  unless (k' `leq` k) $
    err
      [ [DD "Could not match kind"],
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

-- | Infer the type of an expression.
infer :: Expr Name -> TcM (Ty Name, Label, Expr Name)
infer e = typing e Nothing Nothing

-- | Infer the type of an expression, with possibly label.
infer_ :: Expr Name -> Maybe Label -> TcM (Ty Name, Label, Expr Name)
infer_ e = typing e Nothing

-- | Check the type and label of an expression.
check :: Expr Name -> Ty Name -> Label -> TcM (Expr Name)
check e t l = snd <$> check_ e t (Just l)

-- | Check the type of an expression, with possibly label.
check_ :: Expr Name -> Ty Name -> Maybe Label -> TcM (Label, Expr Name)
check_ e t ml = typing e (Just t) ml <&> \(_, l, e') -> (l, e')

-- | Infer the kind of a type.
inferKind :: Ty Name -> TcM (Kind, Ty Name)
inferKind t = kinding t Nothing

-- | Check the kind of a type.
checkKind :: Ty Name -> Kind -> TcM (Ty Name)
checkKind t k = kinding t (Just k) <&> snd

-- | Make sure a type is kinded, but do not care what the kind is.
kinded :: Ty Name -> TcM (Ty Name)
kinded t = inferKind t <&> snd

-- | Infer label if not privided.
labeling :: Maybe Label -> TcM Label
labeling l = do
  Env {..} <- ask
  return $ fromMaybe label l

-- | Check label.
checkLabel :: Maybe Label -> Label -> TcM ()
checkLabel ml l' = whenJust ml $ \l ->
  when (l' /= l) $
    err
      [ [DD "Could not match the leakage label"],
        [DH "Expected", DC l'],
        [DH "Got", DC l]
      ]

checkArity :: AppKind -> Text -> [b] -> [c] -> TcM ()
checkArity appKind ref args paraTypes =
  let m = length args
      n = length paraTypes
   in unless (m == n) $ errArity appKind ref m n

----------------------------------------------------------------
-- Equality check

-- | Check the equivalence of two expressions.
--
-- They must be already well-kinded or well-typed, and in core taype.
equate :: Expr Name -> Expr Name -> TcM ()
equate e e' | e == e' = pass
equate e e' = do
  nf <- whnf e
  nf' <- whnf e'
  go nf nf'
  where
    go nf@GV {} nf' = equateGV nf nf'
    go nf nf'@GV {} = equateGV nf nf'
    go nf@App {} nf' = equateApp nf nf'
    go nf nf'@App {} = equateApp nf nf'
    go Pi {ty, bnd} Pi {ty = ty', bnd = bnd'} = do
      equate ty ty'
      (_, body, body') <- unbind1With bnd bnd'
      equate body body'
    go Lam {bnd} Lam {bnd = bnd'} = do
      (_, body, body') <- unbind1With bnd bnd'
      equate body body'
    go Let {rhs, bnd} Let {rhs = rhs', bnd = bnd'} = do
      equate rhs rhs'
      (_, body, body') <- unbind1With bnd bnd'
      equate body body'
    go
      Ite {cond, left, right}
      Ite {cond = cond', left = left', right = right'} = do
        equate cond cond'
        equate left left'
        equate right right'
    go Case {cond, alts} Case {cond = cond', alts = alts'}
      | length alts == length alts' = do
        equate cond cond'
        -- Since both case expressions are in core taype, the alternatives are
        -- in canonical order.
        NE.zipWithM_ goAlt alts alts'
      where
        goAlt
          CaseAlt {ctor, binders, bnd}
          CaseAlt {ctor = ctor', binders = binders', bnd = bnd'}
            | ctor == ctor' && length binders == length binders' = do
              let n = length binders
              (_, body, body') <- unbindManyWith n bnd bnd'
              equate body body'
        goAlt _ _ = errEquate
    go
      OIte {cond, left, right}
      OIte {cond = cond', left = left', right = right'} = do
        equate cond cond'
        equate left left'
        equate right right'
    go Prod {left, right} Prod {left = left', right = right'} = do
      equate left left'
      equate right right'
    go Pair {left, right} Pair {left = left', right = right'} = do
      equate left left'
      equate right right'
    go PCase {cond, bnd2} PCase {cond = cond', bnd2 = bnd2'} = do
      equate cond cond'
      (_, body, body') <- unbind2With bnd2 bnd2'
      equate body body'
    go OProd {left, right} OProd {left = left', right = right'} = do
      equate left left'
      equate right right'
    go OPair {left, right} OPair {left = left', right = right'} = do
      equate left left'
      equate right right'
    go OPCase {cond, bnd2} OPCase {cond = cond', bnd2 = bnd2'} = do
      equate cond cond'
      (_, body, body') <- unbind2With bnd2 bnd2'
      equate body body'
    go OSum {left, right} OSum {left = left', right = right'} = do
      equate left left'
      equate right right'
    go OInj {tag, inj} OInj {tag = tag', inj = inj'}
      | tag == tag' = equate inj inj'
    go
      OCase {cond, lBnd, rBnd}
      OCase {cond = cond', lBnd = lBnd', rBnd = rBnd'} = do
        equate cond cond'
        (_, lBody, lBody') <- unbind1With lBnd lBnd'
        (_, rBody, rBody') <- unbind1With rBnd rBnd'
        equate lBody lBody'
        equate rBody rBody'
    go
      Mux {cond, left, right}
      Mux {cond = cond', left = left', right = right'} = do
        equate cond cond'
        equate left left'
        equate right right'
    go Promote {expr} Promote {expr = expr'} = equate expr expr'
    go Tape {expr} Tape {expr = expr'} = equate expr expr'
    go nf nf' | nf == nf' = pass
    go _ _ = errEquate

    -- Equate two expressions, but throw away the error messages.
    equate_ t t' = equate t t' `catchError` const errEquate

    -- Equate two expressions with at least one being global variable.
    equateGV nf nf' | nf == nf' = pass
    equateGV nf nf' =
      tryUnfold nf >>= \case
        Just expr -> equate_ expr nf'
        _ ->
          tryUnfold nf' >>= \case
            Just expr' -> equate_ nf expr'
            _ -> errEquate

    -- Equate two expressions with at least one being application.
    equateApp :: Expr Name -> Expr Name -> TcM ()
    equateApp nf nf' = do
      equateApp_ nf nf' `catchError` \appErr ->
        tryUnfoldApp nf >>= \case
          Just expr -> equate_ expr nf'
          _ ->
            tryUnfoldApp nf' >>= \case
              Just expr' -> equate_ nf expr'
              _ -> throwError appErr

    equateApp_ App {fn, args} App {fn = fn', args = args'}
      | length args == length args' = do
        equate fn fn'
        zipWithM_ equate args args'
    equateApp_ _ _ = errEquate

    errEquate =
      err
        [ [DD "Could not match the type"],
          [DH "Expected", DC e],
          [DH "Got", DC e']
        ]

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
whnf e@App {args = arg : args, ..} = do
  nf <- whnf fn
  case nf of
    Lam {..} ->
      whnf App {fn = instantiate_ arg bnd, ..}
    App {fn = nf', args = args'} ->
      return App {fn = nf', args = args' <> args, ..}
    _ -> return e {fn = nf}
whnf Let {..} = whnf $ instantiate_ rhs bnd
whnf Ite {..} = do
  nf <- whnf cond
  case nf of
    BLit {..} -> if bLit then whnf left else whnf right
    _ -> return Ite {cond = nf, ..}
whnf Case {..} = do
  nf <- whnf cond
  let fb = Case {cond = nf, ..}
  case nf of
    App {fn = GV {..}, ..} -> go ref args fb
    GV {..} -> go ref [] fb
    _ -> return fb
  where
    go ref args fb =
      case find (\CaseAlt {..} -> ctor == ref) alts of
        Just CaseAlt {ctor = _, ..}
          | length binders == length args ->
            whnf $ instantiate_ args bnd
        _ -> return fb
whnf PCase {..} = do
  nf <- whnf cond
  case nf of
    Pair {..} -> whnf $ instantiate_ (left, right) bnd2
    _ -> return PCase {cond = nf, ..}
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

-- | Build a series of let bindings, given the bindings and body. If the list of
-- bindings is empty, simply return the body.
lets_ :: [(Name, Ty Name, Label, Expr Name)] -> Expr Name -> Expr Name
lets_ = flip $ foldr go
  where
    go (x, t, l, rhs) body =
      Let
        { mTy = Just t,
          label = Just l,
          binder = Nothing,
          bnd = abstract_ x body,
          ..
        }

maybeGV :: MonadReader Env m => Expr Name -> m (Maybe (NamedDef Name))
maybeGV GV {..} = (ref,) <<$>> lookupGSig ref
maybeGV Loc {..} = maybeGV expr
maybeGV _ = return Nothing

-- | Check if a type is a pi-type and return its components.
--
-- Unlike other dependent type theory, we do not perform weak head normalization
-- here because it is unnecessary in our case: dependent types can only be
-- kinded as oblivious while pi-type is kinded as mixed. On the other hand, if
-- the given type is in core taype ANF, the returned types are also in core
-- taype ANF.
isPi :: Ty Name -> TcM (Ty Name, Maybe Label, Maybe Binder, Scope () Ty Name)
isPi Pi {..} = return (ty, label, binder, bnd)
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
isProd Prod {..} = return (left, right)
isProd Loc {..} = isProd expr
isProd t =
  err
    [ [DD "Expecting a pair"],
      [DH "But instead got", DC t]
    ]

-- | Check if a type is an oblivious product type and return its components.
isOProd :: Ty Name -> TcM (Ty Name, Ty Name)
isOProd t = do
  nf <- whnf t
  case nf of
    OProd {..} -> return (left, right)
    _ ->
      err
        [ [DD "Expecting an oblivious product"],
          [DH "But instead got", DC t]
        ]

-- | Check if a type is an oblivious sum type and return its components.
isOSum :: Ty Name -> TcM (Ty Name, Ty Name)
isOSum t = do
  nf <- whnf t
  case nf of
    OSum {..} -> return (left, right)
    _ ->
      err
        [ [DD "Expecting an oblivious sum"],
          [DH "But instead got", DC t]
        ]

-- | Check if an expression with its type is a discriminee to an ADT case
-- analysis, and return the ADT name and the constructors.
isCaseCond :: Expr Name -> Ty Name -> TcM (Text, NonEmpty (Text, [Expr Name]))
isCaseCond cond condTy =
  maybeGV condTy >>= \case
    Just (ref, ADTDef {..}) -> return (ref, ctors)
    _ ->
      mayWithLoc (peekLoc cond) $
        err
          [ [ DH "The discriminee to the pattern matching is not an ADT",
              DC cond
            ],
            [DH "It has type", DC condTy]
          ]

-- | Promote an expression to a higher label if it is the case. If the target
-- label is lower, then throw an error.
mayPromote :: Label -> Ty Name -> Label -> Expr Name -> TcM (Expr Name)
mayPromote l' t l e | l < l' = do
  x <- fresh
  return $ lets_ [(x, t, l, e)] $ Promote (V x)
mayPromote l' _ l e = checkLabel (Just l) l' >> return e

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
  NonEmpty (CaseAlt Expr a) ->
  NonEmpty (Text, [Ty a]) ->
  TcM (NonEmpty (Text, [Ty a], [Maybe Binder], Scope Int Expr a))
joinAlts alts ctors =
  let (result, missing, rest) = foldr go ([], [], toList alts) ctors
      (dups, unknowns) =
        partition (isJust . (`lookup` toList ctors)) $
          rest <&> \CaseAlt {..} -> ctor
   in case nonEmpty result of
        Just r | null missing && null rest -> do
          forM_ r $ \(ctor, paraTypes, binders, _) ->
            checkArity CtorApp ctor binders paraTypes
          return r
        _ ->
          err $
            [ DH "Some constructors are missing from this pattern matching" :
              andList missing
              | not $ null missing
            ]
              <> [ DH "This pattern matching has some duplicate constructors" :
                   andList dups
                   | not $ null dups
                 ]
              <> [ DH "Some constructors do not belong to this ADT" :
                   andList unknowns
                   | not $ null unknowns
                 ]
  where
    go (ctor, paraTypes) (result, missing, rest) =
      case findAndDel (match ctor) rest of
        Just (CaseAlt {ctor = _, ..}, rest') ->
          ((ctor, paraTypes, binders, bnd) : result, missing, rest')
        _ -> (result, ctor : missing, rest)
    match key CaseAlt {..} = ctor == key

peekLoc :: Expr Name -> Maybe Int
peekLoc Loc {..} = Just loc
peekLoc _ = Nothing

notAppearIn :: Ty Name -> [(Name, Ty Name, Label, Maybe Binder)] -> TcM ()
notAppearIn ty args = do
  Env {options} <- ask
  let xs =
        [ nameOrBinder options x binder
          | (x, _, _, binder) <- args,
            x `elem` ty
        ]
  unless (null xs) $
    err
      [ [DH "Some free variables appear in the inferred type", DC ty],
        DH "These variables are" : andList xs,
        [DD "Could not type this expression without dependent types"]
      ]

depOops :: a
depOops = oops "The number of branches do not match"

depMatchErr :: Ty Name -> TcM a
depMatchErr t =
  err
    [ [ DH "Dependent type does not match the expression",
        DC t
      ]
    ]

----------------------------------------------------------------
-- Definitions checker

-- | Type check all global definitions.
checkDefs :: Options -> Defs Name -> ExceptT Err IO (GCtx Name)
checkDefs options@Options {..} defs = runDcM options $ do
  gsctx <- preCheckDefs defs
  gctx <- go gsctx mempty defs
  return $
    if optNoFlattenLets
      then gctx
      else runFreshM $ mapMGCtxDef flattenLets gctx
  where
    -- Type checking definitions are done in the order of the given definitions.
    -- They can freely refer to the signatures of all definitions, allowing for
    -- (mutual) recursion. However, the definitions that have not been checked
    -- yet will not be unfolded during type equivalence check.
    go _ gdctx [] = return gdctx
    go gsctx gdctx ((name, _) : defs') = do
      -- use the definition in the signature context because the signatures
      -- there have already been checked.
      let def =
            fromMaybe
              (oops $ "Definition " <> name <> " does not exist")
              (lookupGCtx name gsctx)
      def' <- lift $ runTcM (initEnv options gsctx gdctx) $ checkDef def
      gdctx' <- extendGCtx1 gdctx name def'
      go gsctx gdctx' defs'

-- | Type check a global definition.
--
-- The signature of this definition must be checked already.
--
-- The returned definition must be in core taype ANF.
checkDef :: Def Name -> TcM (Def Name)
checkDef FunDef {..} = do
  -- Guess a label for inference.
  let l = case attr of
        SectionAttr -> LeakyL
        RetractionAttr -> SafeL
        SafeAttr -> SafeL
        LeakyAttr -> LeakyL
  expr' <- withLabel l $ check expr ty (fromJust label)
  return FunDef {expr = expr', ..}
checkDef OADTDef {..} = do
  (x, body) <- unbind1 bnd
  body' <-
    withLabel SafeL $
      extendCtx1 x ty SafeL binder $ checkKind body OblivK
  return OADTDef {bnd = abstract_ x body', ..}
-- 'ADTDef' and 'CtorDef' have been checked in pre-checker, and 'BuiltinDef'
-- does not need to be checked.
checkDef def = return def

-- | Pre-check all global signatures to ensure they are well-formed, and their
-- types are well-kinded and in core taype ANF.
preCheckDefs :: Defs Name -> DcM (GCtx Name)
preCheckDefs allDefs = do
  options <- ask
  -- First we check if any pattern matchings have conflicting pattern varaibles.
  lift $
    forM_ allDefs $
      secondM $
        runTcM (initEnv options mempty mempty) . noDupPattenVars
  -- We need to pre-check all ADTs first, because they can mutually refer to
  -- each other but do not contain dependent types.
  let (adtDefs, otherDefs) = partition isADTDef allDefs
  -- Note that @gctx@ trivially satisfies the invariant for global signature
  -- context, because it only contains ADTs (and prelude) at the moment.
  gctx <- extendGCtx preludeGCtx adtDefs
  adtDefs' <-
    lift $
      forM adtDefs $
        secondM $
          runTcM (initEnv options gctx mempty) . preCheckDef
  -- Extend global signature context with the ADTs and their constructors. Note
  -- that the types of all constructors are already in the right form after
  -- pre-check.
  gctx' <- extendGCtx preludeGCtx $ foldMap adtWithCtors adtDefs'
  -- Now we pre-check the rest of signatures in order.
  go gctx' otherDefs
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
      def' <- lift $ runTcM (initEnv options gctx mempty) $ preCheckDef def
      gctx' <- extendGCtx1 gctx name def'
      go gctx' defs

-- | Pre-check a global definition signature.
preCheckDef :: Def Name -> TcM (Def Name)
preCheckDef FunDef {..} = do
  ty' <- go
  checkLabel label label'
  return FunDef {ty = ty', label = Just label', ..}
  where
    go = case attr of
      SectionAttr -> preCheckSecRetType True ty
      RetractionAttr -> preCheckSecRetType False ty
      _ -> withLabel label' $ kinded ty
    label' = case attr of
      SectionAttr -> SafeL
      RetractionAttr -> LeakyL
      SafeAttr -> SafeL
      LeakyAttr -> LeakyL
preCheckDef ADTDef {..} = do
  ctors' <- forM ctors $ secondM $ mapM (`checkKind` PublicK)
  return ADTDef {ctors = ctors', ..}
preCheckDef OADTDef {..} = do
  ty' <- checkKind ty PublicK
  return OADTDef {ty = ty', ..}
preCheckDef _ = oops "Pre-checking constructor or builtin definitions"

-- | Pre-type check the signature of a section or retraction function.
--
-- The first argument is 'True' if checking section, otherwise checking
-- retraction.

-- NOTE: be careful! The location information for the two outermost pi-types is
-- erased.
preCheckSecRetType :: Bool -> Ty Name -> TcM (Ty Name)
preCheckSecRetType b t = do
  -- A section/retraction must be a function type with two arguments.
  (ty1, label1, binder1, bnd1) <- isPi t
  -- The first argument is the public view which must be public with safe label.
  ty1' <- checkKind ty1 PublicK
  checkLabel label1 SafeL
  (x1, body1) <- unbind1 bnd1
  (ty2, label2, binder2, bnd2) <- isPi body1
  -- The second argument of a section must be public with leaky label, while
  -- that of a retraction must be oblivious with safe label.
  let l = if b then LeakyL else SafeL
  ty2' <-
    extendCtx1 x1 ty1' SafeL binder1 $
      checkKind ty2 (if b then PublicK else OblivK)
  checkLabel label2 l
  (x2, body2) <- unbind1 bnd2
  -- The result of a section function must be oblivious, while that of a
  -- retraction must be public.
  bnd2' <-
    extendCtx [(x1, ty1', SafeL, binder1), (x2, ty2', l, binder2)] $
      checkKind body2 (if b then OblivK else PublicK)
  return
    Pi
      { ty = ty1',
        label = Just SafeL,
        binder = binder1,
        bnd =
          abstract_ x1 $
            Pi
              { ty = ty2',
                label = Just l,
                binder = binder2,
                bnd = abstract_ x2 bnd2'
              }
      }

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
        "Definition" <+> dquotes (pretty name) <+> "has already been defined at"
          <> hardline
          <> pretty (renderFancyLocation file code (getDefLoc def'))
    _ -> return $ insertGCtx name def gctx

extendGCtx ::
  (MonadError Err m, MonadReader Options m) =>
  GCtx Name ->
  Defs Name ->
  m (GCtx Name)
extendGCtx = foldlM $ uncurry . extendGCtx1

-- | Check if there are pattern matchings with duplicate patten variables.
noDupPattenVars :: Def Name -> TcM ()
noDupPattenVars = void . transformBiM go
  where
    go :: Expr Name -> TcM (Expr Name)
    go e@Case {..} = do
      forM_ alts $ \CaseAlt {..} ->
        whenJust (findDupBinderName (catMaybes binders)) $ \case
          Named loc name ->
            withCur e $
              withLoc loc $
                err [[DH "Found conflicting pattern variables", DC name]]
          _ -> oops "Anonymous binders cannot be duplicate"
      return e
    go e = return e

-- | Flatten all nested let bindings and remove single variable bindings.
--
-- If the input is in core taype ANF, the result must still be in core taype
-- ANF.
flattenLets :: MonadFresh m => Def Name -> m (Def Name)
flattenLets = transformBiM go
  where
    go e@Let {..} = case rhs of
      V {..} -> return $ instantiateName name bnd
      GV {..} -> return $ instantiate_ (GV ref) bnd
      Let
        { mTy = mTyN,
          label = labelN,
          rhs = rhsN,
          binder = binderN,
          bnd = bndN
        } -> do
          (x, bodyN) <- unbind1 bndN
          body' <- go Let {rhs = bodyN, ..}
          return
            Let
              { mTy = mTyN,
                label = labelN,
                rhs = rhsN,
                binder = binderN,
                bnd = abstract_ x body'
              }
      _ -> return e
    go e = return e

----------------------------------------------------------------
-- Error reporting

data D
  = -- | Display a document.
    DD Doc
  | -- | Display a document followed by a colon and possibly new line.
    DH Doc
  | -- | Display a 'Cutie' instance.
    forall a. Cutie a => DC a
  | -- | Display a quoted 'Cutie' instance.
    forall a. Cutie a => DQ a

class Cutie a where
  cutie :: a -> TcM Doc
  default cutie :: Cute a => a -> TcM Doc
  cutie a = do
    Env {..} <- ask
    n <- getFresh
    return $ contCuteM options n $ cute a

instance Cutie Int

instance Cutie Text

instance Cutie Kind where
  cutie k = return $ show k <+> parens (pretty k)

instance Cutie Label where
  cutie l = return $ show l <+> parens (pretty l)

instance Cutie (Expr Text)

instance Cutie (TCtx Text)

instance Cutie (Expr Name) where
  cutie = cutie <=< mapM renderName

instance Cutie (TCtx Int) where
  cutie = cutie <=< mapM renderName

instance Cutie D where
  cutie (DD doc) = return doc
  cutie (DH doc) = return $ doc <> colon
  cutie (DC e) = cutie e
  cutie (DQ e) = dquotes <$> cutie e

instance Cutie [D] where
  cutie [] = return mempty
  cutie (d : ds) = do
    doc <- cutie d
    rest <- cutie ds
    return $
      case d of
        DH _ -> hang $ doc <> sep1 rest
        _ -> doc <> softline <> rest

instance Cutie [[D]] where
  cutie dss = do
    docs <- mapM cutie dss
    return $ sepWith hardline docs

err_ :: (MonadError Err m) => Int -> Doc -> m a
err_ errLoc errMsg =
  throwError
    Err
      { errCategory = "Typing Error",
        ..
      }

err :: [[D]] -> TcM a
err dss = do
  Env {..} <- ask
  doc <- displayMsg dss
  err_ loc doc

_debug :: [[D]] -> TcM ()
_debug dss = do
  Env {..} <- ask
  doc <- displayMsg dss
  printDoc options $ "Debug" <> colon <> hardline <> doc <> hardline <> hardline
{-# WARNING _debug "'_debug' remains in code" #-}

displayMsg :: [[D]] -> TcM Doc
displayMsg dss = do
  Env {..} <- ask
  doc <- cutie dss
  curDoc <- cutie $ DC cur
  tctxDoc <- cutie tctx
  return $
    doc <> hardline <> hardline
      <> hang ("When checking expression" <> colon <> sep1 curDoc)
      <> hardline
      <> hardline
      <> tctxDoc

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

andList :: [Text] -> [D]
andList [] = []
andList [x] = [DC x]
andList [x, y] = [DC x, DD "and", DC y]
andList (x : xs) = DC (x <> ",") : andList xs

-- | The definition checking monad
type DcM = ReaderT Options (ExceptT Err IO)

runDcM :: Options -> DcM a -> ExceptT Err IO a
runDcM = usingReaderT

-- | The type checking monad
type TcM = FreshT (ReaderT Env (ExceptT Err IO))

runTcM :: Env -> TcM a -> ExceptT Err IO a
runTcM env m = runReaderT (runFreshT m) env

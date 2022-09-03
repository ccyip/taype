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
module Taype.TypeChecker (checkDefs) where

import Algebra.Lattice
import Algebra.PartialOrd
import Bound
import Control.Monad.Error.Class
import Data.HashMap.Strict ((!?))
import qualified Data.HashMap.Strict as M
import Data.List (lookup, partition, zip4, zipWith3)
import Prettyprinter hiding (Doc, hang, indent)
import Relude.Extra.Bifunctor
import Relude.Extra.Tuple
import Taype.Cute
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.Prelude
import Taype.Syntax

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
    _ -> oops $ "Local variable not in scope: " <> show name
typing e@GV {..} Nothing Nothing =
  lookupDef ref >>= \case
    Just FunDef {..} -> return (ty, mustLabel label, e)
    Just CtorDef {..} -> do
      checkArity CtorApp ref [] paraTypes
      return
        ( GV dataType,
          SafeL,
          App {fn = e, args = [], appKind = Just CtorApp}
        )
    Just BuiltinDef {..} -> do
      checkArity BuiltinApp ref [] paraTypes
      return
        ( resType,
          SafeL,
          App {fn = e, args = [], appKind = Just BuiltinApp}
        )
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not a term"]]
    _ ->
      err [[DD "Variable", DQ ref, DD "is not in scope"]]
typing Lam {mTy = Just binderTy, ..} Nothing ml = do
  -- This is the label of the binder, not the label of the whole lambda.
  binderLabel <- labeling label
  (_, binderTy') <- inferKind binderTy
  (x, body) <- unbind1 bnd
  (tBody', l', body') <-
    extendCtx1 x binderTy' binderLabel binder $
      typing body Nothing ml
  return
    ( Pi
        { ty = binderTy',
          label = Just binderLabel,
          bnd = abstract1 x tBody',
          ..
        },
      l',
      Lam
        { mTy = Just binderTy',
          label = Just binderLabel,
          bnd = abstract1 x body',
          ..
        }
    )
typing Lam {..} (Just t) ml = do
  (binderTy', binderLabel, _, tBnd') <- isPi t
  let binderLabel' = mustLabel binderLabel
  -- If the binder label is given, it has to agree with the one in the pi-type.
  checkLabel label binderLabel'
  whenJust mTy $ \binderTy -> do
    (_, t') <- inferKind binderTy
    -- If the binder type is given, it has to agree with the one in the pi-type.
    mayWithLoc (peekLoc binderTy) $
      equate binderTy' t'
  (x, body, tBody') <- unbind1With bnd tBnd'
  (l, body') <-
    extendCtx1 x binderTy' binderLabel' binder $
      check body tBody' ml
  return
    ( Pi
        { ty = binderTy',
          label = Just binderLabel',
          bnd = abstract1 x tBody',
          ..
        },
      l,
      Lam
        { mTy = Just binderTy',
          label = Just binderLabel',
          bnd = abstract1 x body',
          ..
        }
    )
typing App {..} Nothing ml =
  maybeGV fn >>= \case
    Just (ctor, CtorDef {..}) ->
      typePolyApp ctor paraTypes (GV dataType) JoinStrategy CtorApp
    Just (f, BuiltinDef {..}) ->
      typePolyApp f paraTypes resType strategy BuiltinApp
    _ -> typeFnApp
  where
    typePolyApp f paraTypes resType strat appKind' = do
      checkArity appKind' f args paraTypes
      -- TODO: quite messy here
      let ml' = case strat of
            JoinStrategy -> ml
            _ -> Just SafeL
      res <- zipWithM (\arg ty -> typing arg (Just ty) ml') args paraTypes
      xs <- freshes $ length res
      let (ts, ls, _) = unzip3 res
          l' = foldl' (\/) (fromMaybe SafeL ml') ls
      es' <- forM res $ \(t, l, e) -> mayPromote l' t l e
      let bindings = zipWith3 (\x t e -> (x, t, l', e)) xs ts es'
          l = case strat of
            LeakyStrategy -> LeakyL
            SafeStrategy -> SafeL
            _ -> l'
          l'' = fromMaybe l ml
      e' <-
        mayPromote l'' resType l $
          mayLets
            bindings
            App
              { fn = GV f,
                args = V <$> xs,
                appKind = Just $ fromMaybe appKind' appKind
              }
      return
        ( resType,
          l'',
          e'
        )
    typeFnApp = do
      (tFn', l', fn') <- typing fn Nothing ml
      (res, t') <- go args tFn'
      xs <- freshes (length args)
      let bindings = zipWith (\x (t, l, e) -> (x, t, l, e)) xs res
      x <- fresh
      return
        ( t',
          l',
          mayLets
            ((x, tFn', l', fn') : bindings)
            App
              { fn = V x,
                args = V <$> xs,
                appKind = Just FunApp
              }
        )
    go [] t = return ([], t)
    go (arg : args') t = do
      (argTy, argLabel, _, bnd) <- isPi t
      (argTy', argLabel', arg') <-
        typing arg (Just argTy) (Just (mustLabel argLabel))
      -- Unfortunately we have to kind the pi-type body here even though it is
      -- well-kinded, because it may not be in core taype ANF after
      -- instantiation.
      (_, body') <- inferKind (instantiate1 arg' bnd)
      (res, t') <- go args' body'
      return ((argTy', argLabel', arg') : res, t')
typing Let {..} Nothing ml = do
  (rhsTy', rhsLabel', rhs') <- typing rhs mTy label
  (x, body) <- unbind1 bnd
  (t, l', body') <- extendCtx1 x rhsTy' rhsLabel' binder $ typing body Nothing ml
  -- Unfortunately, we have to kind @t@ again even though it is kinded, because
  -- it may not be in core taype ANF after instantiation.
  (_, t') <- inferKind $ substitute x rhs' t
  return
    ( t',
      l',
      Let
        { mTy = Just rhsTy',
          label = Just rhsLabel',
          rhs = rhs',
          bnd = abstract1 x body',
          ..
        }
    )
-- TODO: do not support dependent types
typing Ite {..} Nothing ml = do
  (_, condLabel, cond') <- typing cond (Just TBool) ml
  (leftTy', leftLabel, left') <- typing left Nothing ml
  (rightTy', rightLabel, right') <- typing right Nothing ml
  equate leftTy' rightTy'
  let l' = condLabel \/ leftLabel \/ rightLabel
  left'' <- mayPromote l' leftTy' leftLabel left'
  right'' <- mayPromote l' rightTy' rightLabel right'
  x <- fresh
  return
    ( leftTy',
      l',
      mayLets
        [(x, TBool, condLabel, cond')]
        Ite
          { mTy = Just leftTy',
            cond = V x,
            left = left'',
            right = right''
          }
    )
typing Pair {..} mt ml = do
  (mLeftTy, mRightTy) <- mapM isProd mt <&> (\x -> (fst <$> x, snd <$> x))
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
      mayLets
        [ (xl, leftTy', l', left''),
          (xr, rightTy', l', right'')
        ]
        Pair {left = V xl, right = V xr}
    )
-- TODO: do not support dependent type yet
typing PCase {..} Nothing ml = do
  (condTy', condLabel, cond') <- typing cond Nothing ml
  (leftTy', rightTy') <- mayWithLoc (peekLoc cond) $ isProd condTy'
  ((xl, xr), body) <- unbind2 bnd2
  (t', l, body') <-
    extendCtx
      [ (xl, leftTy', condLabel, lBinder),
        (xr, rightTy', condLabel, rBinder)
      ]
      $ typing body Nothing ml
  -- @t'@ cannot refer to @xl@ or @xr@, otherwise it would be dependent type.
  notAppearIn [xl, xr] t'
  let l' = condLabel \/ l
  body'' <- mayPromote l' t' l body'
  x <- fresh
  return
    ( t',
      l',
      mayLets
        [(x, Prod {left = leftTy', right = rightTy'}, condLabel, cond')]
        PCase
          { mTy = Just t',
            cond = V x,
            bnd2 = abstract_ (xl, xr) body'',
            ..
          }
    )
typing Case {..} Nothing ml = do
  (condTy', condLabel, cond') <- typing cond Nothing ml
  (ref, ctors) <-
    maybeGV condTy' >>= \case
      -- TODO
      Just (ref, ADTDef {..}) -> return (ref, ctors)
      _ ->
        mayWithLoc (peekLoc cond) $
          err
            [ [ DH "The discriminee to the pattern matching is not an ADT",
                DC cond
              ],
              [DH "It has type", DC condTy']
            ]
  augAlts <- joinAlts alts ctors
  res <- mapM (typeCaseAlt condLabel) augAlts
  let ts' = res <&> \(_, _, _, t, _, _) -> t
      t' = head ts'
  equateMany ts'
  forM_ res $ \(_, _, xs, t, _, _) -> notAppearIn xs t
  let l' = flipfoldl' (\(_, _, _, _, l, _) -> (l \/)) condLabel res
  alts' <- mapM (promote l') res
  x <- fresh
  return
    ( t',
      l',
      mayLets
        [(x, GV {..}, condLabel, cond')]
        Case
          { mTy = Just t',
            cond = V x,
            alts = alts'
          }
    )
  where
    typeCaseAlt condLabel (ctor, paraTypes, binders, bnd) = do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      (t', l, body') <-
        extendCtx (zip4 xs paraTypes (replicate n condLabel) binders) $
          typing body Nothing ml
      return (ctor, binders, xs, t', l, body')
    promote l' (ctor, binders, xs, t', l, body') = do
      body'' <- mayPromote l' t' l body'
      return CaseAlt {bnd = abstract_ xs body'', ..}
-- TODO: checking mode is possible
typing Mux {..} Nothing Nothing = do
  (_, _, cond') <- typing cond (Just OBool) (Just SafeL)
  (leftTy', _, left') <- typing left Nothing (Just SafeL)
  (rightTy', _, right') <- typing right Nothing (Just SafeL)
  equate leftTy' rightTy'
  void $ checkKind leftTy' OblivK
  x <- fresh
  xl <- fresh
  xr <- fresh
  return
    ( leftTy',
      SafeL,
      mayLets
        [ (x, OBool, SafeL, cond'),
          (xl, leftTy', SafeL, left'),
          (xr, rightTy', SafeL, right')
        ]
        Mux {cond = V x, left = V xl, right = V xr}
    )
-- TODO: checking mode is possible
typing OIte {..} Nothing Nothing = do
  (_, _, cond') <- typing cond (Just OBool) (Just SafeL)
  (leftTy', _, left') <- typing left Nothing (Just LeakyL)
  (rightTy', _, right') <- typing right Nothing (Just LeakyL)
  equate leftTy' rightTy'
  x <- fresh
  xl <- fresh
  xr <- fresh
  return
    ( leftTy',
      LeakyL,
      mayLets
        [ (x, OBool, SafeL, cond'),
          (xl, leftTy', LeakyL, left'),
          (xr, rightTy', LeakyL, right')
        ]
        OIte {cond = V x, left = V xl, right = V xr}
    )
typing OPair {..} mt Nothing = do
  (mLeftTy, mRightTy) <- mapM isOProd mt <&> (\x -> (fst <$> x, snd <$> x))
  (leftTy', _, left') <- typing left mLeftTy (Just SafeL)
  (rightTy', _, right') <- typing right mRightTy (Just SafeL)
  void $ checkKind leftTy' OblivK
  void $ checkKind rightTy' OblivK
  xl <- fresh
  xr <- fresh
  return
    ( OProd {left = leftTy', right = rightTy'},
      SafeL,
      mayLets
        [ (xl, leftTy', SafeL, left'),
          (xr, rightTy', SafeL, right')
        ]
        OPair {left = V xl, right = V xr}
    )
typing OPCase {..} Nothing ml = do
  (condTy', _, cond') <- typing cond Nothing (Just SafeL)
  (leftTy', rightTy') <- mayWithLoc (peekLoc cond) $ isOProd condTy'
  ((xl, xr), body) <- unbind2 bnd2
  (t', l, body') <-
    extendCtx
      [ (xl, leftTy', SafeL, lBinder),
        (xr, rightTy', SafeL, rBinder)
      ]
      $ typing body Nothing ml
  x <- fresh
  return
    ( t',
      l,
      mayLets
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
  (_, _, inj') <- typing inj (Just injTy') (Just SafeL)
  let t' = OSum {left = left', right = right'}
  x <- fresh
  return
    ( t',
      SafeL,
      mayLets
        [(x, injTy', SafeL, inj')]
        OInj {mTy = Just t', inj = V x, ..}
    )
typing OInj {..} (Just t') Nothing = do
  whenJust mTy $ equate t'
  (left, right) <- isOSum t'
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  let injTy' = if tag then left' else right'
  (_, _, inj') <- typing inj (Just injTy') (Just SafeL)
  x <- fresh
  return
    ( t',
      SafeL,
      mayLets
        [(x, injTy', SafeL, inj')]
        OInj {mTy = Just t', inj = V x, ..}
    )
-- TODO: checking mode is possible
typing OCase {..} Nothing Nothing = do
  (condTy', _, cond') <- typing cond Nothing (Just SafeL)
  (left, right) <- mayWithLoc (peekLoc cond) $ isOSum condTy'
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  (xl, lBody) <- unbind1 lBnd
  (xr, rBody) <- unbind1 rBnd
  (lBodyTy', _, lBody') <-
    extendCtx1 xl left' SafeL lBinder $
      typing lBody Nothing (Just LeakyL)
  (rBodyTy', _, rBody') <-
    extendCtx1 xr right' SafeL rBinder $
      typing rBody Nothing (Just LeakyL)
  equate lBodyTy' rBodyTy'
  x <- fresh
  return
    ( lBodyTy',
      LeakyL,
      mayLets
        [(x, OSum {left = left', right = right'}, SafeL, cond')]
        OCase
          { mTy = Just lBodyTy',
            cond = V x,
            lBnd = abstract1 xl lBody',
            rBnd = abstract1 xr rBody',
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
      mayLets
        [(x, t', LeakyL, e')]
        Tape {expr = V x}
    )
typing Loc {..} mt ml = withLoc loc $ withCur expr $ typing expr mt ml
typing Asc {..} Nothing ml = do
  (_, ty') <- inferKind ty
  (l, expr') <- check expr ty' ml
  return (ty', l, expr')

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
  lookupDef ref >>= \case
    Just ADTDef {} -> return (PublicK, GV {..})
    Just _ ->
      err [[DD "Definition", DQ ref, DD "is not an ADT"]]
    _ ->
      err [[DD "Type", DQ ref, DD "is not in scope"]]
kinding Prod {..} Nothing = do
  (lk, left') <- inferKind left
  (rk, right') <- inferKind right
  return (lk \/ rk \/ PublicK, Prod {left = left', right = right'})
kinding OProd {..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, OProd {left = left', right = right'})
kinding OSum {..} Nothing = do
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  return (OblivK, OSum {left = left', right = right'})
kinding Pi {..} Nothing = do
  (_, ty') <- inferKind ty
  (x, body) <- unbind1 bnd
  l <- labeling label
  (_, body') <- extendCtx1 x ty' l binder $ inferKind body
  return (MixedK, Pi {ty = ty', label = Just l, bnd = abstract1 x body', ..})
kinding App {..} Nothing = do
  (ref, ty) <-
    maybeGV fn >>= \case
      Just (ref, OADTDef {..}) -> return (ref, ty)
      Just (ref, _) ->
        err
          [ [ DD "Definition",
              DQ ref,
              DD "is not an oblivious ADT"
            ]
          ]
      _ -> err [[DH "Type application is not an oblivious ADT", DC fn]]
  arg <- case args of
    [arg] -> return arg
    _ -> errArity TypeApp ref (length args) 1
  (_, arg') <- check arg ty (Just SafeL)
  x <- fresh
  return
    ( OblivK,
      Let
        { mTy = Just ty,
          label = Just SafeL,
          rhs = arg',
          binder = Nothing,
          bnd =
            abstract1 x $
              App
                { appKind = Just TypeApp,
                  fn = GV ref,
                  args = [V x]
                }
        }
    )
kinding Let {..} Nothing = do
  checkLabel label SafeL
  mTy' <- snd <<$>> mapM inferKind mTy
  (t', _, rhs') <- typing rhs mTy' (Just SafeL)
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x t' SafeL binder $ checkKind body OblivK
  return
    ( OblivK,
      Let
        { mTy = Just t',
          label = Just SafeL,
          rhs = rhs',
          bnd = abstract1 x body',
          ..
        }
    )
kinding Ite {..} Nothing = do
  (_, cond') <- check cond TBool (Just SafeL)
  left' <- checkKind left OblivK
  right' <- checkKind right OblivK
  x <- fresh
  return
    ( OblivK,
      Let
        { mTy = Just TBool,
          label = Just SafeL,
          rhs = cond',
          binder = Nothing,
          bnd =
            abstract1 x $
              Ite
                { cond = V x,
                  left = left',
                  right = right',
                  ..
                }
        }
    )
kinding PCase {..} Nothing = do
  (t', _, cond') <- typing cond Nothing (Just SafeL)
  -- NOTE: even though 'isProd' performs weak head normalization, the two
  -- components are still in core taype ANF. This is because @t'@ is never an
  -- oblivious type if it is a product and well-kinded, so the head of @t'@ has
  -- to be @Prod@ already, with possibly @Loc@ wrappers.
  (left', right') <- mayWithLoc (peekLoc cond) $ isProd t'
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCtx [(xl, left', SafeL, lBinder), (xr, right', SafeL, rBinder)] $
      checkKind body OblivK
  x <- fresh
  return
    ( OblivK,
      Let
        { mTy = Just (Prod {left = left', right = right'}),
          label = Just SafeL,
          rhs = cond',
          binder = Nothing,
          bnd =
            abstract1 x $
              PCase
                { cond = V x,
                  bnd2 = abstract_ (xl, xr) body',
                  ..
                }
        }
    )
kinding Case {..} Nothing = do
  (t', _, cond') <- typing cond Nothing (Just SafeL)
  (ref, ctors) <-
    maybeGV t' >>= \case
      -- TODO
      Just (ref, ADTDef {..}) -> return (ref, ctors)
      _ ->
        mayWithLoc (peekLoc cond) $
          err
            [ [ DH "The discriminee to the pattern matching is not an ADT",
                DC cond
              ],
              [DH "It has type", DC t']
            ]
  augAlts <- joinAlts alts ctors
  alts' <- mapM kindCaseAlt augAlts
  x <- fresh
  return
    ( OblivK,
      Let
        { mTy = Just (GV ref),
          label = Just SafeL,
          rhs = cond',
          binder = Nothing,
          bnd = abstract1 x Case {cond = V x, alts = alts', ..}
        }
    )
  where
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

-- | Infer the type of the expression.
infer :: Expr Name -> TcM (Ty Name, Label, Expr Name)
infer e = typing e Nothing Nothing

-- | Check the type of the expression.
check :: Expr Name -> Ty Name -> Maybe Label -> TcM (Label, Expr Name)
check e t ml = typing e (Just t) ml <&> \(_, l, e') -> (l, e')

-- | Infer the kind of the type.
inferKind :: Ty Name -> TcM (Kind, Ty Name)
inferKind t = kinding t Nothing

-- | Check the kind of the type.
checkKind :: Ty Name -> Kind -> TcM (Ty Name)
checkKind t k = kinding t (Just k) <&> snd

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

mustLabel :: Maybe Label -> Label
mustLabel = fromMaybe $ oops "Label not available"

checkArity :: AppKind -> Text -> [b] -> [c] -> TcM ()
checkArity appKind ref args paraTypes =
  let m = length args
      n = length paraTypes
   in unless (m == n) $ errArity appKind ref m n

-- | Check the equivalence of two expressions. They must be already well-kinded
-- or well-typed.
equate :: Expr Name -> Expr Name -> TcM ()
equate e e' | e == e' = pass
equate e e' = do
  nf <- whnf e
  nf' <- whnf e'
  go nf nf'
  where
    go Pi {ty, bnd} Pi {ty = ty', bnd = bnd'} = do
      equate ty ty'
      (_, body, body') <- unbind1With bnd bnd'
      equate body body'
    go Lam {bnd} Lam {bnd = bnd'} = do
      (_, body, body') <- unbind1With bnd bnd'
      equate body body'
    go App {fn, args} App {fn = fn', args = args'}
      | length args == length args' = do
        equate fn fn'
        zipWithM_ equate args args'
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
        let sortedAlts = sortOn (\CaseAlt {..} -> ctor) $ toList alts
            sortedAlts' = sortOn (\CaseAlt {..} -> ctor) $ toList alts'
        zipWithM_ goAlt sortedAlts sortedAlts'
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
    go nf nf' | nf == nf' = pass
    go
      Mux {cond, left, right}
      Mux {cond = cond', left = left', right = right'} = do
        equate cond cond'
        equate left left'
        equate right right'
    go Promote {expr} Promote {expr = expr'} = equate expr expr'
    go Tape {expr} Tape {expr = expr'} = equate expr expr'
    go _ _ = errEquate
    errEquate =
      err
        [ [DD "Could not match the type"],
          [DH "Expected", DC e],
          [DH "Got", DC e']
        ]

equateMany :: NonEmpty (Expr Name) -> TcM ()
equateMany (e :| es) = forM_ es $ equate e

-- | Weak head normal form.
--
-- We do not assume the expression is kinded or typed. This function never
-- fails.
--
-- At the moment, oblivious constructs are not normalized. While possible, it is
-- mostly unnecessary in practice.
whnf :: Expr Name -> TcM (Expr Name)
whnf e@GV {..} =
  lookupDef ref >>= \case
    Just FunDef {..} -> whnf expr
    _ -> return e
whnf App {args = [], ..} = whnf fn
whnf e@App {args = arg : args, ..} = do
  nf <- whnf fn
  case nf of
    Lam {..} ->
      whnf App {fn = instantiate1 arg bnd, ..}
    GV {..} ->
      lookupDef ref >>= \case
        Just OADTDef {..} -> whnf $ instantiate1 arg bnd
        _ -> return e {fn = nf}
    App {fn = nf', args = args'} ->
      return App {fn = nf', args = args' <> args, ..}
    _ -> return e {fn = nf}
whnf Let {..} = whnf $ instantiate1 rhs bnd
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
-- TODO
whnf e = return e

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

maybeGV :: MonadReader Env m => Expr Name -> m (Maybe (Text, Def Name))
maybeGV GV {..} = (ref,) <<$>> lookupDef ref
maybeGV Loc {..} = maybeGV expr
maybeGV _ = return Nothing

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

mayPromote :: Label -> Ty Name -> Label -> Expr Name -> TcM (Expr Name)
mayPromote l' t l e | l < l' = do
  x <- fresh
  return
    Let
      { mTy = Just t,
        label = Just l,
        rhs = e,
        binder = Nothing,
        bnd = abstract1 x $ Promote (V x)
      }
mayPromote l' _ l e = checkLabel (Just l) l' >> return e

mayLets :: [(Name, Ty Name, Label, Expr Name)] -> Expr Name -> Expr Name
mayLets = flip $ foldr go
  where
    go (x, t, l, rhs) body =
      Let
        { mTy = Just t,
          label = Just l,
          binder = Nothing,
          bnd = abstract1 x body,
          ..
        }

-- | Join the pattern matching alternatives and the corresponding ADT's
-- constructors list.
--
-- Each entry of the returned list, when succeeds, consists of the constructor's
-- name, its parameter types, binders and pattern matching body. The order of
-- this list follows that of the constructors list.
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
        partition (isJust . flip lookup (toList ctors)) $
          rest <&> \CaseAlt {..} -> ctor
   in case nonEmpty result of
        Just r | null missing && null rest -> do
          forM_ r $ \(ctor, paraTypes, binders, _) ->
            checkArity CtorApp ctor binders paraTypes
          return r
        _ ->
          err $
            [ DH "Some constructors are missing from this pattern matching" :
              listD missing
              | not $ null missing
            ]
              <> [ DH "This pattern matching has some duplicate constructors" :
                   listD dups
                   | not $ null dups
                 ]
              <> [ DH "Some constructors do not belong to this ADT" :
                   listD unknowns
                   | not $ null unknowns
                 ]
  where
    go (ctor, paraTypes) (result, missing, rest) =
      case findAndDel (match ctor) rest of
        Just (CaseAlt {ctor = _, ..}, rest') ->
          ((ctor, paraTypes, binders, bnd) : result, missing, rest')
        _ -> (result, ctor : missing, rest)
    match key CaseAlt {..} = ctor == key
    listD [] = []
    listD [x] = [DC x]
    listD [x, y] = [DC x, DD "and", DC y]
    listD (x : xs) = DC (x <> ",") : listD xs

findAndDel :: (a -> Bool) -> [a] -> Maybe (a, [a])
findAndDel _ [] = Nothing
findAndDel p (x : xs)
  | p x = Just (x, xs)
  | otherwise = second (x :) <$> findAndDel p xs

insertMany ::
  (Foldable t, Hashable k) => HashMap k v -> t (k, v) -> HashMap k v
insertMany = flipfoldl' $ uncurry M.insert

-- TODO
notAppearIn :: [Name] -> Expr Name -> TcM ()
notAppearIn xs e =
  when (any (`elem` xs) e) $ oops "do not support dependent types yet"

extendGCtx1 ::
  (MonadError Err m, MonadReader Options m) =>
  GCtx Name ->
  Text ->
  Def Name ->
  m (GCtx Name)
extendGCtx1 gctx name def =
  case gctx !? name of
    Just def' -> do
      Options {optFile = file, optCode = code} <- ask
      err_ (getDefLoc def) $
        "Definition" <+> dquotes (pretty name) <+> "has already been defined at"
          <> hardline
          <> pretty (renderFancyLocation file code (getDefLoc def'))
    _ -> return $ M.insert name def gctx

extendGCtx ::
  (MonadError Err m, MonadReader Options m) =>
  GCtx Name ->
  [(Text, Def Name)] ->
  m (GCtx Name)
extendGCtx = foldlM $ uncurry . extendGCtx1

-- | Type check all definitions.
checkDefs :: Options -> [(Text, Def Name)] -> ExceptT Err IO (GCtx a)
checkDefs options defs = runDcM options $ do
  gctx <- preCheckDefs defs
  defs' <- lift $ mapM (traverseToSnd (go gctx) . fst) defs
  return $ mustClosed "Global context" <$> insertMany gctx defs'
  where
    go gctx name =
      runTcM (initEnv options gctx) $
        checkDef $
          fromMaybe
            (oops $ "Definition " <> name <> " does not exist")
            (gctx !? name)

-- | Type check top-level definitions.
--
-- The associated type/type arguments of the given definition must be
-- well-kinded and in core taype ANF if the definition is a function,
-- constructor or OADT.
--
-- The returned definition must be in core taype ANF.
checkDef :: Def Name -> TcM (Def Name)
checkDef FunDef {..} = do
  let l = mustLabel label
  (_, expr') <- withLabel l $ check expr ty (Just l)
  return FunDef {expr = expr', ..}
checkDef OADTDef {..} = do
  (x, body) <- unbind1 bnd
  body' <-
    withLabel SafeL $
      extendCtx1 x ty SafeL binder $ checkKind body OblivK
  return OADTDef {bnd = abstract1 x body', ..}
-- 'ADTDef' and 'CtorDef' have been checked in pre-checker, and 'BuiltinDef'
-- does not need to be checked.
checkDef def = return def

-- | Pre-type check all definitions to ensure they are well-formed, and their
-- types are well-kinded and in core taype ANF.
preCheckDefs :: [(Text, Def Name)] -> DcM (GCtx Name)
preCheckDefs allDefs = do
  -- We need to pre-check all ADTs first, because they can mutually refer to
  -- each other but do not contain dependent types.
  let (adtDefs, otherDefs) = partition isADTDef allDefs
  -- Note that @gctx@ trivially satisfies the invariant for global context (i.e.
  -- function types, constructor and OADT type arguments are well-kinded and in
  -- core taype ANF), because it only contains ADTs (and prelude) at the moment.
  gctx <- extendGCtx preludeGCtx adtDefs
  options <- ask
  adtDefs' <- lift $
    forM adtDefs $
      \(name, def) ->
        (name,) <$> runTcM (initEnv options gctx) (preCheckDef def)
  -- Extend global context with the ADTs and their constructors. Note that the
  -- types of all constructors are already in the right form after pre-check.
  gctx' <- extendGCtx preludeGCtx $ foldMap adtWithCtors adtDefs'
  -- Now we pre-check the rest of definitions in order.
  go gctx' otherDefs
  where
    isADTDef (_, ADTDef {}) = True
    isADTDef _ = False
    adtWithCtors (name, def@ADTDef {..}) =
      let ctorDefs =
            ctors <&> second (\paraTypes -> CtorDef {dataType = name, ..})
       in (name, def) : toList ctorDefs
    adtWithCtors (_, _) = oops "Not an ADT definition"
    -- Pre-checking definitions except for ADTs is done in the order of the
    -- given definitions. While mutual recursion is allowed, the type of a
    -- definition should not refer to this definition itself, directly or
    -- transitively.
    go gctx [] = return gctx
    go gctx ((name, def) : defs) = do
      options <- ask
      def' <- lift $ runTcM (initEnv options gctx) $ preCheckDef def
      gctx' <- extendGCtx1 gctx name def'
      go gctx' defs

-- | pre-Check a top-level definition.
preCheckDef :: Def Name -> TcM (Def Name)
preCheckDef FunDef {..} = do
  ty' <- go
  checkLabel label label'
  return FunDef {ty = ty', label = Just label', ..}
  where
    go = case attr of
      SectionAttr -> preCheckSecRetType True ty
      RetractionAttr -> preCheckSecRetType False ty
      _ -> withLabel label' $ snd <$> inferKind ty
    label' = case attr of
      SectionAttr -> SafeL
      RetractionAttr -> LeakyL
      SafeAttr -> SafeL
      LeakyAttr -> LeakyL
preCheckDef ADTDef {..} = do
  ctors' <- mapM go ctors
  return ADTDef {ctors = ctors', ..}
  where
    go (ctor, paraTypes) = (ctor,) <$> mapM (`checkKind` PublicK) paraTypes
preCheckDef OADTDef {..} = do
  ty' <- checkKind ty PublicK
  return OADTDef {ty = ty', ..}
preCheckDef _ = oops "Pre-checking constructor or builtin definitions"

-- | Pre-type check the type of a section or retraction function.
--
-- The first argument is 'True' if checking section, otherwise checking
-- retraction.

-- NOTE: be careful! The location information for the two outermost pi-types is
-- erased
preCheckSecRetType :: Bool -> Ty Name -> TcM (Ty Name)
preCheckSecRetType b t = do
  -- A section/retraction must be a function type with two arguments.
  (typ1, label1, binder1, bnd1) <- isPi t
  -- The first argument is the public view which must be public with safe label.
  typ1' <- checkKind typ1 PublicK
  checkLabel label1 SafeL
  (x1, body1) <- unbind1 bnd1
  (typ2, label2, binder2, bnd2) <- isPi body1
  -- The second argument of a section must be public with leaky label, while
  -- that of a retraction must be oblivious with safe label.
  let l = if b then LeakyL else SafeL
  typ2' <-
    extendCtx1 x1 typ1' SafeL binder1 $
      checkKind typ2 (if b then PublicK else OblivK)
  checkLabel label2 l
  (x2, body2) <- unbind1 bnd2
  -- The result of a section function must be oblivious, while that of a
  -- retraction must be public.
  bnd2' <-
    extendCtx [(x1, typ1', SafeL, binder1), (x2, typ2', l, binder2)] $
      checkKind body2 (if b then OblivK else PublicK)
  return
    Pi
      { ty = typ1',
        label = Just SafeL,
        binder = binder1,
        bnd =
          abstract1 x1 $
            Pi
              { ty = typ2',
                label = Just l,
                binder = binder2,
                bnd = abstract1 x2 bnd2'
              }
      }

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
  cutie e = do
    Env {options, bctx} <- ask
    let e' = e <&> renderName options bctx
    cutie e'

instance Cutie (TCtx Int) where
  cutie tctx = do
    Env {options, bctx} <- ask
    let tctx' =
          bimapF
            (renderName options bctx)
            (first (renderName options bctx <$>))
            tctx
    cutie tctx'

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

renderName :: Options -> BCtx Name -> Name -> Text
renderName options bctx x = nameOrBinder options x $ lookup x bctx

peekLoc :: Expr Name -> Maybe Int
peekLoc Loc {..} = Just loc
peekLoc _ = Nothing

errArity :: AppKind -> Text -> Int -> Int -> TcM a
errArity appKind ref actual expected =
  let what = case appKind of
        CtorApp -> "constructor"
        BuiltinApp -> "builtin function"
        InfixApp -> "builtin function"
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

-- | The definition checking monad
type DcM = ReaderT Options (ExceptT Err IO)

runDcM :: Options -> DcM a -> ExceptT Err IO a
runDcM = usingReaderT

-- | The type checking monad
type TcM = FreshT (ReaderT Env (ExceptT Err IO))

runTcM :: Env -> TcM a -> ExceptT Err IO a
runTcM env m = runReaderT (runFreshT m) env

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Bidirectional type checker for Taype.
module Taype.TypeChecker
  ( typing,
    checkGCtx,
    preCheckGCtx,
  )
where

import Algebra.Lattice
import Algebra.PartialOrd
import Bound
import Control.Monad.Error.Class
import Data.List (zip4)
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.Syntax

-- | Type check an expression bidirectionally.
--
-- Both types (the second argument) and labels (the third argument) may be
-- inferred or checked. They are in inference mode if they are 'Nothing', or in
-- checking mode otherwise. This function returns the expression's type, label
-- and its full elaboration.
--
-- The given type must be well-kinded.
--
-- The returned type must be well-kinded and in core Taype ANF. It is also
-- equivalent to the given type if in type checking mode.
--
-- The returned label must be the same as the given label if in label checking
-- mode.
--
-- The returned expression must be in core Taype ANF. Of course, it must also be
-- typed by the returned type and label, and equivalent to the given expression.
typing ::
  Expr Name ->
  Maybe (Ty Name) ->
  Maybe Label ->
  TcM (Ty Name, Label, Expr Name)
typing ILit {..} Nothing Nothing = return (TInt, SafeL, ILit {..})
-- TODO: record location
typing Loc {..} mt ml = typing expr mt ml
-- Check label
typing e mt (Just l) = do
  (t', l', e') <- typing e mt Nothing
  if l' < l
    then do
      -- Promote label to a more permissive one
      x <- fresh
      return
        ( t',
          l,
          Let
            { mTy = Just t',
              label = Just l',
              rhs = e',
              binder = Nothing,
              bnd = abstract1 x $ Promote (V x)
            }
        )
    else checkLabel (Just l') l >> return (t', l, e')

-- Check type but infer label
typing e (Just t) Nothing = do
  (t', l', e') <- infer e
  equate t t'
  return (t', l', e')

-- Failed to infer the type
typing _ Nothing Nothing =
  -- TODO
  err "Cannot infer the type. Perhaps you should add type ascription"

-- | Kind check a type bidirectionally.
--
-- It is in inference mode if the second argument is 'Nothing', otherwise in
-- checking mode. This function returns the type's kind and its full
-- elaboration.
--
-- The given type must be sufficiently labeled.
--
-- The returned kind must be the same as the given kind if in checking mode.
--
-- The returned type must be in core Taype ANF. Of course, it must also be
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
    -- TODO
    Just _ -> err "definition is not ADT"
    Nothing -> err "no such definition"
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
  (_, body') <- extendCtx1 x ty' (mustLabel label) binder $ inferKind body
  return (MixedK, Pi {ty = ty', bnd = abstract1 x body', ..})
kinding App {..} Nothing = do
  ref <- isGV fn
  ty <-
    lookupDef ref >>= \case
      Just OADTDef {..} -> return ty
      -- TODO
      Just _ -> err "definition is not OADT"
      Nothing -> err "no such definition"
  arg <- case args of
    [arg] -> return arg
    -- TODO
    _ -> err "arity mismatch"
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
  (t', _, rhs') <- typing rhs mTy (Just SafeL)
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
  ifTrue' <- checkKind ifTrue OblivK
  ifFalse' <- checkKind ifFalse OblivK
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
                  ifTrue = ifTrue',
                  ifFalse = ifFalse',
                  ..
                }
        }
    )
kinding PCase {..} Nothing = do
  (t', _, cond') <- typing cond Nothing (Just SafeL)
  -- NOTE: even though 'isProd' performs weak head normalization, the two
  -- components are still in core Taype ANF. This is because @t'@ is never an
  -- oblivious type if it is a product and well-kinded, so the head of @t'@ has
  -- to be @Prod@ already, with possibly @Loc@ wrappers.
  (left', right') <- isProd t'
  (xl, xr, body) <- unbind2 bnd2
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
                  bnd2 = abstract2 xl xr body',
                  ..
                }
        }
    )
kinding Case {..} Nothing = do
  (t', _, cond') <- typing cond Nothing (Just SafeL)
  ref <- isGV t'
  ctors <-
    lookupDef ref >>= \case
      -- TODO
      Just ADTDef {..} -> do
        let go ctor =
              lookupDef ctor >>= \case
                Just CtorDef {paraTypes} -> return (ctor, paraTypes)
                Just _ -> err "not a constructor"
                _ -> err "no such definition"
        mapM go ctors
      -- TODO
      Just _ -> err "not an ADT"
      Nothing -> err "no such definition"
  case joinAlts alts ctors of
    -- TODO
    Left (_, _) -> err "constructors do not match"
    Right alts' -> do
      alts'' <- forM alts' $
        \(ctor, paraTypes, binders, bnd) -> do
          let n = length paraTypes
          unless (length binders == n) $ err "arguments do not match"
          (xs, body) <- unbindMany n bnd
          body' <-
            extendCtx (zip4 xs paraTypes (replicate n SafeL) binders) $
              checkKind body OblivK
          return $
            CaseAlt
              { bnd = abstractMany xs body',
                ..
              }
      x <- fresh
      return
        ( OblivK,
          Let
            { mTy = Just (GV ref),
              label = Just SafeL,
              rhs = cond',
              binder = Nothing,
              bnd =
                abstract1 x $
                  Case
                    { cond = V x,
                      alts = alts'',
                      ..
                    }
            }
        )
kinding Loc {..} mt = kinding expr mt
-- Check kind
kinding t (Just k) = do
  (k', t') <- inferKind t
  -- TODO
  unless (k' `leq` k) $ err "Kind mismatch"
  return (k, t')

-- Failed
kinding _ Nothing =
  -- TODO
  err "Cannot infer the kind"

-- | Infer the type of the expression
infer :: Expr Name -> TcM (Ty Name, Label, Expr Name)
infer e = typing e Nothing Nothing

-- | Check the type of the expression
check :: Expr Name -> Ty Name -> Maybe Label -> TcM (Label, Expr Name)
check e t ml = typing e (Just t) ml <&> \(_, l, e') -> (l, e')

-- | Infer the kind of the type
inferKind :: Ty Name -> TcM (Kind, Ty Name)
inferKind t = kinding t Nothing

-- | Check the kind of the type
checkKind :: Ty Name -> Kind -> TcM (Ty Name)
checkKind t k = kinding t (Just k) <&> snd

-- | Infer label if not privided
labeling :: Maybe Label -> TcM Label
labeling l = do
  l' <- getLabel
  return $ fromMaybe l' l

-- | Check label
checkLabel :: Maybe Label -> Label -> TcM ()
checkLabel Nothing _ = pass
-- TODO
checkLabel (Just l') l = when (l' /= l) $ err "label mismatch"

mustLabel :: Maybe Label -> Label
mustLabel = fromMaybe $ oops "Label not available"

-- | Check the equivalence of two expressions. They must be already well-kinded
-- or well-typed
equate :: Expr Name -> Expr Name -> TcM ()
equate e e' | e == e' = pass
-- TODO
equate _ _ = err "not equal"

-- | Weak head normal form
whnf :: Expr Name -> TcM (Expr Name)
whnf Loc {..} = whnf expr
whnf Asc {..} = whnf expr
-- TODO
whnf e = return e

isPi :: Ty Name -> TcM (Ty Name, Maybe Label, Maybe Binder, Scope () Ty Name)
isPi t = do
  tnf <- whnf t
  case tnf of
    Pi {..} -> return (ty, label, binder, bnd)
    -- TODO
    _ -> err "not a pi"

isGV :: Expr Name -> TcM Text
isGV e = do
  enf <- whnf e
  case enf of
    GV {..} -> return ref
    -- TODO
    _ -> err "not a global variable"

isProd :: Ty Name -> TcM (Ty Name, Ty Name)
isProd t = do
  tnf <- whnf t
  case tnf of
    Prod {..} -> return (left, right)
    -- TODO
    _ -> err "not a product"

-- | Join the pattern matching alternatives list and the constructors list with
-- their parameter types.
--
-- Each entry of the returned list, when succeeds, consists of the constructor's
-- name, its parameter types, binders and pattern matching body. The order of
-- this list follows that of the constructors list.
--
-- If the two lists do not match, this function fails with a list of
-- constructors that do not appear in the alternatives (i.e. non-exhausted), and
-- a list of constructors that do not appear in the constructors list or that
-- are duplicate.
joinAlts ::
  NonEmpty (CaseAlt Expr a) ->
  NonEmpty (Text, [Ty a]) ->
  Either
    ([Text], [Text])
    (NonEmpty (Text, [Ty a], [Maybe Binder], Scope Int Expr a))
joinAlts alts ctors =
  let (result, missing, alts') = foldr go ([], [], toList alts) ctors
   in case nonEmpty result of
        Just r | null missing && null alts' -> Right r
        _ -> Left (missing, alts' <&> \CaseAlt {..} -> ctor)
  where
    go (ctor, paraTypes) (result, missing, alts') =
      case findAndDel (match ctor) alts' of
        Just (CaseAlt {ctor = _, ..}, alts'') ->
          ((ctor, paraTypes, binders, bnd) : result, missing, alts'')
        _ -> (result, ctor : missing, alts')
    match key CaseAlt {..} = ctor == key

findAndDel :: (a -> Bool) -> [a] -> Maybe (a, [a])
findAndDel _ [] = Nothing
findAndDel p (x : xs)
  | p x = Just (x, xs)
  | otherwise = second (x :) <$> findAndDel p xs

-- | Type check all definitions in the global context.
checkGCtx :: Env -> ExceptT Err IO (GCtx a)
checkGCtx = checkGCtxWith checkDef

-- | Pre-type check all definitions in the global context.
preCheckGCtx :: Env -> ExceptT Err IO (GCtx a)
preCheckGCtx = checkGCtxWith preCheckDef

checkGCtxWith :: (Def Name -> TcM (Def Name)) -> Env -> ExceptT Err IO (GCtx a)
checkGCtxWith chk env@Env {..} = runTcM env $ mapM go gctx
  where
    go def = mustClosed "Definition" <$> chk def

-- | Type check top-level definitions.
--
-- The given definition must be sufficiently labeled.
--
-- The returned definition must be in core Taype ANF.
checkDef :: Def Name -> TcM (Def Name)
checkDef FunDef {..} = do
  -- TODO
  (_, ty') <- kinding ty Nothing
  -- TODO: ty or ty'?
  (_, expr') <- check expr ty label
  return FunDef {ty = ty', expr = expr', ..}
checkDef _ = undefined

-- | Pre-type check top-level definitions.
--
-- If the returned definition is a function definition, its type must be
-- sufficiently labeled, i.e. the top-level pi-types are labeled.
preCheckDef :: Def Name -> TcM (Def Name)
preCheckDef FunDef {..} = do
  ty' <- go
  checkLabel label label'
  return FunDef {ty = ty', label = Just label', ..}
  where
    go = case attr of
      SectionAttr -> preCheckSectionType ty
      RetractionAttr -> preCheckRetractionType ty
      _ -> withLabel label' $ preCheckType ty
    label' = case attr of
      SectionAttr -> SafeL
      RetractionAttr -> LeakyL
      SafeAttr -> SafeL
      LeakyAttr -> LeakyL
preCheckDef def = return def

preCheckType :: Ty Name -> TcM (Ty Name)
preCheckType Pi {..} = do
  t <- preCheckType ty
  (x, body) <- unbind1 bnd
  e <- preCheckType body
  l <- labeling label
  return
    Pi
      { label = Just l,
        ty = t,
        bnd = abstract1 x e,
        ..
      }
preCheckType Prod {..} = do
  left' <- preCheckType left
  right' <- preCheckType right
  return Prod {left = left', right = right'}
preCheckType Loc {..} = preCheckType expr
-- We do not go inside terms
preCheckType e = return e

-- NOTE: be careful! The location information for the two outermost pi-types is
-- erased
preCheckSecRetType :: Label -> Ty Name -> TcM (Ty Name)
preCheckSecRetType l t = do
  -- A section/retraction must be a function type with two arguments
  (typ1, label1, binder1, bnd1) <- isPi t
  -- All the calls to 'preCheckType' are bogus. If the argument types or the
  -- result type contain more pi-types, this is not a valid section/retraction
  -- function, which will be detected in the next phase. However, we pre-check
  -- them anyway to maintain the invariant
  typ1' <- preCheckType typ1
  -- The first argument is the public view which must have safe label
  checkLabel label1 SafeL
  (x1, body1) <- unbind1 bnd1
  (typ2, label2, binder2, bnd2) <- isPi body1
  typ2' <- preCheckType typ2
  -- The label of the second argument depends on whether it is section or
  -- retraction
  checkLabel label2 l
  (x2, body2) <- unbind1 bnd2
  bnd2' <- preCheckType body2
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

preCheckSectionType :: Ty Name -> TcM (Ty Name)
-- The second argument of a section should be leaky
preCheckSectionType = preCheckSecRetType LeakyL

preCheckRetractionType :: Ty Name -> TcM (Ty Name)
-- The second argument of a retraction should be safe
preCheckRetractionType = preCheckSecRetType SafeL

-- TODO
err :: MonadError Err m => Text -> m a
err errMsg = throwError Err {errLoc = -1, errCategory = "Typing Error", ..}

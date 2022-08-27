{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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
-- Bidirectional type checker for Taype.
module Taype.TypeChecker (checkDefs) where

import Algebra.Lattice
import Algebra.PartialOrd
import Bound
import Control.Monad.Error.Class
import Data.HashMap.Strict ((!?))
import qualified Data.HashMap.Strict as M
import Data.List (zip4)
import Relude.Extra.Tuple
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
  l <- labeling label
  (_, body') <- extendCtx1 x ty' l binder $ inferKind body
  return (MixedK, Pi {ty = ty', label = Just l, bnd = abstract1 x body', ..})
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
      Just ADTDef {..} -> return ctors
      -- TODO
      Just _ -> err "not an ADT"
      Nothing -> err "no such definition"
  augAlts <-
    case joinAlts alts ctors of
      -- TODO
      Left (_, _) -> err "constructors do not match"
      Right alts' -> return alts'
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
    kindCaseAlt (_, paraTypes, binders, _)
      -- TODO
      | length paraTypes /= length binders = err "arguments fo not match"
    kindCaseAlt (ctor, paraTypes, binders, bnd) = do
      let n = length paraTypes
      (xs, body) <- unbindMany n bnd
      body' <-
        extendCtx (zip4 xs paraTypes (replicate n SafeL) binders) $
          checkKind body OblivK
      return CaseAlt {bnd = abstractMany xs body', ..}
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

-- | Type check all definitions.
checkDefs :: Options -> [(Text, Def Name)] -> ExceptT Err IO (GCtx a)
checkDefs options defs = do
  gctx <- preCheckDefs options defs
  defs' <- mapM (traverseToSnd (go gctx) . fst) defs
  return $ mustClosed "Global context" $ fromList defs' `M.union` gctx
  where
    go gctx name =
      -- Label does not matter here.
      runTcM Env {ctx = [], bctx = [], label = LeakyL, ..} $
        checkDef $
          fromMaybe
            (oops $ "Definition " <> name <> " does not exist")
            (gctx !? name)

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

-- | Pre-type check all definitions to ensure they are well-formed, and their
-- types are well-kinded and in core Taype ANF.
preCheckDefs :: Options -> [(Text, Def Name)] -> ExceptT Err IO (GCtx Name)
preCheckDefs options = go preludeGCtx
  where
    go gctx [] = return gctx
    go gctx ((name, _) : _)
      | M.member name gctx =
        err $ "Definition " <> name <> " already exists"
    go gctx ((name, def) : defs) = do
      -- Label does not matter here.
      def' <-
        runTcM Env {ctx = [], bctx = [], label = SafeL, ..} $
          preCheckDef def
      go (M.insert name def' gctx) defs

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
preCheckDef def = undefined

-- NOTE: be careful! The location information for the two outermost pi-types is
-- erased

-- | Pre-type check the type of a section or retraction function.
--
-- The first argument is 'True' if checking section, otherwise checking
-- retraction.
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
  typ2' <- checkKind typ2 (if b then PublicK else OblivK)
  checkLabel label2 l
  (x2, body2) <- unbind1 bnd2
  -- The result of a section function must be oblivious, while that of a
  -- retraction must be public.
  bnd2' <- checkKind body2 (if b then OblivK else PublicK)
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

-- TODO
err :: MonadError Err m => Text -> m a
err errMsg = throwError Err {errLoc = -1, errCategory = "Typing Error", ..}

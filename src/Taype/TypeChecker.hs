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
import Data.List (partition, zip4)
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
-- The given type must be well-kinded and in core Taype ANF.
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
typing e@VUnit Nothing Nothing = return (TUnit, SafeL, e)
typing e@BLit {} Nothing Nothing = return (TBool, SafeL, e)
typing e@ILit {} Nothing Nothing = return (TInt, SafeL, e)
typing e@V {..} Nothing Nothing =
  lookupTy name >>= \case
    Just (t, l) -> return (t, l, e)
    -- TODO
    _ -> err "Variable not in scope"
typing e@GV {..} Nothing Nothing =
  lookupDef ref >>= \case
    Just FunDef {..} -> return (ty, mustLabel label, e)
    Just CtorDef {..}
      | null paraTypes ->
        return (GV dataType, SafeL, e)
    Just BuiltinDef {..}
      | null paraTypes ->
        return (resType, SafeL, e)
    -- TODO
    Just CtorDef {} -> err "Constructors need to be fully applied"
    Just BuiltinDef {} -> err "Builtin functions need to be fully applied"
    -- TODO
    Just _ -> err "Definition not a term"
    _ -> err "Definition not available"
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
  mTy' <- snd <<$>> mapM inferKind mTy
  -- If the binder type is given, it has to agree with the one in the pi-type.
  whenJust mTy' $ equate binderTy'
  (x, body) <- unbind1 bnd
  let tBody' = instantiate1Name x tBnd'
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
-- TODO: record location
typing Loc {..} mt ml = typing expr mt ml
typing Asc {..} Nothing ml = do
  (_, ty') <- inferKind ty
  -- TODO: ty (kinded, not in ANF, not fully annotated) or ty' (ANF)
  (l, expr') <- check expr ty' ml
  return (ty', l, expr')
-- Check label
typing e mt (Just l) = do
  -- Note that we never try to infer type but check label if both type and label
  -- are given. We assume no rule only does that.
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
  (ref, ty) <-
    maybeGV fn >>= \case
      Just (ref, OADTDef {..}) -> return (ref, ty)
      -- TODO
      _ -> err "definition is not OADT"
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
  (ref, ctors) <-
    maybeGV t' >>= \case
      -- TODO
      Just (ref, ADTDef {..}) -> return (ref, ctors)
      -- TODO
      _ -> err "not an ADT"
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
checkLabel ml l = whenJust ml $ \l' -> when (l' /= l) $ err "label mismatch"

mustLabel :: Maybe Label -> Label
mustLabel = fromMaybe $ oops "Label not available"

-- | Check the equivalence of two expressions. They must be already well-kinded
-- or well-typed.
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

-- Unlike other dependent type theory, we do not perform weak head normalization
-- here because it is unnecessary in our case: dependent types can only be
-- kinded as oblivious while pi-type is kinded as mixed. On the other hand, if
-- the given type is in core Taype ANF, the returned types are all in core Taype
-- ANF.
isPi :: Ty Name -> TcM (Ty Name, Maybe Label, Maybe Binder, Scope () Ty Name)
isPi Pi {..} = return (ty, label, binder, bnd)
isPi Loc {..} = isPi expr
isPi _ = err "not a pi"

maybeGV :: MonadReader Env m => Expr Name -> m (Maybe (Text, Def Name))
maybeGV GV {..} = (ref,) <<$>> lookupDef ref
maybeGV Loc {..} = maybeGV expr
maybeGV _ = return Nothing

-- Similar to 'isPi', product types are never oblivious types, so weak head
-- normalization is unnecessary. The returned types are in core Taype ANF if the
-- given type is so.
isProd :: Ty Name -> TcM (Ty Name, Ty Name)
isProd Prod {..} = return (left, right)
isProd Loc {..} = isProd expr
-- TODO
isProd _ = err "not a product"

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

insertMany ::
  (Foldable t, Hashable k) => HashMap k v -> t (k, v) -> HashMap k v
insertMany = flipfoldl' $ uncurry M.insert

extendGCtx1 :: MonadError Err m => GCtx Name -> Text -> Def Name -> m (GCtx Name)
extendGCtx1 gctx name _
  | M.member name gctx =
    -- TODO
    err $ "Definition " <> name <> " already exists"
extendGCtx1 gctx name def = return $ M.insert name def gctx

extendGCtx :: MonadError Err m => GCtx Name -> [(Text, Def Name)] -> m (GCtx Name)
extendGCtx = foldlM $ uncurry . extendGCtx1

-- | Type check all definitions.
checkDefs :: Options -> [(Text, Def Name)] -> ExceptT Err IO (GCtx a)
checkDefs options defs = do
  gctx <- preCheckDefs options defs
  defs' <- mapM (traverseToSnd (go gctx) . fst) defs
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
-- well-kinded and in core Taype ANF if the definition is a function,
-- constructor or OADT.
--
-- The returned definition must be in core Taype ANF.
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
-- types are well-kinded and in core Taype ANF.
preCheckDefs :: Options -> [(Text, Def Name)] -> ExceptT Err IO (GCtx Name)
preCheckDefs options allDefs = do
  -- We need to pre-check all ADTs first, because they can mutually refer to
  -- each other but do not contain dependent types.
  let (adtDefs, otherDefs) = partition isADTDef allDefs
  -- Note that @gctx@ trivially satisfies the invariant for global context (i.e.
  -- function types, constructor and OADT type arguments are well-kinded and in
  -- core Taype ANF), because it only contains ADTs (and prelude) at the moment.
  gctx <- extendGCtx preludeGCtx adtDefs
  adtDefs' <- forM adtDefs $
    \(name, def) -> (name,) <$> runTcM (initEnv options gctx) (preCheckDef def)
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
      def' <- runTcM (initEnv options gctx) $ preCheckDef def
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

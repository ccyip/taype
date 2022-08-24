{-# LANGUAGE FlexibleContexts #-}
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

import Bound
import Control.Monad.Error.Class
import Taype.Environment
import Taype.Error
import Taype.Fresh
import Taype.Syntax

-- | Bidirectionally type check an expression. It is in synthesis / inference
-- mode if the second argument is 'Nothing', or in checking mode otherwise.
-- Labels are always inferred. This function returns the well-kinded type of the
-- expression and the fully elaborated expression in core Taype ANF
typing :: Expr Name -> Maybe (Typ Name) -> TcM (Typ Name, Label, Expr Name)
typing ILit {..} Nothing = return (TInt, SafeL, ILit {..})

-- TODO
typing Loc{..} mt = typing expr mt

-- Checking
typing e (Just t) = do
  (t', l, e') <- infer e
  equate t t'
  return (t', l, e')

-- Failed to infer the type
typing _ Nothing =
  -- TODO
  err "Cannot infer the type. Perhaps you should add type ascription"

-- | Kind check a type. This function returns the kind of a type and its fully
-- elaborated counterpart in core Taype in ANF
kinding :: Typ Name -> TcM (Kind, Typ Name)
kinding TInt = return (PublicK, TInt)
kinding _ = wip

-- | Infer the type of the expression
infer :: Expr Name -> TcM (Typ Name, Label, Expr Name)
infer e = typing e Nothing

-- | Check the type of the expression
check :: Expr Name -> Typ Name -> TcM (Label, Expr Name)
check e t = typing e (Just t) <&> \(_, l, e') -> (l, e')

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

-- | Check the equivalence of two expressions
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

isPi :: Typ Name -> TcM (Typ Name, Maybe Label, Binder, Scope () Typ Name)
isPi t = do
  tnf <- whnf t
  case tnf of
    Pi {..} -> return (typ, label, binder, body)
    -- TODO
    _ -> err "not a pi"

-- | Type check all definitions in the global context
checkGCtx :: Env -> ExceptT Err IO (GCtx a)
checkGCtx = checkGCtxWith checkDef

-- | Fully elaborate top-level pi-types with labels and ensure they are well-formed
preCheckGCtx :: Env -> ExceptT Err IO (GCtx a)
preCheckGCtx = checkGCtxWith preCheckDef

checkGCtxWith :: (Def Name -> TcM (Def Name)) -> Env -> ExceptT Err IO (GCtx a)
checkGCtxWith chk env@Env {..} = runTcM env $ mapM go gctx
  where
    go def = mustClosed "Definition" <$> chk def

-- | Type check top-level definitions
checkDef :: Def Name -> TcM (Def Name)
checkDef FunDef {..} = do
  -- TODO
  (_, typ') <- kinding typ
  -- TODO: typ or typ'?
  (l, expr') <- check expr typ
  -- TODO: bidirectional label checking or convert label here
  checkLabel (Just l) $ mustLabel label
  return FunDef {typ = typ', expr = expr', ..}
checkDef _ = wip

-- | Pre-type check top-level definitions
preCheckDef :: Def Name -> TcM (Def Name)
preCheckDef FunDef {..} = do
  typ' <- go
  checkLabel label label'
  return FunDef {typ = typ', label = Just label', ..}
  where
    go = case attr of
      SectionAttr -> preCheckSectionType typ
      RetractionAttr -> preCheckRetractionType typ
      _ -> withLabel label' $ preCheckType typ
    label' = case attr of
      SectionAttr -> SafeL
      RetractionAttr -> LeakyL
      SafeAttr -> SafeL
      LeakyAttr -> LeakyL
preCheckDef def = return def

preCheckType :: Typ Name -> TcM (Typ Name)
preCheckType Pi {..} = do
  t <- preCheckType typ
  x <- fresh
  e <- preCheckType $ instantiate1Name x body
  l <- labeling label
  return
    Pi
      { label = Just l,
        typ = t,
        body = abstract1 x e,
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
preCheckSecRetType :: Label -> Typ Name -> TcM (Typ Name)
preCheckSecRetType l t = do
  -- A section/retraction must be a function type with two arguments
  (typ1, label1, binder1, body1) <- isPi t
  -- All the calls to 'preCheckType' are bogus. If the argument types or the
  -- result type contain more pi-types, this is not a valid section/retraction
  -- function, which will be detected in the next phase. However, we pre-check
  -- them anyway to maintain the invariant
  typ1' <- preCheckType typ1
  -- The first argument is the public view which must have safe label
  checkLabel label1 SafeL
  x1 <- fresh
  (typ2, label2, binder2, body2) <- isPi $ instantiate1Name x1 body1
  typ2' <- preCheckType typ2
  -- The label of the second argument depends on whether it is section or
  -- retraction
  checkLabel label2 l
  x2 <- fresh
  body2' <- preCheckType $ instantiate1Name x2 body2
  return
    Pi
      { typ = typ1',
        label = Just SafeL,
        binder = binder1,
        body =
          abstract1 x1 $
            Pi
              { typ = typ2',
                label = Just l,
                binder = binder2,
                body = abstract1 x2 body2'
              }
      }

preCheckSectionType :: Typ Name -> TcM (Typ Name)
-- The second argument of a section should be leaky
preCheckSectionType = preCheckSecRetType LeakyL

preCheckRetractionType :: Typ Name -> TcM (Typ Name)
-- The second argument of a retraction should be safe
preCheckRetractionType = preCheckSecRetType SafeL

-- TODO
err :: MonadError Err m => Text -> m a
err errMsg = throwError Err {errLoc = -1, errCategory = "Typing Error", ..}

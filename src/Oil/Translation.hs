{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Translate taype to OIL.
--
-- We use naming convention to translate definition names and references to the
-- corresponding leaky types and leaky case analysis definitions, and to resolve
-- promote and leaky if instances. This is more convenient than maintaining a
-- lookup table. The generated names contain characters that are illegal in the
-- taype identifiers to avoid name conflicts.
module Oil.Translation
  ( -- * Naming
    promPrefix,
    lIfPrefix,
    lCasePrefix,
    unsafePrefix,
    privPrefix,
    promName,
    lIfName,
    lCaseName,
    unsafeName,
    privName,

    -- * Translation
    toOilProgram,

    -- * Prelude
    prelude,
  )
where

import Data.Graph (graphFromEdges, reachable)
import Data.HashSet (member)
import Data.List (lookup)
import Data.Maybe (fromJust)
import GHC.List (zipWith3)
import Oil.Syntax
import Relude.Extra.Bifunctor
import Taype.Binder
import Taype.Common
import Taype.Environment (GCtx (..), TCtx (..), lookupGCtx)
import Taype.Name
import Taype.Plate
import Taype.Prelude
import qualified Taype.Syntax as T

----------------------------------------------------------------
-- Naming

promPrefix :: Text
promPrefix = leakyName "prom#"

lIfPrefix :: Text
lIfPrefix = leakyName "if#"

lCasePrefix :: Text
lCasePrefix = leakyName "case#"

unsafePrefix :: Text
unsafePrefix = "unsafe!"

privPrefix :: Text
privPrefix = "private!"

promName :: Text -> Text
promName = (promPrefix <>)

lIfName :: Text -> Text
lIfName = (lIfPrefix <>)

lCaseName :: Text -> Text
lCaseName = (lCasePrefix <>)

unsafeName :: Text -> Text
unsafeName = (unsafePrefix <>)

privName :: Text -> Text
privName = (privPrefix <>)

----------------------------------------------------------------
-- Environment for translation

data Env = Env
  { -- Taype global context
    gctx :: GCtx Name,
    -- Taype typing context
    tctx :: TCtx Name,
    -- Whether the translation is in the conceal/reveal phase.
    isCrust :: Bool,
    -- The current label
    label :: Label
  }

-- | The translation monad
type TslM = FreshT (Reader Env)

runTslM :: Env -> TslM a -> a
runTslM env m = runReader (runFreshT m) env

-- | Look up a taype definition in the global context.
--
-- Unlike the similar function in type checking, this function should always
-- succeed.
lookupGDef :: MonadReader Env m => Text -> m (T.Def Name)
lookupGDef x = fromJust . lookupGCtx x <$> asks gctx

-- | Look up a taype type and its label in the local context.
--
-- Unlike the Similar function in type checking, this function should always
-- succeed.
lookupLCtx :: MonadReader Env m => Name -> m (T.Ty Name, Label)
lookupLCtx x = do
  TCtx tctx <- asks tctx
  return $ fromJust $ lookup x tctx

-- | Look up a taype type and its label in both contexts.
--
-- The given taype expression should be a local or global variable.
--
-- If the translation is unsafe, the label is always 'SafeL'.
lookupTy :: MonadReader Env m => T.Expr Name -> m (T.Ty Name, Label)
lookupTy T.V {..} = lookupLCtx name >>= secondM toMayCrustLabel
lookupTy T.GV {..} =
  lookupGDef ref >>= \case
    T.FunDef {..} -> do
      l <- toMayCrustLabel $ fromJust label
      return (ty, l)
    _ -> oops "Not a function definition"
lookupTy _ = oops "Not a variable"

-- | Look up an ADT variable and its label.
--
-- The given taype expression should be a local or global variable.
--
-- This function does not return the constructor list as it is not used at
-- callsites.
lookupADT ::
  MonadReader Env m =>
  T.Expr Name ->
  m (Text, [[T.Expr Name]], Label)
lookupADT x = do
  (ty, l) <- lookupTy x
  case ty of
    T.GV {..} ->
      lookupGDef ref >>= \case
        T.ADTDef {..} -> return (ref, toList $ snd <$> ctors, l)
        _ -> oops "Not an ADT"
    _ -> oops "Not a global variable"

-- | Extend the taype typing context.
extendCtx ::
  MonadReader Env m => [(Name, T.Ty Name, Label)] -> m a -> m a
extendCtx xs = local go
  where
    go Env {tctx = TCtx tctx, ..} =
      Env {tctx = TCtx $ (xs <&> \(x, t, l) -> (x, (t, l))) <> tctx, ..}

-- | Extend the taype typing context with one entry.
extendCtx1 ::
  MonadReader Env m => Name -> T.Ty Name -> Label -> m a -> m a
extendCtx1 x t l = extendCtx [(x, t, l)]

getIsCrust :: MonadReader Env m => m Bool
getIsCrust = asks isCrust

withLabel :: MonadReader Env m => Label -> m a -> m a
withLabel l = local $ \Env {..} -> Env {label = l, ..}

getLabel :: MonadReader Env m => m Label
getLabel = do
  l <- asks label
  toMayCrustLabel l

toMayCrustLabel :: MonadReader Env m => Label -> m Label
toMayCrustLabel l = do
  b <- asks isCrust
  return $ if b then SafeL else l

----------------------------------------------------------------
-- Translating expressions and types

-- | Translate a taype expression with its label to the corresponding OIL
-- expression.
--
-- The taype expression is well-typed and in core taype ANF.
--
-- The resulting OIL expression should be typed by the corresponding translated
-- OIL type, under the translated typing context. The types and context are
-- translated according to 'toOilTy'.
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
  let binderLabel = fromJust label
      binderTy = fromJust mTy
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x binderTy binderLabel $ toOilExpr body
  return $ lamB x binder body'
toOilExpr T.App {fn = T.GV {..}, ..}
  | appKind == Just BuiltinApp || appKind == Just CtorApp = do
      ref' <- toMayLeakyGV ref
      return $ ref' @@ toOilVar <$> args
toOilExpr T.App {appKind = Just FunApp, ..} =
  return $ toOilVar fn @@ toOilVar <$> args
toOilExpr T.Let {..} = do
  let rhsLabel = fromJust label
      ty = fromJust mTy
  rhs' <- withLabel rhsLabel $ toOilExpr rhs
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x ty rhsLabel $ toOilExpr body
  return $ letB x binder rhs' body'
toOilExpr T.Ite {..} = do
  (_, condLabel) <- lookupTy cond
  left' <- toOilExpr left
  right' <- toOilExpr right
  let cond' = toOilVar cond
  case condLabel of
    SafeL -> return $ ite_ cond' left' right'
    LeakyL -> do
      lIf <- lIfInst $ fromJust retTy
      -- Recall that the first branch of Boolean case analysis corresponds to
      -- @False@ while the second one to @True@, unlike the if-then-else
      -- construct.
      return $ GV (lCaseName "bool") @@ [lIf, cond', right', left']
toOilExpr T.Case {..} = do
  (adtName, paraTypess, condLabel) <- lookupADT cond
  alts' <- zipWithM (go condLabel) (toList alts) paraTypess
  let cond' = toOilVar cond
  case condLabel of
    SafeL -> return $ caseB cond' alts'
    LeakyL -> do
      lIf <- lIfInst $ fromJust retTy
      return $
        GV (lCaseName adtName)
          @@ ( [lIf, cond']
                 <> [lamsB xs body | (_, xs, body) <- alts']
             )
  where
    go condLabel CaseAlt {..} paraTypes = do
      (xs, body) <- unbindMany (length paraTypes) bnd
      let ctx = zipWith (\x t -> (x, t, condLabel)) xs paraTypes
      body' <- extendCtx ctx $ toOilExpr body
      return (ctor, zip xs binders, body')
toOilExpr T.OIte {..} = do
  -- The right branch should have the same type.
  (ty, _) <- lookupTy left
  lIf <- lIfInstMayCrust ty
  return $ lIf @@ (toOilVar <$> [cond, left, right])
toOilExpr T.Pair {..} = do
  ref <- toMayLeakyGV "(,)"
  return $ ref @@ (toOilVar <$> [left, right])
toOilExpr T.PCase {..} = do
  (condTy, condLabel) <- lookupTy cond
  let (leftTy, rightTy) =
        case condTy of
          T.Prod {..} -> (left, right)
          _ -> oops "Not a product"
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCtx
      [ (xl, leftTy, condLabel),
        (xr, rightTy, condLabel)
      ]
      $ toOilExpr body
  let cond' = toOilVar cond
  case condLabel of
    SafeL ->
      return $
        caseB
          cond'
          [("(,)", [(xl, lBinder), (xr, rBinder)], body')]
    LeakyL -> do
      lProm <- promInst leftTy
      rProm <- promInst rightTy
      lIf <- lIfInst $ fromJust retTy
      return $
        GV (lCaseName "*")
          @@ [ lProm,
               rProm,
               lIf,
               cond',
               lamsB [(xl, lBinder), (xr, rBinder)] body'
             ]
toOilExpr T.OPair {..} =
  return $ GV aConcat @@ (toOilVar <$> [left, right])
toOilExpr T.OPCase {..} = do
  let (leftTy, rightTy) =
        case fromJust oprodTy of
          T.OProd {..} -> (left, right)
          _ -> oops "Not an oblivious product"
  leftSize <- toOilSize leftTy
  rightSize <- toOilSize rightTy
  ((xl, xr), body) <- unbind2 bnd2
  body' <-
    extendCtx
      [ (xl, leftTy, SafeL),
        (xr, rightTy, SafeL)
      ]
      $ toOilExpr body
  let cond' = toOilVar cond
  return $
    letsB
      [ (xl, lBinder, GV aSlice @@ [cond', ILit 0, leftSize]),
        (xr, rBinder, GV aSlice @@ [cond', leftSize, rightSize])
      ]
      body'
toOilExpr T.OInj {..} = do
  let (leftTy, rightTy) =
        case fromJust mTy of
          T.OSum {..} -> (left, right)
          _ -> oops "Not an oblivious sum"
  leftSize <- toOilSize leftTy
  rightSize <- toOilSize rightTy
  let inj' = toOilVar inj
  return $
    GV (oblivName $ if tag then "inl" else "inr")
      @@ [leftSize, rightSize, inj']
toOilExpr T.OCase {..} = do
  let (leftTy, rightTy) =
        case fromJust osumTy of
          T.OSum {..} -> (left, right)
          _ -> oops "Not an oblivious sum"
  lSize <- toOilSize leftTy
  rSize <- toOilSize rightTy
  tagSize <- toOilSize T.OBool
  (xl, lBody) <- unbind1 lBnd
  (xr, rBody) <- unbind1 rBnd
  lBody' <- extendCtx1 xl leftTy SafeL $ toOilExpr lBody
  rBody' <- extendCtx1 xr rightTy SafeL $ toOilExpr rBody
  let cond' = toOilVar cond
  lIf <- lIfInstMayCrust (fromJust retTy)
  -- The tag is at the end of the payload.
  return $
    lIf
      @@ [ GV aSlice
             @@ [ cond',
                  GV (internalName "max") @@ [lSize, rSize],
                  tagSize
                ],
           letsB
             [(xl, lBinder, GV aSlice @@ [cond', ILit 0, lSize])]
             lBody',
           letsB
             [(xr, rBinder, GV aSlice @@ [cond', ILit 0, rSize])]
             rBody'
         ]
toOilExpr T.Mux {..} = do
  return $ GV aMux @@ (toOilVar <$> [cond, left, right])
toOilExpr T.Promote {..} =
  getIsCrust >>= \b ->
    if b
      then return $ toOilVar expr
      else do
        (ty, _) <- lookupTy expr
        prom <- promInst ty
        return $ prom @@ [toOilVar expr]
toOilExpr T.Tape {..} =
  getIsCrust >>= \b ->
    if b
      then return $ toOilVar expr
      else return $ GV (leakyName "tape") @@ [toOilVar expr]
toOilExpr _ = oops "Not a term in core taype ANF"

-- | Translate a taype oblivious type to the OIL expression representing its
-- size.
--
-- The taype type is obliviously kinded and in core taype ANF.
--
-- The resulting OIL expression should be typed by 'sizeTy' under the translated
-- typing context, according to 'toOilTy'.
--
-- For a taype term typed by the given oblivious taype type, its translated OIL
-- term (according to 'toOilExpr') is an oblivious array of the size indicated
-- by the resulting OIL expression. In particular, if this taype term is closed,
-- the computed OIL expression is exactly the integer for the size of the
-- computed array.
toOilSize :: T.Ty Name -> TslM (Expr Name)
toOilSize T.TUnit = return $ ILit 0
-- Oblivious boolean is the same as oblivious integer in OIL.
toOilSize T.OBool = return $ ILit 1
toOilSize T.OInt = return $ ILit 1
toOilSize T.OProd {..} = do
  lSize <- toOilSize left
  rSize <- toOilSize right
  return $ GV "+" @@ [lSize, rSize]
toOilSize T.OSum {..} = do
  lSize <- toOilSize left
  rSize <- toOilSize right
  return $ GV "+" @@ [ILit 1, GV (internalName "max") @@ [lSize, rSize]]
toOilSize T.App {appKind = Just TypeApp, fn = T.GV {..}, ..} =
  return $ GV ref @@ toOilVar <$> args
toOilSize T.Let {..} = do
  rhs' <- withLabel SafeL $ toOilExpr rhs
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x (fromJust mTy) SafeL $ toOilSize body
  return $ letB x binder rhs' body'
toOilSize T.Ite {..} = do
  left' <- toOilSize left
  right' <- toOilSize right
  return $ ite_ (toOilVar cond) left' right'
toOilSize T.Case {..} = do
  (_, paraTypess, _) <- lookupADT cond
  alts' <- zipWithM go (toList alts) paraTypess
  return $ caseB (toOilVar cond) alts'
  where
    go CaseAlt {..} paraTypes = do
      (xs, body) <- unbindMany (length paraTypes) bnd
      let ctx = zipWith (\x t -> (x, t, SafeL)) xs paraTypes
      body' <- extendCtx ctx $ toOilSize body
      return (ctor, zip xs binders, body')
toOilSize _ = oops "Not an oblivious type"

-- | Translate a taype variable, either local or global, to the corresponding
-- OIL variable.
--
-- The given taype expression has to be a local or global variable.
toOilVar :: T.Expr Name -> Expr Name
toOilVar T.V {..} = V {..}
toOilVar T.GV {..} = GV {..}
toOilVar _ = oops "Not a variable"

-- | Translate a taype type with its label to the corresponding OIL type.
--
-- The taype type is well-kinded and in core taype ANF.
toOilTy :: T.Ty Name -> TslM (Ty b)
toOilTy t =
  getLabel >>= \case
    SafeL -> toOilTy_ t
    LeakyL -> toLeakyTy <$> toOilTy_ t

-- | Translate a taype type to the corresponding plain OIL type.
--
-- The taype type is well-kinded and in core taype ANF. The resulting OIL type
-- itself is not leaky, but function types may have leaky arguments.
--
-- If the taype type is obliviously kinded, then the result should be oblivious
-- array.
--
-- Two equivalent taype type should be translated to the same OIL type.
toOilTy_ :: T.Ty Name -> TslM (Ty b)
toOilTy_ T.TBool = return $ tGV "bool"
toOilTy_ T.TInt = return TInt
toOilTy_ T.GV {..} = return $ tGV ref
toOilTy_ T.Prod {..} = ("*" @@) <$> mapM toOilTy_ [left, right]
toOilTy_ T.Pi {..} = do
  dom <- withLabel (fromJust label) $ toOilTy ty
  (_, body) <- unbind1 bnd
  cod <- toOilTy_ body
  return Arrow {..}
-- Oblivious types, including type level computation, are translated into
-- oblivious array.
toOilTy_ _ = return OArray

-- | Translate an OIL type to its leaky counterpart.
--
-- Builtin types are translated to the leaky types in the 'prelude'.
-- User-defined ADTs are translated to the corresponding leaky types according
-- to our naming convention, i.e. the ADT names with the 'leakyAccent' prefix.
-- The actual definitions of the ADT leaky counterparts are generated when
-- translating ADT definitions.
toLeakyTy :: Ty a -> Ty a
toLeakyTy TInt = tGV $ leakyName "int"
toLeakyTy OArray = tGV $ leakyName aName
toLeakyTy Arrow {..} = Arrow {cod = toLeakyTy cod, ..}
toLeakyTy TApp {..} =
  TApp {tctor = leakyName tctor, args = (toLeakyTy <$> args) <> args}
-- Local type variables do not appear in type translation.
toLeakyTy _ = oops "Local type variables appear"

----------------------------------------------------------------
-- Leaky structure instance resolution

-- | Resolve the return instance of the leaky structure of an OIL type.
--
-- Given OIL type @T@, the return expression should have type:
--
-- @T -> <|T|>@
--
-- where @<|-|>@ is 'toLeakyTy'.
--
-- The given OIL type is nonleaky. In addition, it is a concrete type, i.e. not
-- a type variable.
promInst_ :: Ty a -> Expr b
promInst_ TInt = GV (promName "int")
promInst_ OArray = GV (promName aName)
promInst_ Arrow {..} = GV (promName "->") @@ [promInst_ cod]
promInst_ TApp {..} = GV (promName tctor)
promInst_ _ = oops "Cannot resolve return instance of type variable"

-- | Resolve the return instance of the leaky structure of a taype type.
promInst :: T.Ty Name -> TslM (Expr b)
promInst = (promInst_ <$>) . toOilTy_

-- | Resolve the leaky if instance of the leaky structure of an OIL type.
--
-- Given OIL type @T@, the return expression should have type:
--
-- @'OArray' -> <|T|> -> <|T|> -> <|T|>@
--
-- where @<|-|>@ is 'toLeakyTy'.
--
-- The given OIL type is a concrete type, i.e. not a type variable.
lIfInst_ :: Ty a -> Expr b
lIfInst_ TInt = GV (lIfName "int")
lIfInst_ OArray = GV (lIfName aName)
lIfInst_ Arrow {..} = GV (lIfName "->") @@ [lIfInst_ cod]
lIfInst_ TApp {..} = GV (lIfName tctor)
lIfInst_ _ = oops "Cannot resolve leaky if instance of type variable"

-- | Resolve the leaky if instance of the leaky structure of a taype type.
lIfInst :: T.Ty Name -> TslM (Expr b)
lIfInst = (lIfInst_ <$>) . toOilTy_

lIfInstMayCrust :: T.Ty Name -> TslM (Expr b)
lIfInstMayCrust t =
  getIsCrust >>= \b ->
    if b
      then return $ GV $ unsafeName "if"
      else lIfInst t

----------------------------------------------------------------
-- Translating definitions

-- | Translate taype definitions to the corresponding OIL definitions.
--
-- The result contains four sets of definitions: the prelude, the actual OIL
-- definitions, the section functions with their dependencies for the conceal
-- phase, and the retraction functions with their dependencies for the reveal
-- phase.
toOilProgram :: Options -> GCtx Name -> T.Defs Name -> Program b a
toOilProgram Options {..} gctx defs =
  Program
    { mainDefs =
        secondF closedDef $
          foldMap (simp optReadableOil . go False) defs,
      ..
    }
  where
    go isCrust =
      runTslM Env {tctx = TCtx [], label = SafeL, ..}
        . toOilDef
    simp readable =
      secondF $
        (if readable then readableDef else id) . simpDef
    funDefs = [def | def@(_, T.FunDef {}) <- defs]
    concealSet = filterCrust funDefs T.SectionAttr
    revealSet = filterCrust funDefs T.RetractionAttr
    crustDefs readable crustSet rename names =
      secondF closedDef $
        bimapF rename (renameCrustDef (crustSet <> fromList names) rename) $
          foldMap
            (simp readable . go True)
            [def | def@(name, _) <- funDefs, name `member` crustSet]
    -- In the conceal phase, we keep the ANF form because the evaluation order
    -- is crucial.
    concealDefs =
      crustDefs
        False
        concealSet
        privName
        [ sectionName "int",
          sectionName "bool",
          oblivName "inl",
          oblivName "inr",
          aNew
        ]
    revealDefs =
      crustDefs
        optReadableOil
        revealSet
        unsafeName
        [ retractionName "int",
          retractionName "bool"
        ]

-- | Translate a taype definition to the corresponding OIL definition.
--
-- The ADT definition is translated to multiple OIL definitions, so this
-- function returns a list of OIL definitions.
toOilDef :: T.NamedDef Name -> TslM [NamedDef Name Name]
toOilDef (name, def) = case def of
  T.FunDef {..} -> withLabel (fromJust label) $ do
    ty' <- toOilTy ty
    expr' <- toOilExpr expr
    return $
      one
        ( name,
          FunDef
            { binders = [],
              tyBnd = abstract_ [] ty',
              expr = expr'
            }
        )
  T.OADTDef {..} -> do
    (x, body) <- unbind1 bnd
    body' <- extendCtx1 x ty SafeL $ toOilSize body
    ty' <- withLabel SafeL $ toOilTy ty
    return $
      one
        ( name,
          FunDef
            { binders = [],
              tyBnd = abstract_ [] $ Arrow ty' sizeTy,
              expr = lamB x binder body'
            }
        )
  T.ADTDef {..} -> do
    let (ctorNames, paraTypess) = unzip $ toList ctors
    sParaTypess <- withLabel SafeL $ mapM (mapM toOilTy) paraTypess
    lParaTypess <- withLabel LeakyL $ mapM (mapM toOilTy) paraTypess
    return
      [ -- ADT
        adtDef_ name [] $ zip ctorNames sParaTypess,
        -- Leaky ADT
        adtDef_ (l_ name) [] $
          zipWith ((,) . l_) ctorNames lParaTypess
            <> [ (prom_ name, [TV name]),
                 (lif_ name, [OArray, "$self", "$self"])
               ],
        -- Leaky case analysis
        funDef_
          (lcase_ name)
          [l_ "r"]
          ( ar_ $
              [ar_ [OArray, l_ "r", l_ "r", l_ "r"], l_ name]
                <> [ar_ $ ts <> [l_ "r"] | ts <- lParaTypess]
                `snoc` l_ "r"
          )
          $ lCaseBody ctorNames sParaTypess
      ]
  _ -> oops "Translating constructor or builtin definitions"
  where
    vars prefix n = (prefix <>) . show <$> [1 .. n]
    lCaseBody ctors tss =
      let fs = vars (l_ "f") $ length tss
       in lams_ ([lif_ "r", l_ "x"] <> (toBinder <$> fs)) $
            case_ (l_ "x") $
              zipWith3 lCaseAlt ctors fs tss
                <> [ ( prom_ name,
                       ["x"],
                       case_ "x" $ zipWith3 promAlt ctors fs tss
                     ),
                     ( lif_ name,
                       [o_ "b", l_ "x1", l_ "x2"],
                       lif_ "r"
                         @@ [ o_ "b",
                              "$self" @@ [lif_ "r", l_ "x1"] <> (V <$> fs),
                              "$self" @@ [lif_ "r", l_ "x2"] <> (V <$> fs)
                            ]
                     )
                   ]
    lCaseAlt ctor f ts =
      let xs = vars (l_ "x") $ length ts
       in (l_ ctor, toBinder <$> xs, V f @@ V <$> xs)
    promAlt ctor f ts =
      let xs = vars "x" $ length ts
       in ( ctor,
            toBinder <$> xs,
            V f @@ zipWith (\t x -> promInst_ t @@ [V x]) ts xs
          )

----------------------------------------------------------------
-- Simplification of OIL expressions

-- | Simplify OIL expressions.
--
-- This function performs various simplifcation such as let flattening and
-- application collapsing.
simpDef :: Def Name Name -> Def Name Name
simpDef = runFreshM . transformBiM go
  where
    go App {args = [], ..} = return fn
    go App {fn = App {..}, args = args'} =
      return $ fn @@ args <> args'
    go e@Let {..} = case rhs of
      V {..} -> return $ instantiateName name bnd
      GV {..} -> return $ instantiate_ GV {..} bnd
      Let {binder = binderN, rhs = rhsN, bnd = bndN} -> do
        (x, bodyN) <- unbind1 bndN
        body' <- go Let {rhs = bodyN, ..}
        return $ letB x binderN rhsN body'
      _ -> return e
    go e = return e

-- | Make the generated OIL programs more readable.
--
-- This function subsitutes all let bindings that do not have a named binder.
readableDef :: Def Name Name -> Def Name Name
readableDef = runFreshM . transformBiM go
  where
    go :: Expr Name -> FreshM (Expr Name)
    go Let {binder = Nothing, ..} = return $ instantiate_ rhs bnd
    go e = return e

----------------------------------------------------------------
-- Helper functions

toMayLeakyGV :: Text -> TslM (Expr a)
toMayLeakyGV x = go <$> getLabel
  where
    go SafeL = GV x
    go LeakyL = GV $ leakyName x

filterCrust :: T.Defs Name -> T.Attribute -> HashSet Text
filterCrust defs a = crustSet
  where
    (graph, fromVertex, toVertex) = graphFromEdges $ mkDepGraph defs
    crustDefs = [name | (name, T.FunDef {..}) <- defs, attr == a]
    crustSet1 name =
      fromList $ maybe [] (toNames . reachable graph) $ toVertex name
    toNames vs = [name | (_, name, _) <- fromVertex <$> vs]
    crustSet = fromList crustDefs <> foldMap crustSet1 crustDefs

mkDepGraph :: T.Defs Name -> [(T.NamedDef Name, Text, [Text])]
mkDepGraph defs =
  let deps = runFreshM $ mapM (go . snd) defs
   in zipWith (\def dep -> (def, fst def, dep)) defs deps
  where
    go T.FunDef {..} = do
      deps <- universeM expr
      return $ hashNub [x | T.GV x <- deps]
    go _ = return []

renameCrustDef ::
  HashSet Text -> (Text -> Text) -> Def Name Name -> Def Name Name
renameCrustDef renameSet rename = runFreshM . transformBiM go
  where
    go :: Expr Name -> FreshM (Expr Name)
    go GV {..}
      | ref `member` renameSet =
          return $ GV {ref = rename ref}
    go e = return e

----------------------------------------------------------------
-- Prelude

-- | The prelude with builtin types and functions
--
-- Because we do not type check these definitions, we need to be careful and
-- make sure all definitions are well-typed and in the right form. Specifically,
-- the alternatives in case analysis are in the canonical order.
prelude :: Defs b a
prelude =
  [ -- Array
    adtDef_
      (l_ aName)
      []
      [ (prom_ aName, [OArray]),
        (lif_ aName, [OArray, "$self", "$self"])
      ],
    -- Boolean
    --
    -- It is defined similarly to that in Haskell: the first constructor is
    -- @False@ and the second one is @True@.
    adtDef_
      "bool"
      []
      [("False", []), ("True", [])],
    adtDef_
      (l_ "bool")
      []
      [ (r_ "bool", [OArray]),
        (prom_ "bool", ["bool"]),
        (lif_ "bool", [OArray, "$self", "$self"])
      ],
    -- Section of boolean
    --
    -- We need one for core computation and one for conceal phase.
    sBoolDef True,
    sBoolDef False,
    -- The first branch of Boolean case analysis corresponds to @False@ while
    -- the second one to @True@.
    funDef_
      (lcase_ "bool")
      [l_ "r"]
      ( ar_
          [ ar_ [OArray, l_ "r", l_ "r", l_ "r"],
            l_ "bool",
            l_ "r",
            l_ "r",
            l_ "r"
          ]
      )
      $ lams_
        [lif_ "r", l_ "b", l_ "ff", l_ "ft"]
        ( case_
            (l_ "b")
            [ (r_ "bool", [o_ "b"], lif_ "r" @@ [o_ "b", l_ "ft", l_ "ff"]),
              (prom_ "bool", ["b"], ite_ "b" (l_ "ft") (l_ "ff")),
              ( lif_ "bool",
                [o_ "b", l_ "b1", l_ "b2"],
                lif_ "r"
                  @@ [ o_ "b",
                       "$self" @@ [lif_ "r", l_ "b1", l_ "ff", l_ "ft"],
                       "$self" @@ [lif_ "r", l_ "b2", l_ "ff", l_ "ft"]
                     ]
              )
            ]
        ),
    funDef_
      (l_ $ s_ "bool")
      []
      (ar_ [l_ "bool", l_ aName])
      $ lam_
        (l_ "b")
        ( case_
            (l_ "b")
            [ (r_ "bool", [o_ "b"], prom_ aName @@ [o_ "b"]),
              ( prom_ "bool",
                ["b"],
                prom_ aName @@ [s_ "bool" @@ ["b"]]
              ),
              ( lif_ "bool",
                [o_ "b", l_ "b1", l_ "b2"],
                lif_ aName
                  @@ [o_ "b", "$self" @@ [l_ "b1"], "$self" @@ [l_ "b2"]]
              )
            ]
        ),
    -- Integer
    adtDef_
      (l_ "int")
      []
      [ (r_ "int", [OArray]),
        (prom_ "int", [TInt]),
        (lif_ "int", [OArray, "$self", "$self"])
      ],
    funDef_
      (l_ $ s_ "int")
      []
      (ar_ [l_ "int", l_ aName])
      $ lam_
        (l_ "n")
        ( case_
            (l_ "n")
            [ (r_ "int", [o_ "n"], prom_ aName @@ [o_ "n"]),
              (prom_ "int", ["n"], prom_ aName @@ [s_ "int" @@ ["n"]]),
              ( lif_ "int",
                [o_ "b", l_ "n1", l_ "n2"],
                lif_ aName
                  @@ [o_ "b", "$self" @@ [l_ "n1"], "$self" @@ [l_ "n2"]]
              )
            ]
        ),
    lIntBopDef "+" "int",
    lIntBopDef "-" "int",
    lIntBopDef "*" "int",
    -- Because of the tape semantics, it is possible to divide a number by 0 in
    -- the "wrong" branches. We check the denominator and return -1 if it is 0.
    lIntBopDef_ "/" "int" $
      \m n -> ite_ ("==" @@ [n, ILit 0]) (ILit (-1)) $ "/" @@ [m, n],
    lIntBopDef "<=" "bool",
    lIntBopDef "==" "bool",
    lBoolUopDef "not",
    lBoolBopDef "&&" False,
    lBoolBopDef "||" True,
    -- Helper functions
    funDef_
      (i_ "max")
      []
      (ar_ [TInt, TInt, TInt])
      $ lams_
        ["m", "n"]
        (ite_ ("<=" @@ ["m", "n"]) "n" "m"),
    -- Product
    adtDef_
      "*"
      ["a", "b"]
      [("(,)", ["a", "b"])],
    adtDef_
      (l_ "*")
      [l_ "a", l_ "b", "a", "b"]
      [ (l_ "(,)", [l_ "a", l_ "b"]),
        (prom_ "*", ["*" @@ ["a", "b"]]),
        ( lif_ "*",
          [ OArray,
            l_ "*" @@ [l_ "a", l_ "b", "a", "b"],
            l_ "*" @@ [l_ "a", l_ "b", "a", "b"]
          ]
        )
      ],
    funDef_
      (lcase_ "*")
      ["a", l_ "a", "b", l_ "b", l_ "r"]
      ( ar_
          [ ar_ ["a", l_ "a"],
            ar_ ["b", l_ "b"],
            ar_ [OArray, l_ "r", l_ "r", l_ "r"],
            l_ "*" @@ [l_ "a", l_ "b", "a", "b"],
            ar_ [l_ "a", l_ "b", l_ "r"],
            l_ "r"
          ]
      )
      $ lams_
        [prom_ "a", prom_ "b", lif_ "r", l_ "p", l_ "f"]
        ( case_
            (l_ "p")
            [ (l_ "(,)", [l_ "x", l_ "y"], l_ "f" @@ [l_ "x", l_ "y"]),
              ( prom_ "*",
                ["p"],
                case_
                  "p"
                  [ ( "(,)",
                      ["x", "y"],
                      l_ "f" @@ [prom_ "a" @@ ["x"], prom_ "b" @@ ["y"]]
                    )
                  ]
              ),
              ( lif_ "*",
                [o_ "b", l_ "p1", l_ "p2"],
                lif_ "r"
                  @@ [ o_ "b",
                       "$self"
                         @@ [prom_ "a", prom_ "b", lif_ "r", l_ "p1", l_ "f"],
                       "$self"
                         @@ [prom_ "a", prom_ "b", lif_ "r", l_ "p2", l_ "f"]
                     ]
              )
            ]
        ),
    -- Instances of function type
    funDef_
      (prom_ "->")
      ["a", "b", l_ "b"]
      (ar_ [ar_ ["b", l_ "b"], ar_ ["a", "b"], "a", l_ "b"])
      $ lams_
        [prom_ "b", "f", "x"]
        (prom_ "b" @@ ["f" @@ ["x"]]),
    funDef_
      (lif_ "->")
      ["a", l_ "b"]
      ( ar_
          [ ar_ [OArray, l_ "b", l_ "b", l_ "b"],
            OArray,
            ar_ ["a", l_ "b"],
            ar_ ["a", l_ "b"],
            "a",
            l_ "b"
          ]
      )
      $ lams_
        [lif_ "b", o_ "b", "f1", "f2", "x"]
        (lif_ "b" @@ [o_ "b", "f1" @@ ["x"], "f2" @@ ["x"]]),
    -- Tape
    funDef_
      (l_ "tape")
      []
      (ar_ [l_ aName, OArray])
      $ lams_
        [l_ "a"]
        ( case_
            (l_ "a")
            [ (prom_ aName, [o_ "a"], o_ "a"),
              ( lif_ aName,
                [o_ "b", l_ "a1", l_ "a2"],
                V aMux
                  @@ [ o_ "b",
                       "$self" @@ [l_ "a1"],
                       "$self" @@ [l_ "a2"]
                     ]
              )
            ]
        ),
    -- Oblivious injection
    --
    -- We need one for core computation and one for conceal phase.
    oblivInjDef True True,
    oblivInjDef False True,
    oblivInjDef True False,
    oblivInjDef False False
  ]

lBoolUopDef :: Text -> NamedDef b a
lBoolUopDef name =
  funDef_
    (l_ name)
    []
    (ar_ [l_ "bool", l_ "bool"])
    $ lam_
      (l_ "x")
      ( case_
          (l_ "x")
          [ (r_ "bool", [o_ "x"], r_ "bool" @@ [o_ name @@ [o_ "x"]]),
            (prom_ "bool", ["x"], prom_ "bool" @@ [V name @@ ["x"]]),
            ( lif_ "bool",
              [o_ "b", l_ "x1", l_ "x2"],
              lif_ "bool"
                @@ [ o_ "b",
                     "$self" @@ [l_ "x1"],
                     "$self" @@ [l_ "x2"]
                   ]
            )
          ]
      )

-- | Build a leaky definition for binary boolean operator, e.g., '&&'.
lBoolBopDef :: Text -> Bool -> NamedDef b a
lBoolBopDef name domi =
  funDef_
    (l_ name)
    []
    (ar_ [l_ "bool", l_ "bool", l_ "bool"])
    $ lams_
      [l_ "x", l_ "y"]
      ( case_
          (l_ "x")
          [ ( r_ "bool",
              [o_ "x"],
              case_
                (l_ "y")
                [ ( r_ "bool",
                    [o_ "y"],
                    r_ "bool" @@ [o_ name @@ [o_ "x", o_ "y"]]
                  ),
                  ( prom_ "bool",
                    ["y"],
                    ite_
                      "y"
                      (if domi then l_ "y" else l_ "x")
                      (if domi then l_ "x" else l_ "y")
                  ),
                  ( lif_ "bool",
                    [o_ "b", l_ "y1", l_ "y2"],
                    lif_ "bool"
                      @@ [ o_ "b",
                           "$self" @@ [l_ "x", l_ "y1"],
                           "$self" @@ [l_ "x", l_ "y2"]
                         ]
                  )
                ]
            ),
            ( prom_ "bool",
              ["x"],
              ite_
                "x"
                (if domi then l_ "x" else l_ "y")
                (if domi then l_ "y" else l_ "x")
            ),
            ( lif_ "bool",
              [o_ "b", l_ "x1", l_ "x2"],
              case_
                (l_ "y")
                [ ( r_ "bool",
                    [Anon],
                    lif_ "bool"
                      @@ [ o_ "b",
                           "$self" @@ [l_ "x1", l_ "y"],
                           "$self" @@ [l_ "x2", l_ "y"]
                         ]
                  ),
                  ( prom_ "bool",
                    ["y"],
                    ite_
                      "y"
                      (if domi then l_ "y" else l_ "x")
                      (if domi then l_ "x" else l_ "y")
                  ),
                  ( lif_ "bool",
                    [Anon, Anon, Anon],
                    lif_ "bool"
                      @@ [ o_ "b",
                           "$self" @@ [l_ "x1", l_ "y"],
                           "$self" @@ [l_ "x2", l_ "y"]
                         ]
                  )
                ]
            )
          ]
      )

-- | Build a leaky definition for binary integer operator, e.g., '+'.
lIntBopDef_ ::
  Text -> Text -> (Expr Text -> Expr Text -> Expr Text) -> NamedDef b a
lIntBopDef_ name cod mkExpr =
  funDef_
    (l_ name)
    []
    (ar_ [l_ "int", l_ "int", l_ cod])
    $ lams_
      [l_ "m", l_ "n"]
      ( case_
          (l_ "m")
          [ ( r_ "int",
              [o_ "m"],
              case_
                (l_ "n")
                [ ( r_ "int",
                    [o_ "n"],
                    r_ cod
                      @@ [o_ name @@ [o_ "m", o_ "n"]]
                  ),
                  ( prom_ "int",
                    ["n"],
                    r_ cod
                      @@ [o_ name @@ [o_ "m", s_ "int" @@ ["n"]]]
                  ),
                  ( lif_ "int",
                    [o_ "b", l_ "n1", l_ "n2"],
                    lif_ cod
                      @@ [ o_ "b",
                           "$self" @@ [l_ "m", l_ "n1"],
                           "$self" @@ [l_ "m", l_ "n2"]
                         ]
                  )
                ]
            ),
            ( prom_ "int",
              ["m"],
              case_
                (l_ "n")
                [ ( r_ "int",
                    [o_ "n"],
                    r_ cod
                      @@ [o_ name @@ [s_ "int" @@ ["m"], o_ "n"]]
                  ),
                  ( prom_ "int",
                    ["n"],
                    prom_ cod
                      @@ [mkExpr "m" "n"]
                  ),
                  ( lif_ "int",
                    [o_ "b", l_ "n1", l_ "n2"],
                    lif_ cod
                      @@ [ o_ "b",
                           "$self" @@ [l_ "m", l_ "n1"],
                           "$self" @@ [l_ "m", l_ "n2"]
                         ]
                  )
                ]
            ),
            ( lif_ "int",
              [o_ "b", l_ "m1", l_ "m2"],
              lif_ cod
                @@ [ o_ "b",
                     "$self" @@ [l_ "m1", l_ "n"],
                     "$self" @@ [l_ "m2", l_ "n"]
                   ]
            )
          ]
      )

lIntBopDef :: Text -> Text -> NamedDef b a
lIntBopDef name cod = lIntBopDef_ name cod $ \m n -> V name @@ [m, n]

-- | Build a boolean section function.
--
-- The first argument is 'True' if this section is used in the core computation
-- phase, or it is used in the conceal phase.
sBoolDef :: Bool -> NamedDef b a
sBoolDef isCompPhase =
  funDef_
    (prefix <> s_ "bool")
    []
    (ar_ ["bool", OArray])
    $ lam_
      "b"
      ( ite_
          "b"
          (GV (prefix <> s_ "int") @@ [ILit 1])
          (GV (prefix <> s_ "int") @@ [ILit 0])
      )
  where
    prefix = if isCompPhase then "" else privPrefix

-- | Build an oblivious injection.
--
-- The first argument indicates whether it is left or right injection. The
-- second argument is 'True' if it is used in the core computation phase,
-- otherwise in the conceal phase.
oblivInjDef :: Bool -> Bool -> NamedDef b a
oblivInjDef tag isCompPhase =
  funDef_
    name
    []
    (ar_ [sizeTy, sizeTy, OArray, OArray])
    $ lams_
      (if tag then ["m", "n", o_ "a"] else ["n", "m", o_ "a"])
      ( lets_
          [ ( "data",
              ite_
                ("<=" @@ ["n", "m"])
                (o_ "a")
                ( V aConcat
                    @@ [o_ "a", aNew' @@ ["-" @@ ["n", "m"]]]
                )
            ),
            ("tag", sBool @@ [if tag then "True" else "False"])
          ]
          $ V aConcat @@ ["data", "tag"]
      )
  where
    rawName = if tag then "inl" else "inr"
    name =
      if isCompPhase
        then oblivName rawName
        else privPrefix <> oblivName rawName
    sBool =
      GV $ if isCompPhase then s_ "bool" else privName $ sectionName "bool"
    aNew' = GV $ if isCompPhase then aNew else privName aNew

----------------------------------------------------------------
-- Smart constructors

l_ :: IsString a => Text -> a
l_ = fromString . toString . leakyName

o_ :: IsString a => Text -> a
o_ = fromString . toString . oblivName

s_ :: IsString a => Text -> a
s_ = fromString . toString . sectionName

r_ :: IsString a => Text -> a
r_ = fromString . toString . leakyName . retractionName

i_ :: IsString a => Text -> a
i_ = fromString . toString . internalName

lif_ :: IsString a => Text -> a
lif_ = fromString . toString . lIfName

prom_ :: IsString a => Text -> a
prom_ = fromString . toString . promName

lcase_ :: IsString a => Text -> a
lcase_ = fromString . toString . lCaseName

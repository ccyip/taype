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
-- return and leaky if instances. This is more convenient than maintaining a
-- lookup table. The generated names contain characters that are illegal in the
-- taype identifiers to avoid name conflicts.
module Oil.Translation
  ( prelude,
    toOilDefs,
  )
where

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

retName :: Text -> Text
retName x = leakyName "ret#" <> x

lIfName :: Text -> Text
lIfName x = leakyName "if#" <> x

lCaseName :: Text -> Text
lCaseName x = leakyName "case#" <> x

----------------------------------------------------------------
-- Environment for translation

data Env = Env
  { -- Taype global context
    gctx :: GCtx Name,
    -- Taype typing context
    tctx :: TCtx Name
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
lookupTy :: MonadReader Env m => T.Expr Name -> m (T.Ty Name, Label)
lookupTy T.V {..} = lookupLCtx name
lookupTy T.GV {..} =
  lookupGDef ref >>= \case
    T.FunDef {..} -> return (ty, fromJust label)
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
toOilExpr :: Label -> T.Expr Name -> TslM (Expr Name)
toOilExpr _ T.V {..} = return V {..}
toOilExpr _ T.GV {..} = return GV {..}
-- Unit value is an empty oblivious array.
toOilExpr _ T.VUnit = return $ GV aNew @@ [ILit 0]
toOilExpr _ T.BLit {..} = return $ if bLit then GV "True" else GV "False"
toOilExpr _ T.ILit {..} = return ILit {..}
toOilExpr l T.Lam {..} = do
  let binderLabel = fromJust label
      binderTy = fromJust mTy
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x binderTy binderLabel $ toOilExpr l body
  let e = lam' x binder body'
  return $ case l of
    SafeL -> e
    LeakyL -> GV (leakyName "lam") @@ [e]
toOilExpr l T.App {fn = T.GV {..}, ..}
  | appKind == Just BuiltinApp || appKind == Just CtorApp =
      return $ mayLeakyGV l ref @@ toOilVar <$> args
toOilExpr SafeL T.App {appKind = Just FunApp, ..} =
  return $ toOilVar fn @@ toOilVar <$> args
toOilExpr LeakyL T.App {appKind = Just FunApp, ..} = do
  (ty, _) <- lookupTy fn
  go ty args $ toOilVar fn
  where
    go T.Pi {..} (arg : args') fn' = do
      (_, body) <- unbind1 bnd
      go body args' $
        GV (leakyName "ap")
          @@ [lIfInst body, fn', toOilVar arg]
    go _ [] fn' = return fn'
    go _ _ _ = oops "The arguments do not match the taype function type"
toOilExpr l T.Let {..} = do
  let rhsLabel = fromJust label
      ty = fromJust mTy
  rhs' <- toOilExpr rhsLabel rhs
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x ty rhsLabel $ toOilExpr l body
  return $ let' x binder rhs' body'
toOilExpr l T.Ite {..} = do
  (_, condLabel) <- lookupTy cond
  left' <- toOilExpr l left
  right' <- toOilExpr l right
  let cond' = toOilVar cond
  return $
    case condLabel of
      SafeL -> ite_ cond' left' right'
      LeakyL ->
        -- Recall that the first branch of Boolean case analysis corresponds to
        -- @False@ while the second one to @True@, unlike the if-then-else
        -- construct.
        GV (lCaseName "bool")
          @@ [ lIfInst $ fromJust mTy,
               cond',
               right',
               left'
             ]
toOilExpr l T.Case {..} = do
  (adtName, paraTypess, condLabel) <- lookupADT cond
  alts' <- zipWithM (go condLabel) (toList alts) paraTypess
  let cond' = toOilVar cond
  return $
    case condLabel of
      SafeL -> case' cond' alts'
      LeakyL ->
        GV (lCaseName adtName)
          @@ ( [ lIfInst $ fromJust mTy,
                 cond'
               ]
                 <> (alts' <&> \(_, xs, body) -> lams' xs body)
             )
  where
    go condLabel CaseAlt {..} paraTypes = do
      (xs, body) <- unbindMany (length paraTypes) bnd
      let ctx = zipWith (\x t -> (x, t, condLabel)) xs paraTypes
      body' <- extendCtx ctx $ toOilExpr l body
      return (ctor, zip xs binders, body')
toOilExpr _ T.OIte {..} = do
  -- The right branch should have the same type.
  (ty, _) <- lookupTy left
  return $ lIfInst ty @@ (toOilVar <$> [cond, left, right])
toOilExpr l T.Pair {..} =
  return $ mayLeakyGV l "(,)" @@ (toOilVar <$> [left, right])
toOilExpr l T.PCase {..} = do
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
      $ toOilExpr l body
  let cond' = toOilVar cond
  return $
    case condLabel of
      SafeL ->
        case'
          cond'
          [("(,)", [(xl, lBinder), (xr, rBinder)], body')]
      LeakyL ->
        GV (lCaseName "*")
          @@ [ lIfInst $ fromJust mTy,
               cond',
               lams' [(xl, lBinder), (xr, rBinder)] body'
             ]
toOilExpr _ T.OPair {..} =
  return $ GV aConcat @@ (toOilVar <$> [left, right])
toOilExpr l T.OPCase {..} = do
  (ty, _) <- lookupTy cond
  let (leftTy, rightTy) =
        case ty of
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
      $ toOilExpr l body
  let cond' = toOilVar cond
  return $
    lets'
      [ (xl, lBinder, GV aSlice @@ [cond', ILit 0, leftSize]),
        (xr, rBinder, GV aSlice @@ [cond', leftSize, rightSize])
      ]
      body'
toOilExpr _ T.OInj {..} = do
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
toOilExpr l T.OCase {..} = do
  (ty, _) <- lookupTy cond
  let (leftTy, rightTy) =
        case ty of
          T.OSum {..} -> (left, right)
          _ -> oops "Not an oblivious sum"
  leftSize <- toOilSize leftTy
  rightSize <- toOilSize rightTy
  tagSize <- toOilSize T.OBool
  (xl, lBody) <- unbind1 lBnd
  (xr, rBody) <- unbind1 rBnd
  lBody' <- extendCtx1 xl leftTy SafeL $ toOilExpr l lBody
  rBody' <- extendCtx1 xr rightTy SafeL $ toOilExpr l rBody
  let cond' = toOilVar cond
  return $
    lIfInst (fromJust mTy)
      @@ [ GV aSlice @@ [cond', ILit 0, tagSize],
           lets'
             [(xl, lBinder, GV aSlice @@ [cond', tagSize, leftSize])]
             lBody',
           lets'
             [(xr, rBinder, GV aSlice @@ [cond', tagSize, rightSize])]
             rBody'
         ]
toOilExpr _ T.Mux {..} = do
  -- The right branch should have the same type.
  (ty, _) <- lookupTy left
  size <- toOilSize ty
  return $ GV aMux @@ (size : (toOilVar <$> [cond, left, right]))
toOilExpr _ T.Promote {..} = do
  (ty, _) <- lookupTy expr
  return $ retInst ty @@ [toOilVar expr]
toOilExpr _ T.Tape {..} = do
  (ty, _) <- lookupTy expr
  size <- toOilSize ty
  return $ GV (leakyName "tape") @@ [size, toOilVar expr]
toOilExpr _ _ = oops "Not a term in core taype ANF"

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
  return $ GV "+" @@ [ILit 1, GV "$max" @@ [lSize, rSize]]
toOilSize T.App {appKind = Just TypeApp, fn = T.GV {..}, ..} =
  return $ GV ref @@ toOilVar <$> args
toOilSize T.Let {..} = do
  rhs' <- toOilExpr SafeL rhs
  (x, body) <- unbind1 bnd
  body' <- extendCtx1 x (fromJust mTy) SafeL $ toOilSize body
  return $ let' x binder rhs' body'
toOilSize T.Ite {..} = do
  left' <- toOilSize left
  right' <- toOilSize right
  return $ ite_ (toOilVar cond) left' right'
toOilSize T.Case {..} = do
  (_, paraTypess, _) <- lookupADT cond
  alts' <- zipWithM go (toList alts) paraTypess
  return $ case' (toOilVar cond) alts'
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
toOilTy :: Label -> T.Ty a -> Ty b
toOilTy SafeL = toOilTy_
toOilTy LeakyL = toLeakyTy . toOilTy_

-- | Translate a taype type to the corresponding plain OIL type.
--
-- The taype type is well-kinded and in core taype ANF. The resulting OIL type
-- itself is not leaky, but function types may have leaky arguments.
--
-- If the taype type is obliviously kinded, then the result should be oblivious
-- array.
--
-- Two equivalent taype type should be translated to the same OIL type.
toOilTy_ :: T.Ty a -> Ty b
toOilTy_ T.TBool = tGV "bool"
toOilTy_ T.TInt = TInt
toOilTy_ T.GV {..} = tGV ref
toOilTy_ T.Prod {..} = "*" @@ [toOilTy_ left, toOilTy_ right]
toOilTy_ T.Pi {..} =
  let dom = toOilTy (fromJust label) ty
      -- A bit hacky here. The bound variable is instantiated arbitrarily
      -- because we do not inspect it when translating types anyway. This is
      -- convenient so we don't have to wrap the function in the 'TslM' monad.
      cod = toOilTy_ $ instantiate_ T.VUnit bnd
   in Arrow {..}
-- Oblivious types, including type level computation, are translated into
-- oblivious array.
toOilTy_ _ = OArray

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
toLeakyTy Arrow {..} = leakyName "->" @@ [dom, toLeakyTy cod]
toLeakyTy TApp {..} = TApp {tctor = leakyName tctor, args = toLeakyTy <$> args}
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
retInst_ :: Ty a -> Expr b
retInst_ TInt = GV (retName "int")
retInst_ OArray = GV (retName aName)
retInst_ Arrow {..} = GV (retName "->") @@ [retInst_ cod]
retInst_ TApp {..} = GV (retName tctor) @@ retInst_ <$> args
retInst_ _ = oops "Cannot resolve return instance of type variable"

-- | Resolve the return instance of the leaky structure of a taype type.
retInst :: T.Ty Name -> Expr b
retInst = retInst_ . toOilTy_

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
lIfInst_ Arrow {} = GV (lIfName "->")
lIfInst_ TApp {..} = GV (lIfName tctor)
lIfInst_ _ = oops "Cannot resolve leaky if instance of type variable"

-- | Resolve the leaky if instance of the leaky structure of a taype type.
lIfInst :: T.Ty Name -> Expr b
lIfInst = lIfInst_ . toOilTy_

----------------------------------------------------------------
-- Translating definitions

-- | Translate taype definitions to the corresponding OIL definitions.
toOilDefs :: Options -> GCtx Name -> T.Defs Name -> Defs b a
toOilDefs Options {..} gctx = foldMap go
  where
    go =
      secondF (closedDef . runFreshM . biplateM simp)
        . runTslM Env {tctx = TCtx [], ..}
        . toOilDef
    simp =
      (if optNoReadableOil then return else readableExpr) <=< simpExpr

-- | Translate a taype definition to the corresponding OIL definition.
--
-- The ADT definition is translated to multiple OIL definitions, so this
-- function returns a list of OIL definitions.
toOilDef :: T.NamedDef Name -> TslM [NamedDef Name Name]
toOilDef (name, def) = case def of
  T.FunDef {..} -> do
    let l = fromJust label
        ty' = toOilTy l ty
    expr' <- toOilExpr l expr
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
    let ty' = toOilTy SafeL ty
    return $
      one
        ( name,
          FunDef
            { binders = [],
              tyBnd = abstract_ [] $ Arrow ty' sizeTy,
              expr = lam' x binder body'
            }
        )
  T.ADTDef {..} -> do
    let (ctorNames, paraTypess) = unzip $ toList ctors
        sParaTypess = toOilTy SafeL <<$>> paraTypess
        lParaTypess = toOilTy LeakyL <<$>> paraTypess
    return
      [ -- ADT
        adtDef_ name [] $ zip ctorNames sParaTypess,
        -- Leaky ADT
        adtDef_ (l_ name) [] $
          zipWith ((,) . l_) ctorNames lParaTypess
            `snoc` (lif_ name, [OArray, "$self", "$self"]),
        -- Return instance of the leaky type
        funDef_ (ret_ name) [] (ar_ [TV name, l_ name]) $
          lam_ "x" $
            case_ "x" $
              zipWith retAlt ctorNames sParaTypess,
        -- Leaky case analysis
        funDef_
          (lcase_ name)
          [l_ "r"]
          ( ar_ $
              [ar_ [OArray, l_ "r", l_ "r", l_ "r"], l_ name]
                <> (lParaTypess <&> \ts -> ar_ $ ts <> [l_ "r"])
                `snoc` l_ "r"
          )
          $ lCaseBody ctorNames lParaTypess
      ]
  _ -> oops "Translating constructor or builtin definitions"
  where
    vars prefix n = (prefix <>) . show <$> [1 .. n]
    retAlt ctor paraTypes =
      let xs = vars "x" $ length paraTypes
       in ( ctor,
            toBinder <$> xs,
            l_ ctor
              @@ zipWith (\t x -> retInst_ t @@ [V x]) paraTypes xs
          )
    lCaseBody ctors tss =
      let fs = vars (l_ "f") $ length tss
       in lams_ ([lif_ "r", l_ "x"] <> (toBinder <$> fs)) $
            case_ (l_ "x") $
              zipWith3 lCaseAlt ctors fs tss
                `snoc` ( lif_ name,
                         [o_ "b", l_ "x1", l_ "x2"],
                         lif_ "r"
                           @@ [ o_ "b",
                                "$self" @@ [lif_ "r", l_ "x1"] <> (V <$> fs),
                                "$self" @@ [lif_ "r", l_ "x2"] <> (V <$> fs)
                              ]
                       )
    lCaseAlt ctor f ts =
      let xs = vars (l_ "x") $ length ts
       in (l_ ctor, toBinder <$> xs, V f @@ V <$> xs)

----------------------------------------------------------------
-- Simplification of OIL expressions

-- | Simplify OIL expressions.
--
-- This function performs various simplifcation such as let flattening and
-- application collapsing.
simpExpr :: MonadFresh m => Expr Name -> m (Expr Name)
simpExpr = transformM go
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
        return $ let' x binderN rhsN body'
      _ -> return e
    go e = return e

-- | Make the generated OIL programs more readable.
--
-- This function subsitutes all let bindings that do not have a named binder.
readableExpr :: MonadFresh m => Expr Name -> m (Expr Name)
readableExpr = transformM go
  where
    go Let {binder = Nothing, ..} = return $ instantiate_ rhs bnd
    go e = return e

----------------------------------------------------------------
-- Helper functions

mayLeakyGV :: Label -> Text -> Expr a
mayLeakyGV SafeL x = GV x
mayLeakyGV LeakyL x = GV $ leakyName x

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
      [ (ret_ aName, [OArray]),
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
      [ (l_ "False", []),
        (l_ "True", []),
        (lif_ "bool", [OArray, "$self", "$self"])
      ],
    funDef_
      (ret_ "bool")
      []
      (ar_ ["bool", l_ "bool"])
      $ lam_
        "b"
        (ite_ "b" (l_ "True") (l_ "False")),
    funDef_
      (s_ "bool")
      []
      (ar_ ["bool", OArray])
      $ lam_
        "b"
        (ite_ "b" (s_ "int" @@ [ILit 1]) (s_ "int" @@ [ILit 0])),
    funDef_
      (r_ "bool")
      []
      (ar_ [OArray, l_ "bool"])
      $ lam_
        (o_ "b")
        (lif_ "bool" @@ [o_ "b", l_ "True", l_ "False"]),
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
            [ (l_ "False", [], l_ "ff"),
              (l_ "True", [], l_ "ft"),
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
            [ (l_ "False", [], ret_ aName @@ [s_ "bool" @@ ["False"]]),
              (l_ "True", [], ret_ aName @@ [s_ "bool" @@ ["True"]]),
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
        (ret_ "int", [TInt]),
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
            [ (r_ "int", [o_ "n"], ret_ aName @@ [o_ "n"]),
              (ret_ "int", ["n"], ret_ aName @@ [s_ "int" @@ ["n"]]),
              ( lif_ "int",
                [o_ "b", l_ "n1", l_ "n2"],
                lif_ aName
                  @@ [o_ "b", "$self" @@ [l_ "n1"], "$self" @@ [l_ "n2"]]
              )
            ]
        ),
    lBopDef "+" "int",
    lBopDef "-" "int",
    lBopDef "<=" "bool",
    lBopDef "==" "bool",
    -- Helper functions
    funDef_
      "$max"
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
      [l_ "a", l_ "b"]
      [ (l_ "(,)", [l_ "a", l_ "b"]),
        ( lif_ "*",
          [ OArray,
            l_ "*" @@ [l_ "a", l_ "b"],
            l_ "*" @@ [l_ "a", l_ "b"]
          ]
        )
      ],
    funDef_
      (ret_ "*")
      ["a", l_ "a", "b", l_ "b"]
      ( ar_
          [ ar_ ["a", l_ "a"],
            ar_ ["b", l_ "b"],
            "*" @@ ["a", "b"],
            l_ "*" @@ [l_ "a", l_ "b"]
          ]
      )
      $ lams_
        [ret_ "a", ret_ "b", "p"]
        ( case_
            "p"
            [ ( "(,)",
                ["x", "y"],
                l_ "(,)" @@ [ret_ "a" @@ ["x"], ret_ "b" @@ ["y"]]
              )
            ]
        ),
    funDef_
      (lcase_ "*")
      [l_ "a", l_ "b", l_ "r"]
      ( ar_
          [ ar_ [OArray, l_ "r", l_ "r", l_ "r"],
            l_ "*" @@ [l_ "a", l_ "b"],
            ar_ [l_ "a", l_ "b", l_ "r"],
            l_ "r"
          ]
      )
      $ lams_
        [lif_ "r", l_ "p", l_ "f"]
        ( case_
            (l_ "p")
            [ (l_ "(,)", [l_ "x", l_ "y"], l_ "f" @@ [l_ "x", l_ "y"]),
              ( lif_ "*",
                [o_ "b", l_ "p1", l_ "p2"],
                lif_ "r"
                  @@ [ o_ "b",
                       "$self" @@ [lif_ "r", l_ "p1", l_ "f"],
                       "$self" @@ [lif_ "r", l_ "p2", l_ "f"]
                     ]
              )
            ]
        ),
    -- Function type
    adtDef_
      (l_ "->")
      ["a", l_ "b"]
      [ (l_ "lam", [ar_ ["a", l_ "b"]]),
        ( lif_ "->",
          [ OArray,
            l_ "->" @@ ["a", l_ "b"],
            l_ "->" @@ ["a", l_ "b"]
          ]
        )
      ],
    funDef_
      (ret_ "->")
      ["a", "b", l_ "b"]
      (ar_ [ar_ ["b", l_ "b"], ar_ ["a", "b"], l_ "->" @@ ["a", l_ "b"]])
      $ lams_
        [ret_ "b", "f"]
        (l_ "lam" @@ [lam_ "x" $ ret_ "b" @@ ["f" @@ ["x"]]]),
    funDef_
      (l_ "ap")
      ["a", l_ "b"]
      ( ar_
          [ ar_ [OArray, l_ "b", l_ "b", l_ "b"],
            l_ "->" @@ ["a", l_ "b"],
            "a",
            l_ "b"
          ]
      )
      $ lams_
        [lif_ "b", l_ "f", "x"]
        ( case_
            (l_ "f")
            [ (l_ "lam", ["f"], "f" @@ ["x"]),
              ( lif_ "->",
                [o_ "b", l_ "f1", l_ "f2"],
                lif_ "b"
                  @@ [ o_ "b",
                       "$self" @@ [lif_ "b", l_ "f1", "x"],
                       "$self" @@ [lif_ "b", l_ "f2", "x"]
                     ]
              )
            ]
        ),
    -- Tape
    funDef_
      (l_ "tape")
      []
      (ar_ [sizeTy, l_ aName, OArray])
      $ lams_
        ["n", l_ "a"]
        ( case_
            (l_ "a")
            [ (ret_ aName, [o_ "a"], o_ "a"),
              ( lif_ aName,
                [o_ "b", l_ "a1", l_ "a2"],
                V aMux
                  @@ [ "n",
                       o_ "b",
                       "$self" @@ ["n", l_ "a1"],
                       "$self" @@ ["n", l_ "a2"]
                     ]
              )
            ]
        ),
    -- Oblivious injection
    funDef_
      (o_ "inl")
      []
      (ar_ [sizeTy, sizeTy, OArray, OArray])
      $ lams_
        ["m", "n", o_ "a"]
        ( V aConcat
            @@ [ s_ "bool" @@ ["True"],
                 ite_
                   ("<=" @@ ["n", "m"])
                   (o_ "a")
                   ( V aConcat
                       @@ [o_ "a", V aNew @@ ["-" @@ ["n", "m"]]]
                   )
               ]
        ),
    funDef_
      (o_ "inr")
      []
      (ar_ [sizeTy, sizeTy, OArray, OArray])
      $ lams_
        ["m", "n", o_ "a"]
        ( V aConcat
            @@ [ s_ "bool" @@ ["False"],
                 ite_
                   ("<=" @@ ["m", "n"])
                   (o_ "a")
                   ( V aConcat
                       @@ [o_ "a", V aNew @@ ["-" @@ ["m", "n"]]]
                   )
               ]
        )
  ]

-- | Build a leaky definition for binary operator, e.g., '+'.
lBopDef :: Text -> Text -> NamedDef b a
lBopDef name cod =
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
                  ( ret_ "int",
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
            ( ret_ "int",
              ["m"],
              case_
                (l_ "n")
                [ ( r_ "int",
                    [o_ "n"],
                    r_ cod
                      @@ [o_ name @@ [s_ "int" @@ ["m"], o_ "n"]]
                  ),
                  ( ret_ "int",
                    ["n"],
                    ret_ cod
                      @@ [V name @@ ["m", "n"]]
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

lif_ :: IsString a => Text -> a
lif_ = fromString . toString . lIfName

ret_ :: IsString a => Text -> a
ret_ = fromString . toString . retName

lcase_ :: IsString a => Text -> a
lcase_ = fromString . toString . lCaseName

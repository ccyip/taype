{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Syntax of the surface and core taype language.
module Taype.Syntax
  ( -- * Syntax
    Expr (..),
    Typ,
    Label,
    AppKind (..),
    CaseAlt (..),
    Def,
    NamedDef,
    DefB (..),
    NamedDefB (..),
    Attribute (..),
    LabelPolyStrategy (..),

    -- * Binders
    Binder,
    BinderM (..),
    fromBinder,
    isBinderName,
    binderNameEq,
    findDupBinderName,

    -- * Specialized locally nameless abstraction and instantiation
    abstract1Binder,
    abstract2Binders,
    abstractBinders,
    instantiate1Binder,
    instantiate2Binders,
    instantiateBinders,

    -- * Smart constructors
    lam_,
    lams_,
    pi_,
    app_,
    iapp_,
    tapp_,
    let_,
    lets_,
    ite_,
    oite_,
    case_,
    ocase_,
    pcase_,
    opcase_,
  )
where

import Bound
import Control.Monad
import Data.Deriving
import Data.Functor.Classes
import Data.List (findIndex, groupBy)
import Prettyprinter
import Taype.Error
import Taype.Fresh
import qualified Text.Show

-- | Taype expression, including the surface and the core syntax
data Expr a
  = -- | Local variable
    V {name :: a}
  | -- | Global variable
    GV {ref :: Text}
  | -- | Dependent function type
    Pi
      { typ :: Typ a,
        label :: Maybe Label,
        body :: Scope () Typ a
      }
  | -- | Lambda abstraction
    Lam
      { maybeType :: Maybe (Typ a),
        label :: Maybe Label,
        body :: Scope () Expr a
      }
  | -- | Application, including function application, type application, etc
    App
      { appKind :: Maybe AppKind,
        fn :: Expr a,
        args :: [Expr a]
      }
  | -- | Let binding
    Let
      { maybeType :: Maybe (Typ a),
        label :: Maybe Label,
        rhs :: Expr a,
        body :: Scope () Expr a
      }
  | -- | Unit type
    TUnit
  | -- | Unit value
    VUnit
  | -- | Boolean type
    TBool
  | -- | Oblivious Boolean type
    OBool
  | -- | Boolean literal
    BLit {bLit :: Bool}
  | -- | Integer type
    TInt
  | -- | Oblivious integer type
    OInt
  | -- | Integer literal
    ILit {iLit :: Int}
  | -- | (Dependent) if conditional
    Ite
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | (Dependent) case analysis.
    --  Do not support empty type, i.e. 'alts' must be non empty
    Case
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        alts :: NonEmpty (CaseAlt Expr a)
      }
  | -- | Oblivious and leaky if conditional
    OIte
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Product type
    Prod {left :: Typ a, right :: Typ a}
  | -- | Normal pair
    Pair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for product
    PCase
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        body2 :: Scope Bool Expr a
      }
  | -- | Oblivious product type
    OProd {left :: Typ a, right :: Typ a}
  | -- | Oblivious pair
    OPair {left :: Expr a, right :: Expr a}
  | -- | Case analysis for oblivious product
    OPCase
      { cond :: Expr a,
        body2 :: Scope Bool Expr a
      }
  | -- | Oblivious sum type
    OSum {left :: Typ a, right :: Typ a}
  | -- | Oblivious injection
    OInj
      { maybeType :: Maybe (Typ a),
        tag :: Bool,
        inj :: Expr a
      }
  | -- | (Leaky) case analysis for oblivious sum type
    OCase
      { maybeType :: Maybe (Typ a),
        cond :: Expr a,
        lBody :: Scope () Expr a,
        rBody :: Scope () Expr a
      }
  | -- | Oblivious conditional, i.e. multiplexer
    Mux
      { cond :: Expr a,
        ifTrue :: Expr a,
        ifFalse :: Expr a
      }
  | -- | Ascription. Do not appear in core taype
    Asc {typ :: Typ a, expr :: Expr a}
  | -- | Label promotion. Do not appear in surface taype
    Promote {expr :: Expr a}
  | -- | Tape, the key operation in taype
    Tape {expr :: Expr a}
  | -- | Add location information
    Loc {loc :: Int, expr :: Expr a}
  deriving stock (Functor, Foldable, Traversable)

-- | A type in taype is also an expression
type Typ = Expr

-- | A leakage label is just a Boolean
type Label = Bool

-- | Application kinds
data AppKind = FunApp | CtorApp | BuiltinApp | InfixApp | TypeApp
  deriving stock (Eq, Show)

-- | Case alternatives
data CaseAlt f a = CaseAlt
  { ctor :: Text,
    binders :: [Binder],
    body :: Scope Int f a
  }
  deriving stock (Functor, Foldable, Traversable)

-- | A binder is either a name, or anonymous, i.e. \"_\", with location
type Binder = BinderM Text

-- | Generalized binders
data BinderM a = Named Int a | Anon
  deriving stock (Eq, Show)

instance IsString a => IsString (BinderM a) where
  fromString = Named (-1) . fromString

-- | Global definition
type Def = DefB Expr

type NamedDef = NamedDefB Expr

-- | Generalized global definition
data DefB f a
  = -- Function
    FunDef {attr :: Attribute, typ :: f a, label :: Maybe Label, expr :: f a}
  | -- | Algebraic data type. Do not support empty type
    ADTDef {ctors :: NonEmpty Text}
  | -- | Oblivious algebraic data type. Only support one argument for now
    OADTDef {typ :: f a, body :: Scope () f a}
  | -- | Constructor
    CtorDef {paraTypes :: [f a], dataType :: Text}
  | -- | Builtin operation
    BuiltinDef {paraTypes :: [f a], resType :: f a, strategy :: LabelPolyStrategy}
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

data NamedDefB f a = NamedDef {name :: Text, loc :: Int, def :: DefB f a}
  deriving stock (Eq, Show)

data Attribute = SectionAttr | RetractionAttr | SafeAttr | LeakyAttr
  deriving stock (Eq, Show)

data LabelPolyStrategy = JoinStrategy | TopStrategy
  deriving stock (Eq, Show)

instance Applicative Expr where
  pure = V
  (<*>) = ap

instance Monad Expr where
  V {..} >>= f = f name
  GV {..} >>= _ = GV {..}
  Pi {..} >>= f = Pi {typ = typ >>= f, body = body >>>= f, ..}
  Lam {..} >>= f = Lam {maybeType = maybeType <&> (>>= f), body = body >>>= f, ..}
  App {..} >>= f = App {fn = fn >>= f, args = args <&> (>>= f), ..}
  Let {..} >>= f =
    Let
      { maybeType = maybeType <&> (>>= f),
        rhs = rhs >>= f,
        body = body >>>= f,
        ..
      }
  TUnit >>= _ = TUnit
  VUnit >>= _ = VUnit
  TBool >>= _ = TBool
  OBool >>= _ = OBool
  BLit {..} >>= _ = BLit {..}
  TInt >>= _ = TInt
  OInt >>= _ = OInt
  ILit {..} >>= _ = ILit {..}
  Ite {..} >>= f =
    Ite
      { maybeType = maybeType <&> (>>= f),
        cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f
      }
  Case {..} >>= f =
    Case
      { maybeType = maybeType <&> (>>= f),
        cond = cond >>= f,
        alts = alts <&> (>>>= f),
        ..
      }
  OIte {..} >>= f =
    OIte
      { cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f,
        ..
      }
  Prod {..} >>= f = Prod {left = left >>= f, right = right >>= f, ..}
  Pair {..} >>= f = Pair {left = left >>= f, right = right >>= f, ..}
  PCase {..} >>= f =
    PCase
      { maybeType = maybeType <&> (>>= f),
        cond = cond >>= f,
        body2 = body2 >>>= f,
        ..
      }
  OProd {..} >>= f = OProd {left = left >>= f, right = right >>= f, ..}
  OPair {..} >>= f = OPair {left = left >>= f, right = right >>= f, ..}
  OPCase {..} >>= f =
    OPCase
      { cond = cond >>= f,
        body2 = body2 >>>= f,
        ..
      }
  OSum {..} >>= f = OSum {left = left >>= f, right = right >>= f, ..}
  OInj {..} >>= f = OInj {maybeType = maybeType <&> (>>= f), inj = inj >>= f, ..}
  OCase {..} >>= f =
    OCase
      { maybeType = maybeType <&> (>>= f),
        cond = cond >>= f,
        lBody = lBody >>>= f,
        rBody = rBody >>>= f,
        ..
      }
  Mux {..} >>= f =
    Mux
      { cond = cond >>= f,
        ifTrue = ifTrue >>= f,
        ifFalse = ifFalse >>= f,
        ..
      }
  Asc {..} >>= f = Asc {typ = typ >>= f, expr = expr >>= f, ..}
  Promote {..} >>= f = Promote {expr = expr >>= f, ..}
  Tape {..} >>= f = Tape {expr = expr >>= f, ..}
  Loc {..} >>= f = Loc {expr = expr >>= f, ..}

instance Bound CaseAlt where
  CaseAlt {..} >>>= f = CaseAlt {body = body >>>= f, ..}

instance Bound DefB where
  FunDef {..} >>>= f = FunDef {typ = typ >>= f, expr = expr >>= f, ..}
  ADTDef {..} >>>= _ = ADTDef {..}
  OADTDef {..} >>>= f = OADTDef {typ = typ >>= f, body = body >>>= f}
  CtorDef {..} >>>= f = CtorDef {paraTypes = paraTypes <&> (>>= f), ..}
  BuiltinDef {..} >>>= f =
    BuiltinDef
      { paraTypes = paraTypes <&> (>>= f),
        resType = resType >>= f,
        ..
      }

instance (Eq1 f, Monad f) => Eq1 (CaseAlt f) where
  liftEq
    eq
    (CaseAlt {ctor, body})
    (CaseAlt {ctor = ctor', body = body'}) =
      ctor == ctor' && liftEq eq body body'

deriveEq1 ''Expr

instance (Eq1 f, Monad f, Eq a) => Eq (CaseAlt f a) where (==) = eq1

instance Eq a => Eq (Expr a) where (==) = eq1

deriveShow1 ''CaseAlt
deriveShow1 ''Expr

instance (Show1 f, Show a) => Show (CaseAlt f a) where showsPrec = showsPrec1

instance Show a => Show (Expr a) where showsPrec = showsPrec1

fromBinder :: BinderM a -> a
fromBinder (Named _ name) = name
fromBinder Anon = oops "Instantiating an anonymous binder"

isBinderName :: (Eq a) => a -> BinderM a -> Bool
isBinderName x (Named _ y) = x == y
isBinderName _ Anon = False

-- | Check if two binders have the same name. Two anonymous binder DO NOT have
-- the same name
binderNameEq :: (Eq a) => BinderM a -> BinderM a -> Bool
binderNameEq (Named _ x) (Named _ y) = x == y
binderNameEq _ _ = False

-- | Return 'Nothing' if the list of binders do not has duplicate names, or
-- 'Just' the duplicate binder
findDupBinderName :: (Eq a) => [BinderM a] -> Maybe (BinderM a)
findDupBinderName binders = find ((> 1) . length) groups >>= viaNonEmpty head
  where
    groups = groupBy binderNameEq binders

abstract1Binder :: (Monad f, Eq a) => BinderM a -> f a -> Scope () f a
abstract1Binder binder = abstract $ \name ->
  if isBinderName name binder
    then Just ()
    else Nothing

abstract2Binders :: (Monad f, Eq a) => BinderM a -> BinderM a -> f a -> Scope Bool f a
abstract2Binders left right = abstract $ \name ->
  if
      | isBinderName name left -> Just True
      | isBinderName name right -> Just False
      | otherwise -> Nothing

abstractBinders :: (Monad f, Eq a) => [BinderM a] -> f a -> Scope Int f a
abstractBinders binders = abstract $ \name -> findIndex (isBinderName name) binders

instantiate1Binder :: (Monad f) => BinderM a -> Scope n f a -> f a
instantiate1Binder = instantiate . const . return . fromBinder

instantiate2Binders :: (Monad f) => BinderM a -> BinderM a -> Scope Bool f a -> f a
instantiate2Binders left right = instantiate $ \b ->
  return . fromBinder $ if b then left else right

instantiateBinders :: (Monad f) => [BinderM a] -> Scope Int f a -> f a
instantiateBinders binders = instantiate $ \i ->
  case binders !!? i of
    Just binder -> return $ fromBinder binder
    Nothing -> oops "Instantiating an out-of-bound binder"

lam_ :: (Eq a) => BinderM a -> Maybe (Typ a) -> Expr a -> Expr a
lam_ binder maybeType body =
  Lam {label = Nothing, body = abstract1Binder binder body, ..}

-- | A smart constructor for lambda abstraction that takes a list of arguments
lams_ :: (Eq a) => NonEmpty (BinderM a, Maybe (Typ a)) -> Expr a -> Expr a
lams_ args body = foldr (uncurry lam_) body args

pi_ :: (Eq a) => BinderM a -> Typ a -> Expr a -> Expr a
pi_ binder typ body =
  Pi {label = Nothing, body = abstract1Binder binder body, ..}

app_ :: Expr a -> [Expr a] -> Expr a
app_ fn args = App {appKind = Nothing, ..}

iapp_ :: Expr a -> [Expr a] -> Expr a
iapp_ fn args = App {appKind = Just InfixApp, ..}

tapp_ :: Expr a -> [Expr a] -> Typ a
tapp_ fn args = App {appKind = Just TypeApp, ..}

let_ :: (Eq a) => BinderM a -> Maybe (Typ a) -> Expr a -> Expr a -> Expr a
let_ binder maybeType rhs body =
  Let {label = Nothing, body = abstract1Binder binder body, ..}

-- | A smart constructor for let that takes a list of bindings
lets_ :: (Eq a) => NonEmpty (BinderM a, Maybe (Typ a), Expr a) -> Expr a -> Expr a
lets_ bindings body = foldr go body bindings
  where
    go (binder, maybeType, rhs) = let_ binder maybeType rhs

ite_ :: Expr a -> Expr a -> Expr a -> Expr a
ite_ cond ifTrue ifFalse = Ite {maybeType = Nothing, ..}

oite_ :: Expr a -> Expr a -> Expr a -> Expr a
oite_ cond ifTrue ifFalse = OIte {..}

case_ :: (a ~ Text) => Expr a -> NonEmpty (Text, [BinderM a], Expr a) -> Expr a
case_ cond alts = Case {maybeType = Nothing, alts = abstr <$> alts, ..}
  where
    abstr (ctor, binders, body) =
      CaseAlt {body = abstractBinders binders body, ..}

ocase_ :: (Eq a) => Expr a -> BinderM a -> Expr a -> BinderM a -> Expr a -> Expr a
ocase_ cond lBinder lBody rBinder rBody =
  OCase
    { maybeType = Nothing,
      lBody = abstract1Binder lBinder lBody,
      rBody = abstract1Binder rBinder rBody,
      ..
    }

pcase_ :: (Eq a) => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
pcase_ cond left right body =
  PCase {maybeType = Nothing, body2 = abstract2Binders left right body, ..}

opcase_ :: (Eq a) => Expr a -> BinderM a -> BinderM a -> Expr a -> Expr a
opcase_ cond left right body =
  OPCase {body2 = abstract2Binders left right body, ..}

-- | Pretty printer for Taype expressions
instance Pretty (Expr Text) where
  pretty = runFresh . prettyExpr

prettyExpr :: Expr Text -> Fresh (Doc ann)
prettyExpr V {..} = return $ pretty name
prettyExpr GV {..} = return $ pretty ref
prettyExpr Pi {..} = do
  x <- freshName
  binderDoc <- prettyBinder x (Just typ)
  bodyDoc <- prettyExpr $ instantiate1 (return x) body
  return $ parens binderDoc <+> "->" <+> bodyDoc
prettyExpr Lam {..} = do
  x <- freshName
  binderDoc <- prettyBinder x maybeType
  bodyDoc <- prettyExpr $ instantiate1 (return x) body
  return $ backslash <> binderDoc <+> "->" <+> bodyDoc
prettyExpr App {..} = do
  fnDoc <- prettyExpr fn
  argsDoc <- mapM prettyExpr args
  return $ fnDoc <+> hsep (parens <$> argsDoc)
prettyExpr Let {..} = do
  x <- freshName
  binderDoc <- prettyBinder x maybeType
  rhsDoc <- prettyExpr rhs
  bodyDoc <- prettyExpr $ instantiate1 (return x) body
  return $ "let" <+> binderDoc <+> equals <+> rhsDoc <+> "in" <> hardline <> bodyDoc
prettyExpr TUnit = return "Unit"
prettyExpr VUnit = return "()"
prettyExpr TBool = return "Bool"
prettyExpr OBool = return "~Bool"
prettyExpr BLit {..} = return $ if bLit then "True" else "False"
prettyExpr TInt = return "Int"
prettyExpr OInt = return "~Int"
prettyExpr ILit {..} = return $ pretty iLit
prettyExpr Ite {..} = do
  condDoc <- prettyExpr cond
  ifTrueDoc <- prettyExpr ifTrue
  ifFalseDoc <- prettyExpr ifFalse
  return $ "if" <+> condDoc <+> "then" <+> ifTrueDoc <+> "else" <+> ifFalseDoc
prettyExpr Case {..} = do
  condDoc <- prettyExpr cond
  altsDoc <- mapM prettyAlt alts
  return $ "case" <+> condDoc <+> "of" <+> sep (toList altsDoc)
  where
    prettyAlt CaseAlt {..} = do
      xs <- freshNames $ length binders
      bodyDoc <-
        prettyExpr $
          instantiate
            ( \n -> case xs !!? n of
                Just x -> return x
                Nothing -> oops "instantiating an out-of-bound name"
            )
            body
      return $ pipe <+> pretty ctor <> foldMap (\x -> space <> pretty x) xs <+> "->" <+> bodyDoc
prettyExpr OIte {..} = do
  condDoc <- prettyExpr cond
  ifTrueDoc <- prettyExpr ifTrue
  ifFalseDoc <- prettyExpr ifFalse
  return $ "~if" <+> condDoc <+> "then" <+> ifTrueDoc <+> "else" <+> ifFalseDoc
prettyExpr Prod {..} = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ leftDoc <+> "*" <+> rightDoc
prettyExpr Pair {..} = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ lparen <> leftDoc <> comma <+> rightDoc <> rparen
prettyExpr PCase {..} = do
  condDoc <- prettyExpr cond
  xl <- freshName
  xr <- freshName
  bodyDoc <- prettyExpr $ instantiate (\b -> return $ if b then xl else xr) body2
  return $
    "case" <+> condDoc <+> "of"
      <+> lparen <> pretty xl <> comma
      <+> pretty xr <> rparen
      <+> "->"
      <+> bodyDoc
prettyExpr OProd {..} = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ leftDoc <+> "~*" <+> rightDoc
prettyExpr OPair {..} = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ "~" <> lparen <> leftDoc <> comma <+> rightDoc <> rparen
prettyExpr OPCase {..} = do
  condDoc <- prettyExpr cond
  xl <- freshName
  xr <- freshName
  bodyDoc <- prettyExpr $ instantiate (\b -> return $ if b then xl else xr) body2
  return $
    "~case" <+> condDoc <+> "of"
      <+> "~" <> lparen <> pretty xl <> comma
      <+> pretty xr <> rparen
      <+> "->"
      <+> bodyDoc
prettyExpr OSum {..} = do
  leftDoc <- prettyExpr left
  rightDoc <- prettyExpr right
  return $ leftDoc <+> "~+" <+> rightDoc
prettyExpr OInj {..} = do
  typeDoc <- maybe (return "") prettyInjType maybeType
  injDoc <- prettyExpr inj
  return $ (if tag then "~inl" else "~inr") <> typeDoc <+> injDoc
  where
    prettyInjType typ = do
      typeDoc <- prettyExpr typ
      return $ langle <> typeDoc <> rangle
prettyExpr OCase {..} = do
  condDoc <- prettyExpr cond
  xl <- freshName
  xr <- freshName
  lBodyDoc <- prettyExpr $ instantiate1 (return xl) lBody
  rBodyDoc <- prettyExpr $ instantiate1 (return xr) lBody
  return $
    "~case" <+> condDoc <+> "of"
      <+> pipe
      <+> "~inl"
      <+> pretty xl
      <+> "->"
      <+> lBodyDoc
      <+> pipe
      <+> "~inr"
      <+> pretty xr
      <+> "->"
      <+> rBodyDoc
prettyExpr Mux {..} = do
  condDoc <- prettyExpr cond
  ifTrueDoc <- prettyExpr ifTrue
  ifFalseDoc <- prettyExpr ifFalse
  return $ "mux" <+> condDoc <+> ifTrueDoc <+> ifFalseDoc
prettyExpr Asc {..} = do
  typeDoc <- prettyExpr typ
  exprDoc <- prettyExpr expr
  return $ lparen <> exprDoc <+> colon <+> typeDoc <> rparen
prettyExpr Promote {..} = ("promote" <+>) <$> prettyExpr expr
prettyExpr Tape {..} = ("tape" <+>) <$> prettyExpr expr
prettyExpr Loc {..} = prettyExpr expr

-- | Pretty printer for Taype definitions
instance Pretty (NamedDef Text) where
  pretty _ = "<cannot print a standalone definition>"
  prettyList defs = foldMap go defs <> hardline
    where
      go def = prettyDef defs def <> hardline <> hardline

prettyDef :: [NamedDef Text] -> NamedDef Text -> Doc ann
prettyDef defs NamedDef {name, def} = case def of
  FunDef {..} ->
    "#" <> lbracket <> pretty attr <> rbracket <> hardline
      <> "fn" <+> pretty name <+> colon <+> pretty typ <+> equals
      <> pretty expr
  ADTDef {..} ->
    "data" <+> pretty name <+> equals
      <+> concatWith (\x y -> x <+> pipe <+> y) (prettyCtors defs <$> ctors)
  OADTDef {..} ->
    "obliv" <+> pretty name <+> rest
    where
      rest = runFresh $ do
        x <- freshName
        binderDoc <- prettyBinder x (Just typ)
        bodyDoc <- prettyExpr (instantiate1 (return x) body)
        return $ parens binderDoc <+> equals <> hardline <> bodyDoc
  -- Do not show builtin definition or constructors
  _ -> mempty

prettyCtors :: [NamedDef Text] -> Text -> Doc ann
prettyCtors defs ctor = pretty ctor <> foldMap ((space <>) . pretty) types
  where
    types =
      fromMaybe (oops $ "cannot find the definition of " <> show ctor) $
        listToMaybe
          [ paraTypes
            | NamedDef {name, def = CtorDef {paraTypes}} <- defs,
              name == ctor
          ]

prettyBinder :: Text -> Maybe (Typ Text) -> Fresh (Doc ann)
prettyBinder binder Nothing = return $ pretty binder
prettyBinder binder (Just typ) = do
  typeDoc <- prettyExpr typ
  return $ pretty binder <+> colon <+> typeDoc

instance Pretty Attribute where
  pretty SectionAttr = "section"
  pretty RetractionAttr = "retraction"
  pretty SafeAttr = "safe"
  pretty LeakyAttr = "leaky"

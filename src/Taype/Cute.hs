{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Pretty printer.
module Taype.Cute
  ( module Prettyprinter,
    Doc,

    -- * Utilities
    indentLevel,
    hang,
    indent,
    sep1,
    sep1_,
    sepWith,
    printDoc,

    -- * Pretty printing infrastructure
    Cute (..),
    CuteM (..),
    runCuteM,
    contCuteM,
    HasPLevel (..),

    -- * Binder related utilities
    nameOrBinder,
    freshNameOrBinder,
    unbind1NameOrBinder,
    unbind2NamesOrBinders,
    unbindManyNamesOrBinders,
    withNamePrefix,

    -- * Common routines for pretty printing expressions
    cuteLamDoc_,
    cuteLamDoc,
    cuteLetDoc,
    cuteAppDoc,
    cuteApp_,
    cuteApp,
    cuteInfixDoc,
    cuteInfix,
    cuteIteDoc,
    cuteIte,
    cutePairDoc,
    cutePair,
    cuteCaseDoc,
    cuteCase,
    cuteAltDoc,
    cuteAltDocs,
    cutePCaseDoc,
    cutePCase_,
    cutePCase,
    cuteSubDoc,
    cuteSub,
    cuteSubAggDoc,
    cuteSubAgg,
  )
where

import Bound
import qualified Data.Text as T
import Prettyprinter hiding (Doc, hang, indent)
import qualified Prettyprinter as PP
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter.Util (putDocW)
import Taype.Binder
import Taype.Common
import Taype.Name
import Taype.Prelude
import Prelude hiding (group)

-- | Document type for all sorts of printing
type Doc = PP.Doc ()

----------------------------------------------------------------
-- Utilities

indentLevel :: Int
indentLevel = 2

hang :: Doc -> Doc
hang = PP.hang indentLevel

indent :: Doc -> Doc
indent = PP.indent indentLevel

sepWith :: Foldable t => Doc -> t Doc -> Doc
sepWith s = concatWith (\x y -> x <> s <> y)

sep1 :: Doc -> Doc
sep1 = group . (line <>)

sep1_ :: Text -> Doc -> Doc
sep1_ x = if T.length x <= indentLevel then (space <>) else sep1

printDoc :: MonadIO m => Options -> Doc -> m ()
printDoc Options {..} = liftIO . maybe putDoc putDocW optWidth

----------------------------------------------------------------
-- Pretty printing infrastructure

-- | A context for fresh name generation with options
newtype CuteM a = CuteM {unCuteM :: FreshT (Reader Options) a}
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadReader Options)

runCuteM :: Options -> CuteM a -> a
runCuteM opts (CuteM m) = runReader (runFreshT m) opts

contCuteM :: Options -> Int -> CuteM a -> a
contCuteM opts n (CuteM m) = runReader (contFreshT n m) opts

instance IsString a => IsString (CuteM a) where
  fromString = return . fromString

-- | Pretty printer class with fresh name generator and options
class Cute a where
  cute :: a -> CuteM Doc
  default cute :: Pretty a => a -> CuteM Doc
  cute = return <$> pretty

-- | Precedence level
class HasPLevel a where
  plevel :: a -> Int

----------------------------------------------------------------
-- Pretty printing instances

instance Cute Int

instance Cute Text

instance Cute Label

instance (Monad f, Cute (f Text)) => Cute (CaseAlt f Text) where
  cute CaseAlt {..} = do
    (xs, body) <- unbindManyNamesOrBinders binders bnd
    bodyDoc <- cute body
    return $ cuteAltDoc ctor xs bodyDoc

----------------------------------------------------------------
-- Binder related utilities

nameOrBinder :: Options -> Name -> Maybe Binder -> Text
nameOrBinder Options {..} x mb =
  let name = optNamePrefix <> show x
   in if optInternalNames then name else maybe name toText mb

freshNameOrBinder :: Maybe Binder -> CuteM Text
freshNameOrBinder binder = do
  opt <- ask
  -- Always generate new name even if we use binder.
  x <- fresh
  return $ nameOrBinder opt x binder

unbind1NameOrBinder ::
  Monad f => Maybe Binder -> Scope () f Text -> CuteM (Text, f Text)
unbind1NameOrBinder = unbindBy . freshNameOrBinder

unbind2NamesOrBinders ::
  Monad f =>
  (Maybe Binder, Maybe Binder) ->
  Scope Bool f Text ->
  CuteM ((Text, Text), f Text)
unbind2NamesOrBinders (binder1, binder2) =
  unbindBy $ (,) <$> freshNameOrBinder binder1 <*> freshNameOrBinder binder2

unbindManyNamesOrBinders ::
  Monad f => [Maybe Binder] -> Scope Int f Text -> CuteM ([Text], f Text)
unbindManyNamesOrBinders = unbindBy . mapM freshNameOrBinder

withNamePrefix :: MonadReader Options m => Text -> m a -> m a
withNamePrefix prefix =
  local $ \Options {..} -> Options {optNamePrefix = prefix, ..}

----------------------------------------------------------------
--  Common routines for pretty printing expressions

cuteLamDoc_ :: Doc -> Bool -> [Doc] -> Doc -> Doc
cuteLamDoc_ _ True [] bodyDoc = sep1 bodyDoc
cuteLamDoc_ _ False [] _ = oops "Lambda has no binder"
-- Quite hacky here
cuteLamDoc_ kw isRoot binderDocs bodyDoc =
  if isRoot
    then
      group
        ( flatAlt
            (hardline <> group mkBindersDoc <> hardline)
            (space <> mkBindersDoc)
        )
        <> column
          ( \k ->
              nesting
                (\i -> if k <= i then indent bodyDoc else sep1 bodyDoc)
          )
    else hang $ group mkBindersDoc <> sep1 bodyDoc
  where
    mkBindersDoc = kw <> align (vsep binderDocs) <+> "->"

cuteLamDoc :: Bool -> [Doc] -> Doc -> Doc
cuteLamDoc = cuteLamDoc_ backslash

cuteLetDoc :: [(Doc, Doc)] -> Doc -> Doc
cuteLetDoc [] bodyDoc = group $ align bodyDoc
cuteLetDoc bindingDocs bodyDoc =
  group $
    align $
      "let"
        <+> align (sepWith hardline (mkBindingDoc <$> bindingDocs)) <> line'
        <+> "in"
        <+> align bodyDoc
  where
    mkBindingDoc (binderDoc, rhsDoc) = hang $ binderDoc <+> equals <> sep1 rhsDoc

cuteAppDoc :: Doc -> [Doc] -> Doc
cuteAppDoc fnDoc docs =
  hang $ fnDoc <> group (foldMap (line <>) docs)

cuteApp_ :: (Cute e, HasPLevel e) => Doc -> [e] -> CuteM Doc
cuteApp_ fnDoc args = do
  docs <- mapM cuteSubAgg args
  return $ cuteAppDoc fnDoc docs

cuteApp :: (Cute e, HasPLevel e) => e -> [e] -> CuteM Doc
cuteApp fn es = do
  fnDoc <- cuteSubAgg fn
  cuteApp_ fnDoc es

cuteInfixDoc :: Text -> Doc -> Doc -> Doc
cuteInfixDoc infixT leftDoc rightDoc =
  hang $ leftDoc <> sep1 (pretty infixT <+> rightDoc)

cuteInfix :: (Cute e, HasPLevel e) => e -> Text -> e -> e -> CuteM Doc
cuteInfix super infixT left right = do
  leftDoc <- cuteSub super left
  rightDoc <- cuteSub super right
  return $ cuteInfixDoc infixT leftDoc rightDoc

cuteIteDoc :: Text -> Doc -> Doc -> Doc -> Doc
cuteIteDoc accent condDoc leftDoc rightDoc =
  group $
    pretty accent <> "if"
      <+> condDoc
        <> line
        <> hang ("then" <> sep1 leftDoc)
        <> line
        <> hang ("else" <> sep1 rightDoc)

cuteIte :: Cute e => Text -> e -> e -> e -> CuteM Doc
cuteIte accent cond left right = do
  condDoc <- cute cond
  leftDoc <- cute left
  rightDoc <- cute right
  return $ cuteIteDoc accent condDoc leftDoc rightDoc

cutePairDoc :: Text -> Doc -> Doc -> Doc
cutePairDoc accent leftDoc rightDoc =
  pretty accent <> parens (align (leftDoc <> comma <> sep1 rightDoc))

cutePair :: Cute e => Text -> e -> e -> CuteM Doc
cutePair accent left right = do
  leftDoc <- cute left
  rightDoc <- cute right
  return $ cutePairDoc accent leftDoc rightDoc

cuteCaseDoc :: Foldable t => Text -> Bool -> Doc -> t Doc -> Doc
cuteCaseDoc accent usePipe condDoc altDocs =
  align $
    pretty accent <> "case"
      <+> condDoc
      <+> "of"
        <> ( if usePipe
               then foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
               else foldMap (hardline <>) altDocs
           )
        <> hardline
        <> "end"

cuteCase ::
  (Traversable t, Monad f, Cute (f Text)) =>
  Text ->
  Bool ->
  f Text ->
  t (CaseAlt f Text) ->
  CuteM Doc
cuteCase accent usePipe cond alts = do
  condDoc <- cute cond
  altDocs <- mapM cute alts
  return $ cuteCaseDoc accent usePipe condDoc altDocs

cuteAltDoc :: Text -> [Text] -> Doc -> Doc
cuteAltDoc ctor xs bodyDoc =
  hang
    ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
        <+> "->" <> sep1 bodyDoc
    )

cuteAltDocs :: (Functor t) => t (Text, [Text], Doc) -> t Doc
cuteAltDocs = (go <$>)
  where
    go (ctor, xs, bodyDoc) = cuteAltDoc ctor xs bodyDoc

cutePCaseDoc :: Text -> Doc -> Text -> Text -> Doc -> Doc
cutePCaseDoc accent condDoc xl xr bodyDoc =
  cuteCaseDoc
    accent
    False
    condDoc
    [ hang $
        cutePairDoc accent (pretty xl) (pretty xr) <+> "->" <> sep1 bodyDoc
    ]

cutePCase_ :: Cute e => Text -> e -> Text -> Text -> e -> CuteM Doc
cutePCase_ accent cond xl xr body = do
  condDoc <- cute cond
  bodyDoc <- cute body
  return $
    cuteCaseDoc
      accent
      False
      condDoc
      [ hang $
          cutePairDoc accent (pretty xl) (pretty xr) <+> "->" <> sep1 bodyDoc
      ]

cutePCase ::
  (Monad f, Cute (f Text)) =>
  Text ->
  f Text ->
  Maybe Binder ->
  Maybe Binder ->
  Scope Bool f Text ->
  CuteM Doc
cutePCase accent cond lBinder rBinder bnd2 = do
  ((xl, xr), body) <- unbind2NamesOrBinders (lBinder, rBinder) bnd2
  cutePCase_ accent cond xl xr body

-- | Add parentheses to the expressions according to their precedence level.
cuteSubDoc :: HasPLevel e => e -> e -> Doc -> Doc
cuteSubDoc super sub doc = cuteSubIfDoc doc $ plevel super > plevel sub

cuteSub :: (Cute e, HasPLevel e) => e -> e -> CuteM Doc
cuteSub super sub = do
  doc <- cute sub
  return $ cuteSubDoc super sub doc

-- | Add parentheses to the expressions more aggressively.
cuteSubAggDoc :: HasPLevel e => e -> Doc -> Doc
cuteSubAggDoc sub doc = cuteSubIfDoc doc $ plevel sub == 0

cuteSubAgg :: (Cute e, HasPLevel e) => e -> CuteM Doc
cuteSubAgg sub = do
  doc <- cute sub
  return $ cuteSubAggDoc sub doc

cuteSubIfDoc :: Doc -> Bool -> Doc
cuteSubIfDoc doc True = doc
cuteSubIfDoc doc False = parens $ align doc

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
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
    hardline2,
    sep1,
    sep1_,
    sepWith,
    printDoc,
    printDocToFile,

    -- * Pretty printing infrastructure
    Cute (..),
    CuteM (..),
    runCuteM,
    contCuteM,
    HasPLevel (..),
    MonadCute (..),
    Disp (..),
    debugDoc,
    debug,

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
    cuteMatchDoc,
    cuteMatch,
    cuteAltDoc,
    cuteAltDocs,
    cutePMatchDoc,
    cutePMatch_,
    cutePMatch,
    cuteSubDoc,
    cuteSub,
    cuteSubAggDoc,
    cuteSubAgg,
  )
where

import Bound
import Data.Text qualified as T
import Prettyprinter hiding (Doc, hang, indent)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text (hPutDoc, putDoc)
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

hardline2 :: Doc
hardline2 = hardline <> hardline

sepWith :: Foldable t => Doc -> t Doc -> Doc
sepWith s = concatWith (\x y -> x <> s <> y)

sep1 :: Doc -> Doc
sep1 = group . (line <>)

sep1_ :: Text -> Doc -> Doc
sep1_ x = if T.length x <= indentLevel then (space <>) else sep1

printDoc :: MonadIO m => Options -> Doc -> m ()
printDoc Options {..} = liftIO . maybe putDoc putDocW optWidth

printDocToFile :: MonadIO m => FilePath -> Doc -> m ()
printDocToFile file doc =
  liftIO $ withFile file WriteMode (`hPutDoc` doc)

----------------------------------------------------------------
-- Pretty printing infrastructure

-- | A context for fresh name generation with options
newtype CuteM a = CuteM {unCuteM :: FreshT (Reader Options) a}
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadReader Options)

runCuteM :: Options -> CuteM a -> a
runCuteM opts (CuteM m) = runReader (runFreshT m) opts

contCuteM :: Options -> Int -> CuteM a -> a
contCuteM opts n (CuteM m) = runReader (contFreshT m n) opts

instance IsString a => IsString (CuteM a) where
  fromString = return . fromString

-- | Pretty printer class with fresh name generator and options
class Cute a where
  cute :: a -> CuteM Doc
  default cute :: Pretty a => a -> CuteM Doc
  cute = return . pretty

-- | Precedence level
class HasPLevel a where
  plevel :: a -> Int

-- | Similar to 'Cute', but it allows monads other than 'CuteM'.
--
-- Technically we can define 'Cute' in terms of 'MonadCute', but it introduces
-- heavier syntax for most cases.
class MonadCute m a where
  cutie :: a -> m Doc
  default cutie ::
    (MonadReader r m, HasOptions r, MonadFresh m, Cute a) => a -> m Doc
  cutie a = do
    options <- asks getOptions
    n <- getFresh
    return $ contCuteM options n $ cute a

-- | Display things.
--
-- Mostly used in error reporting and debugging.
data Disp m
  = -- | Display a document.
    DD Doc
  | -- | Display a document followed by a colon and possibly new line.
    DH Doc
  | -- | Display a 'MonadCute' instance.
    forall a. MonadCute m a => DC a
  | -- | Display a quoted 'MonadCute' instance.
    forall a. MonadCute m a => DQ a

----------------------------------------------------------------
-- Pretty printing instances

instance Cute Text

instance Cute Int where
  cute i =
    return $
      if i < 0
        then parens $ pretty i
        else pretty i

instance (Monad f, Cute (f Text)) => Cute (MatchAlt f Text) where
  cute MatchAlt {..} = do
    (xs, body) <- unbindManyNamesOrBinders binders bnd
    bodyDoc <- cute body
    return $ cuteAltDoc ctor xs bodyDoc

instance Monad m => MonadCute m (Disp m) where
  cutie (DD doc) = return doc
  cutie (DH doc) = return $ doc <> colon
  cutie (DC e) = cutie e
  cutie (DQ e) = dquotes <$> cutie e

instance Monad m => MonadCute m [Disp m] where
  cutie [] = return mempty
  cutie (d : ds) = do
    doc <- cutie d
    rest <- cutie ds
    return $
      case d of
        DH _ -> hang $ doc <> sep1 rest
        _ -> doc <> softline <> rest

instance Monad m => MonadCute m [[Disp m]] where
  cutie dss = do
    docs <- mapM cutie dss
    return $ sepWith hardline docs

debugDoc :: Monad m => [[Disp m]] -> m Doc
debugDoc dss = do
  doc <- cutie dss
  return $ "Debug" <> colon <> hardline <> doc <> hardline <> hardline

debug :: (MonadIO m, MonadReader r m, HasOptions r) => [[Disp m]] -> m ()
debug dss = do
  options <- asks getOptions
  doc <- debugDoc dss
  printDoc options doc

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
    mkBindersDoc = kw <> align (vsep binderDocs) <+> "=>"

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

cutePairDoc :: PairKind -> Doc -> Doc -> Doc
cutePairDoc pKind leftDoc rightDoc =
  pretty (accentOfPairKind pKind)
    <> parens (align (leftDoc <> comma <> sep1 rightDoc))

cutePair :: Cute e => PairKind -> e -> e -> CuteM Doc
cutePair pKind left right = do
  leftDoc <- cute left
  rightDoc <- cute right
  return $ cutePairDoc pKind leftDoc rightDoc

cuteMatchDoc :: Foldable t => Text -> Bool -> Doc -> t Doc -> Doc
cuteMatchDoc accent usePipe condDoc altDocs =
  align $
    pretty accent <> "match"
      <+> condDoc
      <+> "with"
        <> ( if usePipe
               then foldMap (\altDoc -> hardline <> pipe <+> altDoc) altDocs
               else foldMap (hardline <>) altDocs
           )
        <> hardline
        <> "end"

cuteMatch ::
  (Traversable t, Monad f, Cute (f Text)) =>
  Text ->
  Bool ->
  f Text ->
  t (MatchAlt f Text) ->
  CuteM Doc
cuteMatch accent usePipe cond alts = do
  condDoc <- cute cond
  altDocs <- mapM cute alts
  return $ cuteMatchDoc accent usePipe condDoc altDocs

cuteAltDoc :: Text -> [Text] -> Doc -> Doc
cuteAltDoc ctor xs bodyDoc =
  hang
    ( pretty ctor <> group (foldMap ((line <>) . pretty) xs)
        <+> "=>" <> sep1 bodyDoc
    )

cuteAltDocs :: (Functor t) => t (Text, [Text], Doc) -> t Doc
cuteAltDocs = (go <$>)
  where
    go (ctor, xs, bodyDoc) = cuteAltDoc ctor xs bodyDoc

cutePMatchDoc :: PairKind -> Doc -> Text -> Text -> Doc -> Doc
cutePMatchDoc pKind condDoc xl xr bodyDoc =
  cuteMatchDoc
    (accentOfPairKind pKind)
    False
    condDoc
    [ hang $
        cutePairDoc pKind (pretty xl) (pretty xr) <+> "=>" <> sep1 bodyDoc
    ]

cutePMatch_ :: Cute e => PairKind -> e -> Text -> Text -> e -> CuteM Doc
cutePMatch_ pKind cond xl xr body = do
  condDoc <- cute cond
  bodyDoc <- cute body
  return $ cutePMatchDoc pKind condDoc xl xr bodyDoc

cutePMatch ::
  (Monad f, Cute (f Text)) =>
  PairKind ->
  f Text ->
  Maybe Binder ->
  Maybe Binder ->
  Scope Bool f Text ->
  CuteM Doc
cutePMatch pKind cond lBinder rBinder bnd2 = do
  ((xl, xr), body) <- unbind2NamesOrBinders (lBinder, rBinder) bnd2
  cutePMatch_ pKind cond xl xr body

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

{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
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
    sepWith,
    printDoc,

    -- * Pretty printing infrastructure
    Cute,
    cute,
    CuteM (..),
    runCuteM,
    contCuteM,

    -- * Binder related utilities
    nameOrBinder,
    unbind1NameOrBinder,
    unbind2NamesOrBinders,
    unbindManyNamesOrBinders,
  )
where

import Bound
import Prettyprinter hiding (Doc, hang, indent)
import qualified Prettyprinter as PP
import Prettyprinter.Render.Text (putDoc)
import Prettyprinter.Util (putDocW)
import Taype.Binder
import Taype.Common
import Taype.Name
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

----------------------------------------------------------------
-- Pretty printing instances

instance Cute Int

instance Cute Text

instance Cute Label

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

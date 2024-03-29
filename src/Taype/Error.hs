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
-- Error reporting.
module Taype.Error
  ( Err (..),
    ErrClass (..),
    initPosState,
    getLocation,
    renderLocation,
    showLocation,
    showUnknownLocation,
    renderFancyLocation,
  )
where

import Data.Text qualified as T
import Prettyprinter.Render.Terminal qualified as PP
import Taype.Common
import Taype.Cute
import Text.Megaparsec

data Err = Err
  { errLoc :: Int,
    errMsg :: Doc,
    errCategory :: Text,
    errClass :: ErrClass
  }
  deriving stock (Show)

data ErrClass = WarningC | ErrorC
  deriving stock (Show)

initPosState :: FilePath -> Text -> PosState Text
initPosState file code =
  PosState
    { pstateInput = code,
      pstateOffset = 0,
      pstateSourcePos = initialPos file,
      pstateTabWidth = defaultTabWidth,
      pstateLinePrefix = ""
    }

getLocation :: FilePath -> Text -> Int -> (Int, Int, Maybe String)
getLocation file code offset = (li, col, maybeOffender)
  where
    (maybeOffender, st) = reachOffset offset $ initPosState file code
    pos = pstateSourcePos st
    li = unPos (sourceLine pos)
    col = unPos (sourceColumn pos)

renderLocation :: FilePath -> Text -> Int -> Text
renderLocation file code offset
  | offset < 0 = showUnknownLocation file
  | otherwise = showLocation file li col
  where
    (li, col, _) = getLocation file code offset

showLocation :: FilePath -> Int -> Int -> Text
showLocation file li col = toText file <> ":" <> show li <> ":" <> show col

showUnknownLocation :: FilePath -> Text
showUnknownLocation file = toText file <> ":" <> "(unknown location)"

renderFancyLocation :: FilePath -> Text -> Int -> Text
renderFancyLocation file code offset
  | offset < 0 = showUnknownLocation file <> ":"
  | otherwise =
      showLocation file li col
        <> ":\n"
        <> maybe "" showOffender maybeOffender
  where
    (li, col, maybeOffender) = getLocation file code offset
    showOffender offender =
      lpadding
        <> bar
        <> "\n"
        <> lineTxt
        <> bar
        <> toText offender
        <> "\n"
        <> lpadding
        <> bar
        <> pointerPadding
        <> "^"
      where
        lineTxt = show li
        lpadding = T.replicate (T.length lineTxt) " "
        pointerPadding = T.replicate (col - 1) " "
        bar = " | "

----------------------------------------------------------------
-- Pretty printer

instance Cute Err where
  cute Err {..} = do
    Options {optFile = file, optCode = code} <- ask
    return $
      annotate (PP.color clr) $
        "!!!! "
          <> pretty errCategory
          <> " !!!!"
          </> pretty (renderFancyLocation file code errLoc)
          <//> errMsg <> hardline2
    where
      clr = case errClass of
        WarningC -> PP.Yellow
        ErrorC -> PP.Red

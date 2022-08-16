{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Taype.Error
  ( oops,
    LocatedError (..),
    renderLocation,
    renderFancyLocation,
    renderError,
  )
where

import qualified Data.Text as T
import Text.Megaparsec

oops :: Text -> a
oops msg = error $ "Oops! This should not happen:\n" <> msg

data LocatedError = LocatedError
  { errLoc :: Int,
    errMsg :: Text,
    errCategory :: Text
  }
  deriving stock (Eq, Show)

getLocation :: FilePath -> Text -> Int -> (Int, Int, Maybe String)
getLocation file code offset = (line, col, maybeOffender)
  where
    initState =
      PosState
        { pstateInput = code,
          pstateOffset = 0,
          pstateSourcePos = initialPos file,
          pstateTabWidth = defaultTabWidth,
          pstateLinePrefix = ""
        }
    (maybeOffender, st) = reachOffset offset initState
    pos = pstateSourcePos st
    line = unPos (sourceLine pos)
    col = unPos (sourceColumn pos)

renderLocation :: FilePath -> Text -> Int -> Text
renderLocation file code offset
  | offset < 0 = showUnknownLocation file
  | otherwise = showLocation file line col
  where
    (line, col, _) = getLocation file code offset

showLocation :: FilePath -> Int -> Int -> Text
showLocation file line col = toText file <> ":" <> show line <> ":" <> show col

showUnknownLocation :: FilePath -> Text
showUnknownLocation file = toText file <> ":" <> "(unknown location)"

renderFancyLocation :: FilePath -> Text -> Int -> Text
renderFancyLocation file code offset
  | offset < 0 = showUnknownLocation file <> ":\n"
  | otherwise =
    showLocation file line col <> ":\n"
      <> maybe "" showOffender maybeOffender
      <> "\n"
  where
    (line, col, maybeOffender) = getLocation file code offset
    showOffender offender =
      lpadding
        <> sep
        <> "\n"
        <> lineTxt
        <> sep
        <> toText offender
        <> "\n"
        <> lpadding
        <> sep
        <> pointerPadding
        <> "^"
      where
        lineTxt = show line
        lpadding = T.replicate (T.length lineTxt) " "
        pointerPadding = T.replicate (col - 1) " "
        sep = " | "

renderError :: FilePath -> Text -> LocatedError -> Text
renderError file code LocatedError {..} =
  "!!" <> errCategory <> "!!\n"
    <> renderFancyLocation file code errLoc
    <> errMsg
    <> "\n"

{-# LANGUAGE OverloadedStrings #-}

module Taype.Error (oops) where

oops :: Text -> a
oops msg = error $ "Oops! This should not happen:\n" <> msg

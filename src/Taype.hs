{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Top-level functions.
module Taype
  ( test,
  )
where

import Prettyprinter
import Prettyprinter.Render.Text
import Taype.Syntax

test :: IO ()
test = do
  let term = App (lam "x" (V "x")) [V "y"] :: Exp Text
  print term
  putDoc (pretty term)
  putStrLn ""
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
  let term = App Nothing (lam "x" Nothing Nothing (V "x")) [V "y"] :: Expr Text
  print term
  putDoc (pretty term)
  putStrLn ""
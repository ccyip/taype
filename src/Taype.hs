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

-- import Prettyprinter
-- import Prettyprinter.Render.Text

import Taype.Lexer
import Taype.Syntax
import Text.Megaparsec.Error (errorBundlePretty)

test :: FilePath -> IO ()
test file = do
  content <- readFileBS file
  case lex file $ decodeUtf8 content of
    Left bundle -> putStr (errorBundlePretty bundle)
    Right tokens -> print tokens
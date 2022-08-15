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

import Taype.Parser

test :: FilePath -> IO ()
test file = do
  content <- readFileBS file
  parse file $ decodeUtf8 content

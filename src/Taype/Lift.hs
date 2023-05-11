-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Lifting algorithm that derives oblivious programs from the public ones.
module Taype.Lift (liftDefs) where

import Taype.Common
import Taype.Environment
import Taype.Error
import Taype.Name
import Taype.Syntax

liftDefs :: Options -> GCtx Name -> Defs Name -> ExceptT Err IO (Defs Name)
liftDefs _ _ = return

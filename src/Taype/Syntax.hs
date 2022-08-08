{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Syntax of the surface and core taype language.
module Taype.Syntax
  ( -- * Syntax
    Exp (..),

    -- * Smart constructors
    lam,
  )
where

import Bound
import Control.Monad
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes
import Prettyprinter
import Taype.Fresh
import qualified Text.Show

-- | Taype expression, including the surface and the core syntax
data Exp a
  = V {name :: a}
  | Lam {body :: Scope () Exp a}
  | App {fn :: Exp a, args :: Exp a}
  deriving stock (Functor, Foldable, Traversable)

instance Applicative Exp where
  pure = V
  (<*>) = ap

instance Monad Exp where
  V {..} >>= f = f name
  Lam {..} >>= f = Lam {body = body >>>= f}
  App {..} >>= f = App {fn = fn >>= f, args = args >>= f}

deriveEq1 ''Exp
deriveShow1 ''Exp

instance Eq a => Eq (Exp a) where (==) = eq1

instance Show a => Show (Exp a) where showsPrec = showsPrec1

-- | A smart constructor for 'Lam'
lam :: Eq a => a -> Exp a -> Exp a
lam v b = Lam {body = abstract1 v b}

-- | Pretty printer for Taype expressions
instance Pretty (Exp Text) where
  pretty = runFresh . prettyExp

prettyExp :: Exp Text -> Fresh (Doc ann)
prettyExp V {..} = return $ pretty name
prettyExp Lam {..} = do
  x <- freshName
  return $ "\\" <+> pretty x <+> "->" <+> pretty (instantiate1 (V x) body)
prettyExp App {..} = return $ pretty fn <+> pretty args
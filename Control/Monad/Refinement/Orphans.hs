{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Control.Monad.Refinement.Orphans where

import Numeric.Algebra
import Prelude hiding ((+), (*), negate)
import qualified Prelude as P


instance Additive Rational where (+) = (P.+)
instance Multiplicative Rational where (*) = (P.*)
instance Abelian Rational
instance Semiring Rational


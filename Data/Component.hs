{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Data.Component where

import Data.String
import Data.Text (Text)
import Refinement
import Prelude hiding (product, (+), (*), minimum, maximum, negate)


data Component = Component Text
  | Symbol Int
  | Equals Component Rational
  | LessThan Component Rational
  | GreaterThan Component Rational
  | Neg Component
  | Or Component Component
  | And Component Component
  | Implies Component Component
  | Always | Never
  deriving (Eq, Ord, Show)

instance IsString Component where fromString = Component . fromString

instance Additive Component where (+) = Or
instance Multiplicative Component where (*) = And

instance Monoidal Component where zero = Never
instance   Unital Component where  one = Always

instance Semigroup Component where (<>) = (*)
instance Monoid Component where
  mappend = (<>)
  mempty = zero

instance Group Component where
  negate Never = Always
  negate Always = Never
  negate (Neg c) = c
  negate c = Neg c

instance Propositional Component where
  conjunction (And a b) = Just (a, b)
  conjunction _ = Nothing

  disjunction (Or a b) = Just (a, b)
  disjunction _ = Nothing

  a ==> b = Implies a b
  implication (Implies a b) = Just (a, b)
  implication _ = Nothing

  negation (Neg c) = Just c
  negation _ = Nothing

instance Quantifiable Component where
  equation (Equals a n) = Just (a, n)
  equation _ = Nothing

  minimum (GreaterThan a n) = Just (a, n)
  minimum _ = Nothing

  maximum (LessThan a n) = Just (a, n)
  maximum _ = Nothing

  a >. n  = GreaterThan a n
  a <. n  = LessThan a n

  a =. n  = Equals a n


instance Letter Component where
  letter c | Just (a,_) <- conjunction c = letter a
  letter c | Just (a,_) <- disjunction c = letter a
  letter c | Just (a,_) <- implication c = letter a
  letter c | Just (a,_) <- equation c = letter a
  letter c | Just (a,_) <- minimum c = letter a
  letter c | Just (a,_) <- maximum c = letter a
  letter c | Just a <- negation c = letter a
  letter c = c


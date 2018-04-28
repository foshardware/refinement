{-# LANGUAGE ConstrainedClassMethods, FlexibleContexts #-}

module Control.Monad.Refinement.Class where

import Control.Applicative
import Prelude hiding (minimum, maximum, negate, (+), (*))

infixr 5 |.
infixr 6 &.
infix 8 <., >., =., >=., <=.
infixr 1 ==>

infixl 6 +
infixl 7 *

-- | A Product that is unrefined and a strategy to refine it form a Monoid
class Product a where
  product :: Monoidal a => a
  product = zero

  refine :: Additive a => a -> a -> a
  refine = (+)

  perturbate :: Multiplicative a => a -> a -> a
  perturbate = (*)

class Monoidal a where
  zero :: a

class Unital a where
  one :: a

class Multiplicative a where
  (*) :: a -> a -> a

class Additive a where
  (+) :: a -> a -> a

class Group a where
  negate :: a -> a


-- | Logical operators in propositional algebra
(&.) :: Multiplicative c => c -> c -> c
(&.) = (*)

(|.) :: Additive c => c -> c -> c
(|.) = (+)

neg :: Group c => c -> c
neg = negate

class Propositional c where
  conjunction :: c -> Maybe (c, c)
  disjunction :: c -> Maybe (c, c)
  negation :: c -> Maybe c
  negation _ = Nothing
  (==>) :: c -> c -> c
  (==>) = const
  implication :: c -> Maybe (c, c)
  implication _ = Nothing

class Quantifiable c where
  equation :: c -> Maybe (c, Rational)
  equation _ = Nothing
  minimum  :: c -> Maybe (c, Rational)
  minimum _ = Nothing
  maximum  :: c -> Maybe (c, Rational)
  maximum _ = Nothing
  (=.) :: c -> Rational -> c
  (>.) :: c -> Rational -> c
  (>.) = (=.)
  (<.) :: c -> Rational -> c
  (<.) = (=.)

(<=.) :: (Additive c, Quantifiable c) => c -> Rational -> c
a <=. n = a <. n + a =. n
(>=.) :: (Additive c, Quantifiable c) => c -> Rational -> c
a >=. n = a >. n + a =. n

equivalent :: (Eq c, Group c, Monoidal c, Unital c, Quantifiable c, Propositional c) => c -> c -> Bool
equivalent x y = sufficient x y && sufficient y x

-- | sufficient (e <== x)
-- DNF
sufficient :: (Eq c, Group c, Monoidal c, Unital c, Quantifiable c, Propositional c) => c -> c -> Bool

sufficient _ x | x == zero = True
sufficient e _ | e == one = True

sufficient e x
  | Just (a, n) <- minimum =<< negation e
  , Just (b, m) <- minimum =<< negation x
  = a == b && n >= m
sufficient e x
  | Just (a, n) <- maximum e
  , Just (b, m) <- minimum =<< negation x
  = a == b && n > m
sufficient e x
  | Just (a, n) <- maximum =<< negation e
  , Just (b, m) <- maximum =<< negation x
  = a == b && m >= n
sufficient e x
  | Just (a, n) <- minimum e
  , Just (b, m) <- maximum =<< negation x
  = a == b && m > n

sufficient e x
  | Just (a, n) <- minimum =<< negation e
  , Just (b, m) <- equation x
  = a == b && n >= m
sufficient e x
  | Just (a, n) <- maximum =<< negation e
  , Just (b, m) <- equation x
  = a == b && m >= n

sufficient e x
  | Just _ <- disjunction x
  = and [sufficient e y | y <- disjunctions x]
sufficient e x
  | Just _ <- disjunction e
  = or [sufficient f x | f <- disjunctions e]

sufficient e x
  | Just _ <- conjunction e
  = and [sufficient f x | f <- conjunctions e]
sufficient e x
  | Just _ <- conjunction x
  = or [sufficient e y | y <- conjunctions x]

sufficient e x
  | Just a <- negation e
  , Just b <- negation x
  = a == b
sufficient e x
  | Just a <- negation e
  = not $ sufficient a x
sufficient e x
  | Just a <- negation x
  = e /= a

sufficient e x
  | Just (a, n) <- minimum e
  , Just (b, m) <- equation x
  = a == b && m > n
sufficient e x
  | Just (a, n) <- maximum e
  , Just (b, m) <- equation x
  = a == b && n > m
sufficient e x
  | Just (a, n) <- minimum e
  , Just (b, m) <- minimum x
  = a == b && m >= n
sufficient e x
  | Just (a, n) <- maximum e
  , Just (b, m) <- maximum x
  = a == b && n >= m

sufficient e x = e == x


replace
  :: (Eq c, Additive c, Multiplicative c, Group c, Propositional c, Quantifiable c)
  => c -> c -> c -> c
replace x y c | Just (a, b) <- conjunction c = replace x y a * replace x y b
replace x y c | Just (a, b) <- disjunction c = replace x y a + replace x y b
replace x y c | Just (a, b) <- implication c = replace x y a ==> replace x y b
replace x y c | Just (a, n) <- equation c = replace x y a =. n
replace x y c | Just (a, n) <- minimum c = replace x y a >. n
replace x y c | Just (a, n) <- maximum c = replace x y a <. n
replace x y c | Just a <- negation c = negate $ replace x y a
replace x y c | x == c = y
replace _ _ c = c

-- Extract the primitive letter from a proposition
class Letter c where letter :: c -> c

conjunctions :: Propositional c => c -> [c]
conjunctions u | Just (a, b) <- conjunction u = conjunctions a ++ conjunctions b
conjunctions u = [u]

disjunctions :: Propositional c => c -> [c]
disjunctions u | Just (a, b) <- disjunction u = disjunctions a ++ disjunctions b
disjunctions u = [u]

prettyProposition :: (Show c, Eq c, Monoidal c, Propositional c, Quantifiable c) => c -> String
prettyProposition c | Just (a, b) <- disjunction c, a == zero = prettyProposition b
prettyProposition c | Just (a, b) <- disjunction c, b == zero = prettyProposition a
prettyProposition c | Just (a, b) <- disjunction c = prettyProposition a ++" | "++ prettyProposition b
prettyProposition c
  | Just (a, b) <- conjunction c
  , Just _ <- disjunction a <* disjunction b
  = "("++ prettyProposition a ++") & ("++ prettyProposition b ++ ")"
prettyProposition c
  | Just (a, b) <- conjunction c
  , Just _ <- disjunction a
  = "("++ prettyProposition a ++") & "++ prettyProposition b
prettyProposition c
  | Just (a, b) <- conjunction c
  , Just _ <- disjunction b
  = prettyProposition a ++" & ("++ prettyProposition b ++")"
prettyProposition c | Just (a, b) <- conjunction c = prettyProposition a ++" & "++ prettyProposition b
prettyProposition c
  | Just a <- negation c
  , Just _ <- disjunction a <|> conjunction a <|> implication a
  = "~("++ prettyProposition a ++")"
prettyProposition c | Just a <- negation c = "~"++ prettyProposition a
prettyProposition c | Just (a, b) <- implication c = show a ++" ==> "++ show b
prettyProposition c | Just (a, n) <- equation c = show a ++" = "++ show n
prettyProposition c | Just (a, n) <- minimum c = show a ++" > "++ show n
prettyProposition c | Just (a, n) <- maximum c = show a ++" < "++ show n
prettyProposition c = show c


{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module XC70 where

import Refinement
import Control.Monad.Refinement.CNF
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Data.Foldable (forM_)
import Prelude hiding (product, (+), (*))
import qualified Prelude as Num


xc70 :: Refinement Car Component ()
xc70 = do
  unique product { available = NA } [Kinetic, Momentum, Summum]
  -- high performance sound
  rule product { fixedPrice = 700, available = Optional } $ O 832 &. Kinetic
  rule product { available = NA } $ O 832 &. Summum
  -- infotainment center
  rule product { fixedPrice = 1250, available = Optional } $ Kinetic &. O 935
  rule product { fixedPrice = 550, available = Optional } $ Momentum &. O 935
  -- premium infotainment
  rule product { available = Optional } $ O 934
  rule product { fixedPrice = 2400 } $ Kinetic &. neg BusinessPro &. O 934
  rule product { fixedPrice = 1700 } $ Momentum &. neg BusinessPro &. O 934
  rule product { fixedPrice = 1150 } $ Summum &. O 934
  rule product { fixedPrice = 1150 } $ (Kinetic |. Momentum) &. BusinessPro &. O 934
  -- only one entertainment center
  unique product { available = NA } [O 832, O 934, O 935]
  -- digital instruments
  rule product { available = Optional, fixedPrice = 420 } $ Kinetic &. O 584
  -- radio
  rule product { available = Optional, fixedPrice = 430 } $ O 501 &. (O 832 |. O 934 |. O 935)
  rule product { available = NA } $ O 501 &. neg (O 832 |. O 934 |. O 935)
  rule product { available = Optional, fixedPrice = 90 } $ O 683 &. (O 832 |. O 934 |. O 935)
  rule product { available = NA } $ O 683 &. neg (O 832 |. O 934 |. O 935)
  -- only one radio
  unique product { available = NA } [O 501, O 683]
  -- suggest 501
  rule product { suggest = O 683 `replace` O 501 } $ O 683

printRuleSet :: Refinement Car Component () -> Component -> IO ()
printRuleSet car c = forM_ (evalRefinement $ car >> ruleSet c) $
  \(r, p) -> putStrLn $ show r ++": "++ show p


data Car = Car
  { fixedPrice :: Int
  , available :: Availability
  , suggest :: Component -> Component
  }

instance Show Car where
  show c = "{ fixedPrice: "++ show (fixedPrice c) ++", available: "++ show (available c) ++" }"

instance Product Car

instance Additive Car where
  a + b = Car
    { fixedPrice = fixedPrice a Num.+ fixedPrice b
    , available = available a <> available b
    , suggest = suggest a . suggest b
    }

instance Multiplicative Car where (*) = const

instance Monoidal Car where
  zero = Car
    { fixedPrice = 0
    , available = mempty
    , suggest = id
    }

instance Semigroup Car where (<>) = (+)
instance Monoid Car where
  mempty = zero
  mappend = (<>)

data Availability = NA | Series | Optional deriving Show

instance Semigroup Availability where
  Series <> b = b
  b <> Series = b
  NA <> _ = NA
  _ <> NA = NA
  _ <> _ = Optional

instance Monoid Availability where
  mempty = Series
  mappend = (<>)

data Component = Null | One
  | Kinetic | Momentum | Summum
  | BusinessPro
  | O Int
  | Equals Component Rational
  | Neg Component
  | Or Component Component
  | And Component Component
  deriving (Eq, Ord, Show)

instance Additive Component where (+) = Or
instance Multiplicative Component where (*) = And

instance Monoidal Component where zero = Null
instance Unital Component where one = One 

instance Semigroup Component where (<>) = (*)
instance Monoid Component where
  mappend = (<>)
  mempty = zero

instance Group Component where
  negate (Neg c) = c
  negate c = Neg c

instance Propositional Component where
  conjunction (And a b) = Just (a, b)
  conjunction _ = Nothing

  disjunction (Or a b) = Just (a, b)
  disjunction _ = Nothing

  negation (Neg c) = Just c
  negation _ = Nothing

instance Quantifiable Component where
  equation (Equals a n) = Just (a, n)
  equation _ = Nothing
  c =. r = Equals c r

instance Letter Component where
  letter c | Just (a,_) <- conjunction c = letter a
  letter c | Just (a,_) <- disjunction c = letter a
  letter c | Just (a,_) <- equation c = letter a
  letter c | Just a <- negation c = letter a
  letter c = c


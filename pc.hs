{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}

module PC where

import Refinement
import Data.Foldable (forM_)
import Data.Component
import Data.Range
import Prelude hiding (product, (+), (*), minimum, maximum, negate)


pc :: Refinement PC Component ()
pc = do
  rule product { price = least 1200 } "Gfx 1"
  rule product { available = False }  "Gfx 2"
  rule product { price = most 1100 } $ neg $ "CPUCores" >. 2 &. "CPUCores" <. 5
--  rule product { available = False } . negate . foldr1 (|.) $ map ("CPUCores" =.) [2,4,8,16,32]

data PC = PC
  { price :: Range Int
  , time :: Range Int
  , available :: Bool
  , suggest :: Component -> Component
  }

instance Show PC where
  show p | available p = "{price: "++ show (price p) ++", time: "++ show (time p) ++"}"
  show p = "N/A"

instance Product PC

instance Additive PC where
  a + b = PC
    { price = price a + price b
    , time = time a + time b
    , available = available a && available b
    , suggest = suggest a . suggest b
    }

instance Multiplicative PC where
  a * b = PC
    { price = price a * price b
    , time = time a * time b
    , available = available a || available b
    , suggest = undefined
    }

instance Monoidal PC where
  zero = PC
    { price = zero
    , time = zero
    , available = True
    , suggest = id
    }

instance Semigroup PC where (<>) = (+)
instance Monoid PC where
  mempty = zero
  mappend = (<>)


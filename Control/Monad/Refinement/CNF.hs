
module Control.Monad.Refinement.CNF
  ( toCNF
  , toSetsCNF
  ) where

import Control.Monad.Refinement.Class
import Control.Monad.Refinement.DNF
import Data.Set as Set
import Prelude as List hiding ((+), (*), negate)


toCNF, t :: (Eq c, Additive c, Multiplicative c, Group c, Propositional c) => c -> c
toCNF = toDNF

t = undefined


toSetsCNF :: (Ord c, Group c, Monoidal c, Unital c, Propositional c) => c -> Set (Set c)
toSetsCNF d = fromList
  [ x
  | r <- fromList . disjunctions <$> conjunctions d
  , let s = r \\ intersection r (Set.map negate r)
  , notMember one s
  , x <- [s | size s == 1]
      ++ [delete zero s | size s > 1]
  ]



module Control.Monad.Refinement.DNF
  ( toDNF, reduce
  , fromSetsDNF, toSetsDNF
  , resolve, eliminate
  , primeTermTable, rows, columns
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Refinement.Class
import Control.Monad.ST
import Data.Bits
import Data.Foldable (for_)
import Data.Maybe
import qualified Data.Vector as Vector 
import Data.Vector (length, thaw, unsafeFreeze, unsafeIndex, ifoldl')
import Data.Vector.Mutable (unsafeRead, unsafeWrite)
import Data.Set as Set hiding (foldl')
import Data.STRef
import Prelude as List hiding ((+), (*), negate, length)
import qualified Prelude as Num 

import Data.BitMatrix
import Data.BitVector


toDNF = t
toDNF, t :: (Eq c, Additive c, Multiplicative c, Group c, Propositional c) => c -> c

t c | Just (a, b) <- implication =<< negation c = t $ a * negate b
t c | Just (a, b) <- implication c = t (negate a) + t b

-- DeMorgan
t c | Just (a, b) <- conjunction =<< negation c = t (negate a) + t (negate b)
t c | Just (a, b) <- disjunction =<< negation c = t $ negate a * negate b

-- Absorbtion
t c
  | Just (a, b) <- conjunction c
  , Just (d, e) <- disjunction a
  , t b `elem` [t d, t e]
  = t b
t c
  | Just (a, b) <- conjunction c
  , Just (d, e) <- disjunction b
  , t a `elem` [t d, t e]
  = t a
t c
  | Just (a, b) <- disjunction c
  , Just (d, e) <- conjunction a
  , t b `elem` [t d, t e]
  = t b
t c
  | Just (a, b) <- disjunction c
  , Just (d, e) <- conjunction b
  , t a `elem` [t d, t e]
  = t a

-- Distributive
t c | Just (a, b) <- conjunction c, Just (d, e) <- disjunction a = t (b * d) + t (b * e)
t c | Just (a, b) <- conjunction c, Just (d, e) <- disjunction b = t (a * d) + t (a * e)

-- Idempotent
t c | Just (a, b) <- conjunction c <|> disjunction c, t a == t b = t a

-- Traversal
t c | Just (a, b) <- conjunction c, c == t a * t b = c
t c | Just (a, b) <- conjunction c = t $ t a * t b
t c | Just (a, b) <- disjunction c = t a + t b

-- Break Condition
t c = c 


-- | Note on complexity: Size of minterms considered as constant
--
reduce
  :: (Ord c, Group c, Monoidal c, Unital c, Additive c, Multiplicative c, Propositional c)
  => c -> c
reduce c = fromSetsDNF $ eliminate (toSetsDNF c) $ resolve (toSetsDNF c) mempty

-- | O(ms*log(ms))
toSetsDNF :: (Ord c, Group c, Monoidal c, Unital c, Propositional c) => c -> Set (Set c)
toSetsDNF d = fromList
  [ x
  | r <- fromList . conjunctions <$> disjunctions d
  , let s = r \\ intersection r (Set.map negate r)
  , notMember zero s
  , x <- [s | size s == 1]
      ++ [delete one s | size s > 1]
  ]

-- | O(ms)
fromSetsDNF
  :: (Ord c, Group c, Monoidal c, Unital c, Additive c, Multiplicative c)
  => Set (Set c) -> c
fromSetsDNF s | s == singleton mempty || s == singleton (singleton one) = one
fromSetsDNF s | not $ List.null xs = foldr1 (+) $ foldr1 (*) <$> xs
  where xs = [x | x <- elems $ singleton one `delete` s, size x > 0]
fromSetsDNF _ = zero

resolve :: (Ord c, Group c) => Set (Set c) -> Set (Set c) -> Set (Set c)
resolve x xs | size x == 1, size xs == 0 = x
resolve x xs
  | rs <- absorb r $ xs `union` absorb x x
  , size r > 0
  , r `union` rs /= xs `union` absorb x x
  = resolve r rs
  where
  r = fromList
    [ delete e a `union` delete (negate e) b
    | a <- elems $ absorb x x
    , b <- elems $ xs `union` absorb x x
    , let c = a `intersection` Set.map negate b
    , let e = elemAt 0 c
    , size c == 1
    ]
resolve x xs = xs `union` absorb x x

-- | O(n*m)
absorb :: Ord c => Set (Set c) -> Set (Set c) -> Set (Set c)
absorb s = Set.filter $ \a -> not $ any (`isProperSubsetOf` a) s

eliminate :: Ord c => Set (Set c) -> Set (Set c) -> Set (Set c)
eliminate  _ rs | size rs <= 1 = rs
eliminate ms rs
  | size ms <= 0x100000 Num.* wordSize
  , size rs <= 0x100000 Num.* wordSize
  = fromDistinctAscList [r | (i, r) <- [0..] `zip` toAscList rs, unsafeIndex v i /= zeroBits]
  where BitMatrix _ v = columns $ primeTermTable ms rs
eliminate ms rs | size ms > (Num.*) 0x100000 wordSize || size ms > size rs = rs
eliminate ms  _ = ms

-- | O(ms*rs)
primeTermTable :: Ord c => Set (Set c) -> Set (Set c) -> BitMatrix
primeTermTable ms rs
  | mv <- Vector.fromList $ toAscList ms
  , rv <- Vector.fromList $ toAscList rs
  = BitMatrix (size ms) . flip fmap rv
  $ \r -> ifoldl' (\n j m -> if isSubsetOf r m then setBit n j else n) zeroBits mv 

-- | O(rs^2)
rows :: BitMatrix -> BitMatrix
rows u
  | (n, v) <- runST $ strike u $ \vi vj -> vj == vj .&. vi
  , n > 0
  = columns v
rows u = u

-- | O(ms^2 + rs*ms)
columns :: BitMatrix -> BitMatrix
columns u
  | (n, v) <- runST $ strike (transpose u) $ \vi vj -> vi == vi .&. vj
  , n > 0
  = rows $ transpose v
columns u = rows u

-- | Row elimination by criteria; Rows containing only zeroes are `striked out`
--
strike :: BitMatrix -> (BitVector -> BitVector -> Bool) -> ST s (Int, BitMatrix)
strike (BitMatrix c u) criteria = do
  changes <- newSTRef 0
  m <- thaw u
  for_ [0..(length u - 1)] $ \i -> do
    vi <- unsafeRead m i
    for_ [j | j <- [0..(length u - 1)], vi /= zeroBits, i /= j] $ \j -> do
      vj <- unsafeRead m j
      when (vj /= zeroBits && criteria vi vj) $ do
        modifySTRef' changes succ
        unsafeWrite m j zeroBits
  n <- readSTRef changes
  v <- unsafeFreeze m
  pure (n, BitMatrix c v)

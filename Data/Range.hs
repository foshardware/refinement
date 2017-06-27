{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module Data.Range where

import Data.Pointed
import Data.Semigroup
import Numeric.Algebra hiding ((>))
import Prelude hiding ((+), (*), (-))


data Range a = Range !a !a | Ranges [Range a] | Nil
  deriving Eq

instance Functor Range where
  fmap f (Range  a b) = Range (f a) (f b)
  fmap f (Ranges  rs) = Ranges [f <$> r | r <- rs]
  fmap _ Nil = Nil

instance Pointed Range where point a = Range a a

instance (Group a, Ord a) => Additive (Range a) where
  Range i0 i1 + Range j0 j1 = normalize $ Range (max i0 j0) (min i1 j1)
  i@(Range  _ _) + Ranges rs = normalize $ Ranges [i + r | r <- rs]
  r@(Ranges _) + i@(Range _ _) = i + r
  Ranges rs + Ranges ss = normalize $ Ranges [r + s | r <- rs, s <- ss]
  _ + _ = Nil

instance (Group a, Ord a) => Multiplicative (Range a) where
  i@(Range _ _)  * j@(Range _ _) = normalize $ Ranges [i, j]
  i@(Range  _ _) * Ranges rs = normalize . Ranges $ i : rs
  r@(Ranges _) * i@(Range _ _) = i * r
  Ranges rs * Ranges ss = normalize . Ranges $ rs <> ss
  Nil * x = x
  x * Nil = x

instance (Group a, Ord a, RightModule Natural a) => RightModule Natural (Range a) where
  Range a b *. n = Range (a *. n) (b *. n)
  Ranges rs *. n = Ranges $ fmap (*. n) rs
  Nil *. _ = Nil
instance (Group a, Ord a, LeftModule Natural a) => LeftModule Natural (Range a) where
  n .* Range a b = Range (n .* a) (n .* b)
  n .* Ranges rs = Ranges $ fmap (n .*) rs
  _ .* Nil = Nil

instance (Group a, Ord a, Bounded a) => Monoidal (Range a) where
  zero = Range minBound maxBound

instance (Group a, Ord a) => Semigroup (Range a) where (<>) = (+)
instance (Group a, Ord a, Bounded a) => Monoid (Range a) where
  mappend = (<>)
  mempty = zero

instance (Ord a, Group a) => Ord (Range a) where
  Range i0 i1 <= Range j0 j1 | i0 == j0 = i1 - i0 <= j1 - j0
  Range i0  _ <= Range j0  _ = i0 <= j0
  Range _ _ <= Ranges _ = True
  Ranges _ <= Range _ _ = False
  Ranges r <= Ranges s = length r <= length s
  Nil <= _ = True
  _   <= _ = False

valid :: Ord a => Range a -> Bool
valid (Range a b) = a <= b
valid (Ranges rs) = or $ valid <$> rs
valid Nil = False

normalize :: (Ord a, Group a) => Range a -> Range a
normalize Nil = Nil
normalize r@(Range _ _) | valid r = r
normalize   (Range _ _) = Nil
normalize  (Ranges [ ]) = Nil
normalize  (Ranges [r]) = normalize r 
normalize  (Ranges  rs) = unwind . filter valid . normalizeList $ normalize <$> rs
  where
    unwind [ ] = Nil
    unwind [x] = x
    unwind  xs = Ranges xs

-- | A smart mergesort that joins and drops elements appropriately
-- effectively normalizing a list of `Ranges`
normalizeList :: (Ord a, Group a) => [Range a] -> [Range a]
normalizeList = mergeAll . sequences
  where
    sequences (r@(Range i0 i1) : s@(Range j0 j1) : xs)
      | not (valid r) || r `isSubsetOf` s = descending s [] xs
      | not (valid s) || s `isSubsetOf` r = descending r [] xs
      | i0 <= j0 && i1 >= j0 = descending (Range i0 j1) [] xs
      | j0 <= i0 && j1 >= i0 = descending (Range j0 i1) [] xs
      | r > s = descending s [r] xs
      | otherwise = ascending s (r:) xs
    sequences xs = [xs]

    descending r@(Range i0 i1) rs (s@(Range j0 j1) : ss)
      | not (valid r) || r `isSubsetOf` s = descending s rs ss
      | not (valid s) || s `isSubsetOf` r = descending r rs ss
      | i0 <= j0 && i1 >= j0 = descending (Range i0 j1) rs ss
      | j0 <= i0 && j1 >= i0 = descending (Range j0 i1) rs ss
      | r > s = descending s (r:rs) ss
    descending a as bs = (a:as) : sequences bs

    ascending r@(Range i0 i1) rs (s@(Range j0 j1) : ss)
      | not (valid r) || r `isSubsetOf` s = ascending Nil rs $ s : ss
      | not (valid s) || s `isSubsetOf` r = ascending r rs ss
      | i0 <= j0 && i1 >= j0 = ascending (Range i0 j1) rs ss
      | j0 <= i0 && j1 >= i0 = ascending (Range j0 i1) rs ss
      | r <= s = ascending s (\ys -> rs (r:ys)) ss
    ascending r rs ss = rs [r] : sequences ss

    mergeAll [x] = x
    mergeAll  xs = mergeAll $ mergePairs xs

    mergePairs (a:b:xs) = merge a b : mergePairs xs
    mergePairs       xs = xs

    merge rs@(r@(Range i0 i1) : rs') ss@(s@(Range j0 j1) : ss')
      | not (valid r) || r `isSubsetOf` s = merge rs' ss
      | not (valid s) || s `isSubsetOf` r = merge rs ss'
      | i0 <= j0 && i1 >= j0 = merge rs' $ Range i0 j1 : ss'
      | j0 <= i0 && j1 >= i0 = merge rs' $ Range j0 i1 : ss'
      | r > s = s : merge rs ss'
      | otherwise = r : merge rs' ss
    merge [] ss = ss
    merge rs [] = rs
    merge rs ss = rs <> ss

isSubsetOf :: Ord a => Range a -> Range a -> Bool
isSubsetOf (Range i0 i1) (Range j0 j1) = i0 >= j0 && i1 <= j1
isSubsetOf Nil Nil = True
isSubsetOf Nil   _ = True
isSubsetOf   _ Nil = False
isSubsetOf   _   _ = error "isSubsetOf not implemented for higher-order ranges"


instance (Bounded a, Eq a, Ord a, Group a, Show a) => Show (Range a) where
  show Nil = "invalid"
  show (Range a b) | Range a b == zero = "open"
  show (Range a b) | b == maxBound = show a ++"..open"
  show (Range a b) | a == minBound = "open.."++ show b
  show (Range a b) | a == b = show a
  show (Range a b) = show a ++".."++ show b
  show (Ranges rs) = show rs

inRange :: Ord a => Range a -> a -> Bool
inRange (Range a b) c = c >= a && c <= b
inRange (Ranges xs) c = or [inRange x c | x <- xs]
inRange _ _ = False

range :: a -> a -> Range a
range = Range

ranges :: [Range a] -> Range a
ranges = Ranges

notInRange :: Bounded a => a -> a -> Range a
notInRange a b = Ranges [Range minBound a, Range b maxBound]

at :: (a -> b) -> a -> b
at f = f

least :: Bounded a => a -> Range a
least x = Range x maxBound

most :: Bounded a => a -> Range a
most x = Range minBound x


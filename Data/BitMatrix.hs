{-# LANGUAGE OverloadedStrings #-}

module Data.BitMatrix where

import Data.Bits
import Data.Foldable
import Data.Monoid
import Data.Text.Lazy (unpack)
import Data.Text.Lazy.Builder
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Prelude hiding ((!!))

(!) :: U.Vector Word -> Int -> Word
(!) = U.unsafeIndex

(!!) :: V.Vector a -> Int -> a
(!!) = V.unsafeIndex

-- |    m0,m1,m2,..
--   r0 0x00000001
--   r1 0x00000002
--   ..
-- 
--  m0 <=> LSB
--
data BitMatrix = BitMatrix !Int (V.Vector BitVector)

instance Eq BitMatrix where
  BitMatrix m u == BitMatrix n v = m == n && u == v

-- | Inexpensive: right shifts, row operators, bitwise ands, word aligned parameters
--
instance Bits BitMatrix where
  bitSizeMaybe (BitMatrix c v) = Just $ c * V.length v
  isSigned _ = False

  BitMatrix c u .&. BitMatrix d v
    = BitMatrix (min c d) $ uncurry (.&.) <$> V.zip u v

  BitMatrix c u .|. BitMatrix d v
    | V.length u > V.length v
    = BitMatrix (max c d) . flip V.imap u
    $ \i ui -> if i >= V.length v then ui else ui .|. v!!i
  BitMatrix c u .|. BitMatrix d v
    | V.length u < V.length v
    = BitMatrix (max c d) . flip V.imap v
    $ \i vi -> if i >= V.length u then vi else u!!i .|. vi
  BitMatrix c u .|. BitMatrix d v
    = BitMatrix (max c d) $ uncurry (.|.) <$> V.zip u v
  
  BitMatrix c u `xor` BitMatrix d v
    | V.length u > V.length v
    = BitMatrix (max c d) . flip V.imap u
    $ \i ui -> if i >= V.length v then ui else ui `xor` v!!i
  BitMatrix c u `xor` BitMatrix d v
    | V.length u < V.length v
    = BitMatrix (max c d) . flip V.imap v
    $ \i vi -> if i >= V.length u then vi else u!!i `xor` vi
  BitMatrix c u `xor` BitMatrix d v
    = BitMatrix (max c d) $ uncurry xor <$> V.zip u v

  complement (BitMatrix c v)
    = BitMatrix c $ complementN c <$> v

  popCount (BitMatrix c v)
    = sum $ popCountN c <$> v

  testBit (BitMatrix c v) n
    = n <= c * V.length v && testBit (v !! div n c) (mod n c)

  bit n
    = BitMatrix wordSize . V.generate (divWord n + 1)
    $ \i -> if i /= divWord n then zeroBits else bit $ modWord n

  zeroBits = BitMatrix 0 V.empty

  clearBit (BitMatrix c v) n
    | n > c * V.length v
    = BitMatrix c v
  clearBit (BitMatrix c v) n
    | (m, k) <- divMod n c
    = BitMatrix c . flip V.imap v
    $ \i vi -> if i /= m then vi else vi .&. complementN k (bit k)

  shift (BitMatrix c v) 0 = BitMatrix c v 
  shift (BitMatrix c v) n = BitMatrix (c+n) $ flip shift n <$> v
  
  rotate (BitMatrix c v) 0 = BitMatrix c v 
  rotate (BitMatrix c v) n = BitMatrix c $ flip rotate n <$> v

rowShift :: BitMatrix -> Int -> BitMatrix
rowShift (BitMatrix c v) n | n > 0 = BitMatrix c $ V.replicate n zeroBits V.++ v
rowShift (BitMatrix c v) n | n < 0 = BitMatrix c $ V.drop (-n) v
rowShift bm _ = bm

rowShiftR :: BitMatrix -> Int -> BitMatrix
rowShiftR x n = rowShift x (-n)

rowShiftL :: BitMatrix -> Int -> BitMatrix
rowShiftL x n = rowShift x n

rowRotate :: BitMatrix -> Int -> BitMatrix
rowRotate (BitMatrix c v) n
  | n > 0
  , (v0, v1) <- V.splitAt (n `mod` V.length v) v
  = BitMatrix c $ v1 V.++ v0
rowRotate (BitMatrix c v) n
  | n < 0 
  , (v0, v1) <- V.splitAt (V.length v + (-n) `mod` V.length v) v
  = BitMatrix c $ v1 V.++ v0
rowRotate bm _ = bm

rowRotateR :: BitMatrix -> Int -> BitMatrix
rowRotateR x n = rowRotate x (-n)

rowRotateL :: BitMatrix -> Int -> BitMatrix
rowRotateL x n = rowRotate x n

rowSlice :: Int -> Int -> BitMatrix -> BitMatrix
rowSlice x n (BitMatrix c v) = BitMatrix c $ V.slice x n v

columnSlice :: Int -> Int -> BitMatrix -> BitMatrix
columnSlice _ 0 _ = BitMatrix 0 mempty
columnSlice 0 n (BitMatrix c v) | n >= c = BitMatrix c v
columnSlice x n (BitMatrix _ v) = BitMatrix n $ slice x n <$> v

-- | O(ms*rs)
transpose :: BitMatrix -> BitMatrix
transpose (BitMatrix c v)
  = BitMatrix (V.length v) . V.generate c
  $ \i -> V.ifoldl' (\n j a -> if testBit a i then setBit n j else n) zeroBits v


newtype BitVector = BitVector (U.Vector Word)

wordSize :: Int
wordSize = finiteBitSize (maxBound :: Word)

modWord :: Int -> Int
modWord n | wordSize == 64 = n .&. 63
modWord n | wordSize == 32 = n .&. 31
modWord _ = undefined

divWord :: Int -> Int
divWord n | wordSize == 64 = shiftR n 6
divWord n | wordSize == 32 = shiftR n 5
divWord _ = undefined 

instance Eq BitVector where
  BitVector a == BitVector b
    | (a0, a1) <- U.splitAt (U.length b) a
    , (b0, b1) <- U.splitAt (U.length a) b
    = a0 == b0 && U.all (== 0) a1 && U.all (== 0) b1 

instance Bits BitVector where
  bitSizeMaybe (BitVector v) = Just $ U.length v * wordSize
  isSigned _ = False

  BitVector a .&. BitVector b
    = BitVector $ uncurry (.&.) `U.map` U.zip a b

  BitVector a .|. BitVector b
    | U.length a > U.length b
    = BitVector . flip U.imap a
    $ \i ai -> if i >= U.length b then ai else ai .|. b!i
  BitVector a .|. BitVector b
    | U.length a < U.length b
    = BitVector . flip U.imap b
    $ \i bi -> if i >= U.length a then bi else a!i .|. bi
  BitVector a .|. BitVector b
    = BitVector $ uncurry (.|.) `U.map` U.zip a b

  BitVector a `xor` BitVector b
    | U.length a > U.length b
    = BitVector . flip U.imap a
    $ \i ai -> if i >= U.length b then ai else ai `xor` b!i
  BitVector a `xor` BitVector b
    | U.length a < U.length b
    = BitVector . flip U.imap b
    $ \i bi -> if i >= U.length a then bi else a!i `xor` bi
  BitVector a `xor` BitVector b
    = BitVector $ uncurry xor `U.map` U.zip a b

  complement (BitVector v) = BitVector $ U.map complement v

  popCount (BitVector v) = U.foldl' (\n a -> n + popCount a) 0 v

  testBit (BitVector v) n = U.length v > divWord n && testBit (v ! divWord n) (modWord n)

  bit n
    = BitVector . U.generate (divWord n + 1)
    $ \i -> if i /= divWord n then 0 else bit $ modWord n

  zeroBits = BitVector U.empty

  clearBit b n = b .&. complementN n (bit n)

  shiftL (BitVector v) n
    | modWord n == 0
    = BitVector $ U.replicate (divWord n) 0 U.++ v
  shiftL (BitVector v) n
    | m <- modWord n, k <- divWord n
    = BitVector . U.generate (U.length v + k)
    $ \i -> case compare 0 (i-k) of
      GT -> 0
      LT -> shiftR (v!(i-k-1)) (wordSize-m) .|. shiftL (v!(i-k)) m
      EQ -> shiftL (v!0) m
  shiftR (BitVector v) n
    | modWord n == 0
    = BitVector $ U.drop (divWord n) v
  shiftR (BitVector v) n
    | m <- modWord n, k <- divWord n
    = BitVector . U.generate (U.length v - k)
    $ \i -> case compare (i+k) (U.length v - 1) of
      LT -> shiftR (v!(i+k)) (wordSize-m) .|. shiftL (v!(i+k+1)) (wordSize-m)
      EQ -> shiftR (v!(i+k)) m
      GT -> undefined

  rotateL (BitVector v) n
    | modWord n == 0
    , (v0, v1) <- U.splitAt (divWord n) v
    = BitVector $ v1 U.++ v0
  rotateL (BitVector v) n
    | m <- modWord n, k <- divWord n
    = BitVector . U.generate (U.length v)
    $ \i -> v!(mod (i+k) (U.length v)) .|. v!(mod (i+k) (U.length v))
  rotateR (BitVector v) n
    | modWord n == 0
    , (v0, v1) <- U.splitAt (U.length v - divWord n) v
    = BitVector $ v1 U.++ v0

complementN :: Int -> BitVector -> BitVector
complementN 0 bv = bv
complementN n (BitVector v)
  = BitVector $ U.map complement v U.++ U.replicate (divWord (n+wordSize-1) - U.length v) maxBound

popCountN :: Int -> BitVector -> Int 
popCountN n _ | n <= 0 = 0
popCountN n v | modWord n == 0 = popCount v
popCountN n (BitVector v)
  = popCount (v!(divWord n) .&. (shiftL 1 (modWord n) - 1))
  + popCount (BitVector $ U.take (divWord n) v)

slice :: Int -> Int -> BitVector -> BitVector
slice x n (BitVector v)
  | modWord n == 0
  , modWord x == 0
  = BitVector . U.take (divWord n)
  $ U.drop (divWord x) v 
slice x n (BitVector v)
  | (x+n) > wordSize * U.length v
  = slice x (wordSize * U.length v - x) (BitVector v)
slice x n (BitVector v)
  | modWord x == 0
  = BitVector . U.snoc (U.unsafeSlice (divWord x) (divWord n) v)
  $ v!(divWord x + divWord n) .&. (shiftL 1 (modWord n) - 1)
slice x n bv
  = slice 0 (x+n) bv `shiftR` x


instance Show BitMatrix where
  show = unpack . toLazyText . bitMatrixBuilder

bitMatrixBuilder :: BitMatrix -> Builder
bitMatrixBuilder (BitMatrix c v) | elem 0 [c, V.length v] = "( )" 
bitMatrixBuilder (BitMatrix c v)
  = foldr (\e s -> "( " <> foldr (check e) mempty [0..(c-1)] <> " )\n" <> s) mempty v
  where
  check e j m | testBit e j = "×" <> m
  check _ _ m = singleton ' ' <> m

instance Show BitVector where
  show bv@(BitVector v)
    = [ if testBit bv n then '1' else '0'
      | n <- [0..(wordSize * U.length v - 1)]
      ]


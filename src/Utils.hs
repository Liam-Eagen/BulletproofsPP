{-# LANGUAGE BangPatterns, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Utils where

import Data.Bits (testBit)
import Data.VectorSpace
import Data.Foldable (foldl')

import Data.Field.Galois hiding ((*^), (/))
import Data.Curve
import qualified Data.Curve as Curve

data Range = R { minRange :: Integer, maxRange :: Integer }

data Pair a = T2 { t20 :: a, t21 :: a }
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

instance Applicative Pair where
  pure x = T2 x x
  (T2 f0 f1) <*> (T2 x0 x1) = T2 (f0 x0) (f1 x1)

data Triple a = T3 { t30 :: a, t31 :: a, t32 :: a}
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

instance Applicative Triple where
  pure x = T3 x x x
  (T3 f0 f1 f2) <*> (T3 x0 x1 x2) = T3 (f0 x0) (f1 x1) (f2 x2)

idAp :: (a -> b) -> a -> (a, b)
idAp f x = (x, f x)

appIf :: (a -> a) -> Bool -> a -> a
appIf f True x = f x
appIf _ False x = x

zipPair :: (a -> b -> c) -> (a, a) -> (b, b) -> (c, c)
zipPair f (a, b) (c, d) = (f a c, f b d)

sumPair :: Num a => [(a, a)] -> (a, a)
sumPair = foldl' (zipPair (+)) (0,0)

zipQuad :: (a -> b -> c) -> (a,a,a,a) -> (b,b,b,b) -> (c,c,c,c)
zipQuad f (x0,x1,x2,x3) (y0,y1,y2,y3) = (f x0 y0, f x1 y1, f x2 y2, f x3 y3)

sumQuad :: Num a => [(a,a,a,a)] -> (a,a,a,a)
sumQuad = foldl' (zipQuad (+)) (0,0,0,0)

-- replicate defaults to [] on negative n - length xs
padLeft :: Int -> a -> [a] -> [a]
padLeft n z xs = (replicate (n - length xs) z) ++ xs

padRight :: Int -> a -> [a] -> [a]
padRight n x xs = take n $ xs ++ repeat x

-- TODO use something faster (only called during setup)
-- returns 0 on negative base, returns floor(log_b(n))
integerLog :: Integer -> Integer -> Integer
integerLog b n = if n < b then 0 else 1 + integerLog b (n `quot` b)

baseDigits :: Integral a => Integer -> Integer -> [a] -> [a]
baseDigits _ 0 xs = xs
baseDigits b n xs = let (q,r) = n `quotRem` b in baseDigits b q (fromInteger r:xs)

-- Test bit for integral values
testBit' :: Integral a => a -> Int -> Bool
testBit' x n = testBit (toInteger x) n

applyN' :: Int -> (Int -> a -> a) -> a -> a
applyN' !n f !x = if n == 0 then x else applyN' (n-1) f (f n x)

--bimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
--bimap f g (x, y) = (f x, g y)

dup :: (a -> b) -> (a, a) -> (b, b)
dup f (x, y) = (f x, f y)

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (_:[]) = []
pairs (x:y:zs) = (x,y) : pairs zs

unPairs :: [(a,a)] -> [a]
unPairs [] = []
unPairs ((x,y):zs) = x : y : unPairs zs

-- NOTE produces infinite list
powers :: Num a => a -> [a]
powers a = iterate (* a) 1

powers' :: Num a => a -> [a]
powers' = tail . powers

powers'' :: Num a => a -> a -> [a]
powers'' b a = iterate (* a) b

-- Splits a scalar into halves and returns a function applying shamir with these
-- halves to curve points and the halves, as well as the inverse of the
-- denominator. Utility function
splitScalar :: (Integral s, Fractional s) => s -> (s, s, s, Integer)
splitScalar e = (fromInteger (a*s), b', 1/b', s)
  where
    (a, b) = rationalRep e
    s = signum b
    b' = fromInteger $ abs b
    bInv' = 1/b'

-- Computes rational representation n = a/b mod p for a,b ~ p^(1/2) using the
-- extended euclidean algorithm. Can be made more efficient as well as made to
-- use LLL for n = (a + b * w) / (c + d * w) mod p, a,b,c,d ~ p^1/4
rationalRep :: (Fractional p, Integral p) => p -> (Integer, Integer)
rationalRep n = head $ dropWhile (\(a, b) -> a > abs b) $ egcd (p, 0) (toInteger n, 1)
  where
    p = 1 + toInteger (-n/n)      -- TODO very hacky, maybe just add PrimeField constraints
    -- Assumes initial a > b and both positive
    egcd a b = b : egcd b c
      where
        q = fst a `quot` fst b
        c = (fst a - q * fst b, snd a - q * snd b)

-- Multiply vector by one of {0, 1, -1}
signumV :: VectorSpace v => Integer -> v -> v
signumV 0 _ = zeroV
signumV 1 v = v
signumV (-1) v = negateV v

-- Conditionally add the first argument to the second
addIfV :: VectorSpace v => Bool -> v -> v -> v
addIfV c a b = if c then a ^+^ b else b

---------------------------
-- VectorSpace instances --

-- Allows treating F_p and E(F_q) as vector spaces over F_p
newtype WrapV f = WV { unWV :: f }
  deriving (Eq, Num)

class AdditiveGroup a => FastDouble a where
  dbl' :: a -> a

instance (Num f, Field f) => AdditiveGroup (WrapV f) where
  zeroV = 0
  a ^+^ b = a + b
  negateV a = negate a

instance (Num f, Field f) => VectorSpace (WrapV f) where
  type Scalar (WrapV f) = f
  s *^ (WV p) = WV $ s * p

instance (Num f, Field f) => FastDouble (WrapV f) where
  dbl' x = x + x

instance (Curve f c e q p) => AdditiveGroup (Point f c e q p) where
  zeroV = Curve.id
  p ^+^ q = p `add` q
  negateV p = Curve.inv p

instance (Curve f c e q p) => VectorSpace (Point f c e q p) where
  type Scalar (Point f c e q p) = p
  s *^ p = p `mul` s

-- NOTE vector addition is not defined for the point with itself. Must use this
instance (Curve f c e q p) => FastDouble (Point f c e q p) where
  dbl' = dbl

---------------------------------------
-- Class for zipping two collections --

class (Functor f) => Zip f where
  -- Basically just a second applicative instance
  liftZip :: a -> f a
  
  zip' :: f a -> f b -> f (a, b)
  zip' = zipWith' (,)

  zipWith' :: (a -> b -> c) -> f a -> f b -> f c
  zipWith' f xs ys = fmap (uncurry f) $ zip' xs ys

  -- Given a default value, append and zipWith' if unequal lengths
  zipWithDef' :: (a -> b -> c) -> b -> f a -> f b -> f c

  zipWithDef'' :: (a -> b -> c) -> a -> b -> f a -> f b -> f c

instance Zip [] where
  liftZip a = repeat a

  zip' = zip
  zipWith' = zipWith
  
  zipWithDef' _ _  []     _      = []       -- TODO do we want?
  zipWithDef' f y0 (x:xs) (y:ys) = f x y  : zipWithDef' f y0 xs ys
  zipWithDef' f y0 xs     []     = map (flip f y0) xs

  -- TODO migrate to this function instead of zipWithDef'
  zipWithDef'' _ _  _  []     []     = []
  zipWithDef'' f x0 y0 (x:xs) (y:ys) = f x y  : zipWithDef'' f x0 y0 xs ys
  zipWithDef'' f x0 _  []     ys     = map (f x0) ys
  zipWithDef'' f _  y0 xs     []     = map (flip f y0) xs

newtype ZipVector f a = ZV { getZV :: f a }
  deriving (Eq, Show, Functor, Foldable, Traversable, Zip)

instance (Zip f, Num a) => AdditiveGroup (ZipVector f a) where
  zeroV = liftZip 0
  (^+^) = zipWith' (+)
  (^-^) = zipWith' (-)
  negateV = fmap negate


dotZip :: (Foldable f, Zip f, Num a) => f a -> f a -> a
dotZip xs ys = sum $ zipWith' (*) xs ys

weightedDotZip :: (Foldable f, Zip f, Num a) => [a] -> f a -> f a -> a
weightedDotZip ws xs ys = fst $ foldl' step (0, ws) $ zipWith' (*) xs ys
  where
    step (n, w : ws) xy = (n + w * xy, ws)
    step (n, []) _ = (n, [])

linCombZipDef :: (Zip f, Num a) => a -> a -> f a -> f a -> f a
linCombZipDef a b xs ys = zipWithDef' (\x y -> a * x + b * y) 0 xs ys


-- Given a sorted list removes equal elements
deDup :: Eq a => [a] -> [a]
deDup [] = []
deDup (x:xs) = x : deDup (dropWhile (== x) xs)

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = uncurry (:) $ chunks n <$> splitAt n xs

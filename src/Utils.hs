module Utils where

import Data.Proxy
import Data.Bits (testBit)
import Data.VectorSpace
import Data.Foldable (foldl')
import Control.Monad (replicateM)
import qualified Data.Set as S (toList, fromList)

import Data.Bits
import Data.Binary
import Data.Binary.Get (runGet)
import Data.Binary.Put (runPut)
import qualified Data.ByteString.Lazy as BS

import Data.Field.Galois hiding ((*^), (/), recip, Binary(..))
import Data.Curve
import Data.Curve.Weierstrass
import qualified Data.Curve as Curve

import qualified Data.Vector as V
import Data.Field.BatchInverse

import Data.Field.Eis
import Data.Curve.CM

proxy' :: a -> Proxy a
proxy' _ = Proxy

sameType :: a -> a -> a
sameType = const

data Range = R { minRange :: Integer, maxRange :: Integer }
  deriving (Eq, Show, Ord)

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

pairToList (x, y) = [x, y]

bizipPair f g (a, b) (c, d) = (f a c, g b d)

zipPair :: (a -> b -> c) -> (a, a) -> (b, b) -> (c, c)
zipPair f (a, b) (c, d) = (f a c, f b d)

sumPair :: Num a => [(a, a)] -> (a, a)
sumPair = foldl' (zipPair (+)) (0,0)

zipQuad :: (a -> b -> c) -> (a,a,a,a) -> (b,b,b,b) -> (c,c,c,c)
zipQuad f (x0,x1,x2,x3) (y0,y1,y2,y3) = (f x0 y0, f x1 y1, f x2 y2, f x3 y3)

mapQuad f (a, b, c, d) = (f a, f b, f c, f d)

sumQuad :: Num a => [(a,a,a,a)] -> (a,a,a,a)
sumQuad = foldl' (zipQuad (+)) (0,0,0,0)

-- replicate defaults to [] on negative n - length xs
padLeft :: Int -> a -> [a] -> [a]
padLeft n z xs = (replicate (n - length xs) z) ++ xs

padRight :: Int -> a -> [a] -> [a]
padRight n x xs = take n $ xs ++ repeat x

-- returns 0 on negative base, returns floor(log_b(n))
integerLog :: Integer -> Integer -> Integer
integerLog b n = if n < b then 0 else 1 + integerLog b (n `quot` b)

baseDigits :: Integral a => Integer -> Integer -> [a] -> [a]
baseDigits _ 0 xs = xs
baseDigits b n xs = let (q,r) = n `quotRem` b in baseDigits b q (fromInteger r:xs)

dup :: (a -> b) -> (a, a) -> (b, b)
dup f (x, y) = (f x, f y)

-- Extract adjacent pairs, or dovetail two lists
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

negIfV True x = negateV x
negIfV False x = x

-- Allows treating F_p as vector spaces over F_p
newtype WrapV f = WV { unWV :: f }
  deriving (Eq, Num)

instance (Num f, Field f) => AdditiveGroup (WrapV f) where
  zeroV = 0
  {-# INLINE zeroV #-}

  a ^+^ b = a + b
  {-# INLINE (^+^) #-}

  negateV a = negate a
  {-# INLINE negateV #-}

instance (Num f, Field f) => VectorSpace (WrapV f) where
  type Scalar (WrapV f) = f
  s *^ (WV p) = WV $ s * p
  {-# INLINE (*^) #-}


-----------------------
-- Unit Num Instance --

-- This is used by the range proof verifier to avoid duplicating code
instance Num () where
  _ + _ = ()
  _ - _ = ()
  _ * _ = ()
  negate _ = ()
  abs _ = ()
  signum _ = ()
  fromInteger _ = ()

instance Real () where
  toRational _ = toRational 0

-- Not sure if should error here, since it might be more useful to just 
-- return unit
instance Integral () where
  toInteger _ = 0
  quotRem _ _ = ((), ())

instance Fractional () where
  fromRational _ = ()
  recip _ = ()

---------------------------------------
-- Class for zipping two collections --

class (Functor f) => Zip f where
  zip' :: f a -> f b -> f (a, b)
  zip' = zipWith' (,)

  zipWith' :: (a -> b -> c) -> f a -> f b -> f c
  zipWith' f xs ys = fmap (uncurry f) $ zip' xs ys

  -- Useful if one of the data types doesn't have a default
  zipWithDef' :: (a -> b -> c) -> b -> f a -> f b -> f c

  -- Pad lists to equal length with default values
  zipWithDef'' :: (a -> b -> c) -> a -> b -> f a -> f b -> f c

instance Zip [] where
  zip' = zip
  zipWith' = zipWith

  zipWithDef' _ _  []      _      = []
  zipWithDef' f y0 (!x:xs) (!y:ys) = f x y  : zipWithDef' f y0 xs ys
  zipWithDef' f y0 xs      []     = map (flip f y0) xs

  zipWithDef'' _ _   _   []     []     = []
  zipWithDef'' f !x0 !y0 (x:xs) (y:ys) = f x y  : zipWithDef'' f x0 y0 xs ys
  zipWithDef'' f !x0 _   []     ys     = map (f x0) ys
  zipWithDef'' f _   !y0 xs     []     = map (flip f y0) xs

instance Zip V.Vector where
  zip' = V.zip
  zipWith' = V.zipWith

  zipWithDef' f y0 xs ys = V.generate n go
    where
      n = V.length xs
      go i = f (xs V.! i) (ys `getDef` y0)
        where getDef as a0 = maybe a0 Prelude.id $ as V.!? i

  zipWithDef'' f x0 y0 xs ys = V.generate n go
    where
      n = max (V.length xs) (V.length ys)
      go i = f (xs `getDef` x0) (ys `getDef` y0)
        where 
          getDef :: V.Vector a -> a -> a
          getDef as a0 = maybe a0 Prelude.id $ as V.!? i

dotZip :: (Foldable f, Zip f, Num a) => f a -> f a -> a
dotZip xs ys = sum $ zipWith' (*) xs ys

weightedDotZip :: (Foldable f, Zip f, Num a) => [a] -> f a -> f a -> a
weightedDotZip ws xs ys = fst $ foldl' step (0, ws) $ zipWith' (*) xs ys
  where
    step (n, w : ws) xy = (n + w * xy, ws)
    step (n, []) _ = (n, [])

-- Given a sorted list removes equal elements
deDup :: (Ord a, Eq a) => [a] -> [a]
deDup = S.toList . S.fromList

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = uncurry (:) $ chunks n <$> splitAt n xs

-- Sum lists
sums :: Num a => [[a]] -> [a]
sums = foldr (zipWith (+)) (repeat 0)


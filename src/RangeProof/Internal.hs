{-# LANGUAGE TypeFamilies, DeriveFunctor, BangPatterns #-}

module RangeProof.Internal where

import Data.AdditiveGroup
import Data.VectorSpace

import Utils
import Commitment
import NormLinearProof

-- Implements common functionality for both Binary and Reciprocal range proofs
-- including the VectorSpace instance for the RPWitness type.

-- TODO unify with commitment types somehow? Rename
data RPWitness s = RPW { getBlindingRPW :: s, getScalarRPW :: s, getLinearRPW :: [s], getNormRPW :: [s] }
  deriving (Eq, Show, Functor)

instance Zip RPWitness where
  --liftZip z = RPW z z (repeat z) (repeat z)
  liftZip z = RPW z z [] []
  zipWith' f (RPW b0 s0 l0 n0) (RPW b1 s1 l1 n1) = RPW (f b0 b1) (f s0 s1) (zipWith' f l0 l1) (zipWith' f n0 n1)
  zipWithDef'' f z0 z1 (RPW b0 s0 l0 n0) (RPW b1 s1 l1 n1) = RPW (f b0 b1) (f s0 s1) (zip' l0 l1) (zip' n0 n1)
    where zip' = zipWithDef'' f z0 z1

  -- TODO don't use
  zipWithDef' f = zipWithDef'' f (error "called with one default")

instance Num s => AdditiveGroup (RPWitness s) where
  zeroV = liftZip 0
  (^+^) = zipWithDef'' (+) 0 0
  (^-^) = zipWithDef'' (-) 0 0
  negateV = fmap negate

instance Num s => VectorSpace (RPWitness s) where
  type Scalar (RPWitness s) = s
  s *^ v = fmap (s *) v

commitRPW :: CanCommit v s => s -> v -> s -> v -> [s] -> [v] -> [s] -> [v] -> v
commitRPW bl h sc g ln hs xs gs = shamirWith body zeroV
  where body (*:) (+:) z = dotWith (*:) (+:) ln hs $ dotWith (*:) (+:) xs gs $ (bl *: h) +: (sc *: g) +: z

blindedRPW :: CanCommitM v s m => s -> [s] -> [s] -> m (RPWitness s)
blindedRPW sc ln xs = do
  bl <- random
  return $ RPW bl sc ln xs

normRPW :: CanCommitM v s m => s -> [s] -> m (RPWitness s)
--normRPW sc xs = blindedRPW sc (repeat 0) xs
normRPW sc xs = blindedRPW sc [] xs

linearRPW :: CanCommitM v s m => s -> [s] -> m (RPWitness s)
--linearRPW sc ln = blindedRPW sc ln (repeat 0)
linearRPW sc ln = blindedRPW sc ln []

scalarRPW :: CanCommitM v s m => PedersenScalar v s -> m (RPWitness s)
--scalarRPW ps = return $ RPW (scalarCP $ blindingPS ps) (scalarCP $ scalarPS ps) (repeat 0) (repeat 0)
scalarRPW ps = return $ RPW (scalarCP $ blindingPS ps) (scalarCP $ scalarPS ps) [] []

scalarPairRPW :: CanCommitM v s m => PedersenScalarPair v s -> m (RPWitness s)
--scalarPairRPW (PSP b (sc0, sc1)) = return $ RPW (scalarCP b) (scalarCP sc0) (scalarCP sc1 : repeat 0) (repeat 0)
scalarPairRPW (PSP b (sc0, sc1)) = return $ RPW (scalarCP b) (scalarCP sc0) [scalarCP sc1] []

makeBlindingTerms :: Integral a => [a] -> [a] -> [a] -> (a, a)
makeBlindingTerms ws wit bls = (2 * mult wit bls, mult bls bls)
  where mult as bs = weightedDotZip ws as bs

------------------------------------------------------------
-- Functions used by both Reciprocal and ReciprocalShared --

-- Uses montgomery batch inversion to invert a list of number using three
-- multiplications per number and one reciprocal for the whole list. Maps the
-- inverse of zero to zero.
batchInverse :: (Fractional a, Eq a) => [a] -> [a]
batchInverse vs = rec0 1 vs []
  where
    rec0 !n [] ss = rec1 (1/n,n) ss []
    rec0 !n (0:xs) ss = rec0 n xs $ (0, n) : ss
    rec0 !n (x:xs) ss = rec0 (x*n) xs $ (x,n) : ss
    
    rec1 _ [] ys = ys
    rec1 (!y, m) ((0, n):ss) ys = rec1 (y, n) ss $ 0 : ys
    rec1 (!y, _) ((x, n):ss) ys = rec1 (x * y, n) ss $ y * n : ys

-- Could be faster
counts :: Eq a => [a] -> [a] -> [Integer]
counts xs ys = [toInteger $ length $ filter (== x) ys | x <- xs]

digitsMults :: Bool -> Integer -> [Integer] -> Integer -> ([Integer], [Integer], [Integer])
digitsMults True b bs n = let (ds, ms, ns) = digitsMults False b (tail bs) n' in (dn : ds, 0 : ms, 0 : ns)
  where (dn, n') = if n > head bs then (1, n - head bs) else (0, n)

digitsMults False b bs n = (ds, ms, ns)
  where 
    q = min (b-1) $ n `quot` head bs
    ds = (q :) $ padLeft (length bs - 1) 0 $ baseDigits b (n - q * head bs) []
    ns = [0..b-1] ++ replicate (length bs - fromInteger b) 0
    ms = counts [0..b-1] ds ++ replicate (length bs - fromInteger b) 0

reciprocalPSV :: CanCommit v s => Integer -> v -> v -> [v] -> [v]
              -> s -> [s] -> s -> s -> [Bool] -> RPWitness s
              -> PedersenScalarVector (NormLinear []) v s
reciprocalPSV deg h g hs gs q cs y yInv bits (RPW bl sc lin nrm) = makePSV bl h sc g $ makeNormLinear q cs (zipWith (*) ns nrm) gs' lin hs
  where
    ns = map (\b -> if b then y^deg else 1) bits
    gs' = zipWith (appIf ((yInv^deg) *^)) bits gs

splitAtMaybe :: Int -> [a] -> Maybe ([a], [a])
splitAtMaybe n xs = let (as, bs) = splitAt n xs in if length as == n then Just (as, bs) else Nothing

takeMaybe :: Int -> [a] -> Maybe [a]
takeMaybe n xs = let ys = take n xs in if length ys == n then Just ys else Nothing

computeRecips :: (Integral a, Fractional a) => a -> [a] -> [a] -> [a]
computeRecips e xs ds = batchInverse $ zipWith (*) xs $ map (e -) ds

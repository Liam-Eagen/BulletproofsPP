module RangeProof.Internal where

import Data.List (tails, transpose)
import qualified Data.Map as M
import Data.AdditiveGroup
import Data.VectorSpace
import Control.Monad (replicateM)
import qualified Data.ByteString.Lazy as BS

import Utils
import Commitment 
import ZKP
import Bulletproof
import Encoding

-- Implements common functionality for both Binary and Reciprocal range proofs
-- including the VectorSpace instance for the RPWitness type.

-- TODO unify with commitment types somehow? Rename
-- TODO need to remove the blinding for these
--data RPWitness s = RPW { getBlindingRPW :: s, getScalarRPW :: s, getLinearRPW :: [s], getNormRPW :: [s] }
data RPWitness s = RPW { getScalarRPW :: s, getLinearRPW :: [s], getNormRPW :: [s] }
  deriving (Eq, Show, Functor)

instance Zip RPWitness where
  zipWith' f (RPW s0 l0 n0) (RPW s1 l1 n1) = RPW (f s0 s1) (zipWith' f l0 l1) (zipWith' f n0 n1)
  zipWithDef'' f z0 z1 (RPW s0 l0 n0) (RPW s1 l1 n1) = RPW (f s0 s1) (zip' l0 l1) (zip' n0 n1)
    where zip' = zipWithDef'' f z0 z1

  -- TODO don't use
  zipWithDef' f = zipWithDef'' f (error "called with one default")

instance Num s => AdditiveGroup (RPWitness s) where
  zeroV = RPW 0 [] []
  (^+^) = zipWithDef'' (+) 0 0
  (^-^) = zipWithDef'' (-) 0 0
  negateV = fmap negate

instance Num s => VectorSpace (RPWitness s) where
  type Scalar (RPWitness s) = s
  s *^ v = fmap (s *) v

commitRPW :: CanCommit v s => s -> v -> [s] -> [v] -> [s] -> [v] -> v
commitRPW (sc :: s) (g :: v) ln hs xs gs = commit (ChC body)
  where 
    body :: forall a b. (s -> v -> a) -> (a -> b -> b) -> b -> b
    --body (*:) (+:) z = dotWith (*:) (+:) ln hs $ dotWith (*:) (+:) xs gs $ (sc *: g) +: z
    body = dotWith ln hs .: dotWith xs gs .: dotWith [sc] [g]

unblindedRPW :: CanCommitM v s m => s -> [s] -> [s] -> m (RPWitness s)
unblindedRPW sc ln xs = return $ RPW sc ln xs

scalarRPW' :: CanCommitM v s m => PedersenScalar v s -> m (RPWitness s)
scalarRPW' ps = return $ RPW (scalarCP $ scalarPS ps) [scalarCP $ blindingPS ps] []

scalarPairRPW' :: CanCommitM v s m => PedersenScalarPair v s -> m (RPWitness s)
scalarPairRPW' (PSP b (sc0, sc1)) = return $ RPW (scalarCP sc0) [scalarCP sc1, scalarCP b] []

space :: a -> [a] -> [a]
space z [] = []
space z [x] = [x]
space z (x:xs) = x:z:space z xs

-- Computes the weighted self convolution
makePolyTerms :: Integral a => [a] -> [[a]] -> [a]
makePolyTerms ws tss = map sum $ transpose rows
  where
    -- convenience
    f xss = uncurry (weightedDotZip ws) <$> zip tss xss
    -- All square terms, counted once
    sqs = space 0 $ f $ tss
    -- Rest of terms counted twice
    dotss = space 0 . fmap (2 *) . f <$> tail (tails tss)
    -- Shift each row the corresponding amount
    rows = (sqs :) $ uncurry ((++) . flip replicate 0) <$> zip [1..] dotss
    

-- Could be faster?
counts :: (Eq a, Ord a) => [a] -> [a] -> [Integer]
counts xs ys = [ M.findWithDefault 0 x m | x <- xs]
  where m = M.fromListWith (+) $ zip ys $ repeat 1

---------------------
-- List Operations --

splitAtMaybe :: Int -> [a] -> Maybe ([a], [a])
splitAtMaybe n xs = let (as, bs) = splitAt n xs in if length as == n then Just (as, bs) else Nothing

takeMaybe :: Int -> [a] -> Maybe [a]
takeMaybe n xs = let ys = take n xs in if length ys == n then Just ys else Nothing

dropIf :: [Bool] -> [a] -> [a]
dropIf fs xs = snd <$> filter (not . fst) (zip fs xs)

replaceIf :: [Bool] -> a -> [a] -> [a]
replaceIf fs y xs = [ if f then y else x | (f, x) <- zip fs xs ]

-- List operations
insertAt :: Int -> a -> [a] -> [a]
insertAt n x xs = ys ++ (x : zs)
  where (ys, zs) = splitAt n xs

removeAt :: Int -> [a] -> [a]
removeAt n xs = ys ++ zs
  where (ys, _:zs) = splitAt n xs

sumDiagonals :: Num a => [[a]] -> [a]
sumDiagonals xss = M.elems m
  where
    m = M.fromListWith (+) $ do
      (a, xs) <- zip [0..] xss
      (b, x) <- zip [0..] xs
      return (a + b, x)

--------------------------------
-- Generic Blinding Functions --
-- For < v_{n-1}, v_n >_q

scaleErrs n r1Inv xs = ys ++ ((r1Inv *) <$> as) ++ bs
  where 
    (ys, zs) = splitAt (n+1) xs 
    (as, bs) = splitAt (n-2) zs

appLast :: (a -> a) -> [a] -> [a]
appLast f xs = ys ++ [f y]
  where
    (ys, [y]) = splitAt (length xs - 1) xs

addConsts :: Num a => a -> a -> [a] -> [a]
addConsts a b (x:y:zs) = (a*x + b*y) : zs

-- Accepts the term that the value occurs on and the term of this commitment.
-- Generates the appropriate random values and zeros
blindWitness :: (CanCommitM v s m) => Int -> Int -> [s] -> [s] -> m (RPWitness s)
blindWitness n k ls ns = do
  -- Have an extra blinding value because of types
  let nBls = if k == 1 then 2*n-1 else 2*n-k+1
  bls <- padRight (2*n + 1) 0 . insertAt (2*n - k) 0 <$> replicateM nBls random
  let bl0:bls' = bls

  -- Append blinded terms
  unblindedRPW bl0 (bls' ++ ls) ns

-- The witness commitment with error terms (i.e. recips in typed range proof)
blindErrWitness :: (CanCommitM v s m) => Int -> [s] -> [s] -> [s] -> m (RPWitness s)
blindErrWitness n es ls ns = do
  let nBls = n + 1
  bls <- padRight (2*n + 1) 0 . (++ es) . insertAt (n) 0 <$> replicateM nBls random
  let bl0:bls' = bls

  -- Append blinded terms
  unblindedRPW bl0 (bls' ++ ls) ns

-- Then another function that accepts all the other commitments, pulls out the
-- correct values, as well as the higher order error terms and generates the
-- final blinding values.
blindBlindingTerm :: CanCommitM v s m => RPWitness s -> s -> (s, s) -> (s, s) -> [s] -> [RPWitness s] -> s -> m (RPWitness s)
blindBlindingTerm (RPW 0 (blT:blsLin) blsNrm) tC (r0, r0Inv) (r1, r1Inv) errs wits inputBl = do
  -- terms organized as
  --   t^0 in scalar
  --   type
  --   t^1..t^(n-2)         r0 r1
  --   t^(n+1)..t^(2n-2)    r0
  --   
  -- This allows us to put the q-free error terms in the t^(n+1)..t^(2n-2)
  -- components of commitmentment n. We treat term t^(2n) specially to handle
  -- inputs. See paper for more details. Since commitment n is only scaled by
  -- r0 and monomials t^(n+1)..t^(2n-2) are only scaled by r0, we need to modify
  -- the scaling.
  --
  -- In the witness, error terms of these degrees are scaled by r1Inv. Then,
  -- following the diagonal sum, all the blinded error terms of these degrees
  -- are multiplied by r1. Since the constant and type are not scaled at all,
  -- they are scaled by r0Inv*r1Inv before the diagonal sums.
  let rsInv = r0Inv * r1Inv
  let n = length wits       -- Number of terms 
  let n' = 2 * n - 2        -- Extra error terms here
 
  -- Remove the rest of the linear witness, as well as the error terms embedded
  -- in the final witness. Negate all the blinding values to balance with the
  -- earlier commitments
  let (wits', [witErr]) = splitAt (n-1) wits
  let witErr' = getScalarRPW witErr : (padRight (2*n) 0 $ take (n+1) $ getLinearRPW witErr)
  let witRows = zipWith (:) (getScalarRPW <$> wits) $ (take (2*n) . getLinearRPW <$> wits')
  let witRows' = (\(x:y:xs) -> (x :) $ (y :) $ negate <$> xs) <$> (witRows ++ [witErr'])

  -- Combine the degree zero error terms (types and scalar), insert empty column
  -- at value term, then sum the diagonals. Remove the input blinding from the
  -- final error term.
  let errs' = negate <$> (head errs - tC * blT : fmap (rsInv *) (tail errs))
  let table = insertAt (2*n-1) 0 <$> errs' : (scaleErrs n r1Inv . addConsts (rsInv) (rsInv*tC) <$> witRows')
  let blErrs = appLast (\x -> x - (2*inputBl)) $ scaleErrs n r1 $ take (2*n) $ removeAt (2*n-1) $ sumDiagonals table
   
  -- Final commitment
  unblindedRPW (negate $ head blErrs) (blT : tail blErrs ++ blsLin) blsNrm


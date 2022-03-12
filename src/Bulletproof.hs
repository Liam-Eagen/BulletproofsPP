{-# LANGUAGE QuantifiedConstraints, RankNTypes #-}

module Bulletproof where

import Data.Maybe (maybe)
import Data.Bifunctor
import Data.Foldable (foldrM)
import Control.Monad (replicateM)

import Data.Bits
import Data.VectorSpace
import Data.Field.Galois (PrimeField)
import qualified Data.Field.Galois as GF

import qualified Data.Vector as V

import Data.Field.Eis
import Data.Curve.CM
import Utils
import Commitment 
import ZKP

-- Testing to see improvement?
import Control.Parallel.Strategies


-- Intended to allow substituting other containers in the future.
class (Functor f, Foldable f, Zip f
      , forall a. (Show a) => Show (f a), forall a. (Eq a) => Eq (f a)) 
      => BPCollection f where
  empty' :: f a
  single' :: a -> f a
  unHalves'' :: f (a, a) -> f a
  
  -- TODO remove, debugging Show
  tensor' :: (Num a, Show a) => f a -> [a] -> [a] -> f a

  fromList' :: [a] -> f a

  -- Accepts a function to apply to pairs of adjacent points and an accumulated
  -- fold state. Produces a new accumulated value and new value for the pair.
  -- Accepts default parameter for odd length. Should be able to take advantage
  -- of known size in some cases
  foldMapHalves :: (a -> a -> c -> (c, b)) -> a -> c -> f a -> (c, f b)
  foldMapHalves f d z xs = (foldHalves g d z xs, mapHalves h d xs)
    where 
      g x y a = fst $ f x y a
      h x y = snd $ f x y z     -- NOTE this isn't really correct

  -- This takes the halves applies a combining function to every two elements,
  -- and the accumulated result. Accepts a default paramter and folds to the
  -- left
  foldHalves :: (a -> a -> c -> c) -> a -> c -> f a -> c
  foldHalves f d z xs = fst $ foldMapHalves (\x y a -> (f x y a, ())) d z xs

  -- This takes the halves and applies a a function to every two elements and
  -- outputs the result as a collection
  mapHalves :: (a -> a -> c) -> a -> f a -> f c
  mapHalves f d xs = snd $ foldMapHalves (\ x y _ -> ((), f x y)) d () xs

  -- Takes shorter sequence, dots with subsequences of same length in longer
  -- sequence. This is akin to tensoring with the identity matrix so that we can
  -- extract the intermediate values. TODO rename?
  contract' :: Num a => f a -> f a -> f a

  parColl :: Strategy a -> Strategy (f a)

instance BPCollection [] where
  empty' = []
  single' x = [x]

  unHalves'' [] = []
  unHalves'' ((x,y):zs) = x : y : unHalves'' zs

  fromList' x = x

  foldMapHalves f d !z [] = (z, [])
  foldMapHalves f d !z (x:[]) = let (z', v) = f x d z in (z', [v])
  foldMapHalves f d !z (x:y:zs) = let (!z', v) = f x y z
                                      (!z'', vs) = foldMapHalves f d z' zs
                                  in (z'', v:vs)
  
  foldHalves f d !z [] = z
  foldHalves f d !z (x:[]) = f x d z
  foldHalves f d !z (x:y:zs) = let !z' = f x y z in foldHalves f d z' zs

  -- Must preserve order here for correctness
  mapHalves f d [] = []
  mapHalves f d (x:[]) = [f x d]
  mapHalves f d (x:y:zs) = f x y : mapHalves f d zs

  -- Accepts the base case, challenges in reverse order and q powers in correct
  -- order. TODO should maybe refactor?
  tensor' bs es qs = (*) <$> bs <*> (fst $ foldr step ([1], qs) es)
    where step e (ts, q:qs) = ( (*) <$> [q, e] <*> ts, qs )

  contract' xs ys = map (dotZip xs) $ chunks (length xs) ys

  parColl = parListChunk 8

-- See Utils for Zip instance
instance BPCollection V.Vector where
  empty' = V.empty
  single' = V.singleton

  unHalves'' xs = V.generate n go
    where
      n = 2*V.length xs
      go i = let (q, r) = i `divMod` 2
             in case (xs V.! q, r) of
               (p, 0) -> fst p
               (p, 1) -> snd p

  tensor' bs es qs = V.generate (lExp * bLen) multIndex
    where
      xs = zip3 [0..] (reverse es) qs
      lExp = 2^(length xs)
      bLen = length bs
      multIndex n = b0 * product [ if testBit n (k) then e else q | (k, e, q) <- xs ]
        where
          -- Upper values encode which b to use
          b0 = bs V.! (n `div` lExp)
  
  fromList' = V.fromList

  -- Probably get rid of foldMap since there is no nice way to implement with
  -- vectors

  -- TODO need to test that the left fold is valid here, should be.
  --foldHalves :: (a -> a -> c -> c) -> a -> c -> f a -> c
  foldHalves f d z xs = V.ifoldl' go z xs
  --foldHalves f d z xs = V.ifoldr go z xs
    where
      --go n x z = if even n then f x y z else z
      go z n x = if even n then f x y z else z
        where y = (maybe d id $ xs V.!? (n + 1))
      
  -- This takes the halves and applies a a function to every two elements and
  -- outputs the result as a collection
  --mapHalves :: (a -> a -> c) -> a -> f a -> f c
  mapHalves f d xs = V.generate n go
    where
      n = uncurry (+) $ length xs `quotRem` 2
      go i = f (xs V.! (2*i)) (maybe d id $ xs V.!? (2*i + 1))

  --contract' :: Num a => f a -> f a -> f a
  contract' xs ys = V.generate n' go
    where
      xLen = length xs
      yLen = length ys
      (n, r) = yLen `quotRem` xLen
      n' = n + (if r /= 0 then 1 else 0)

      -- Index in resulting list govern chunks of ys
      go i = V.sum $ V.zipWith (*) xs ys'
        where
          ys' = if i == n
                  then V.drop (yLen - r) ys
                  else V.slice (i * xLen) xLen ys

  --parColl :: Strategy a -> Strategy (f a)
  parColl = const rseq

-- Keeps track of normalization

-- TODO trying everything strict because this is internal, not sure if better
data BPFrame'' g f v s = BPF'' { nrmlz'' :: !s, body'' :: f (g v s) } deriving (Eq, Show)

instance (Functor f, Bifunctor g) => Bifunctor (BPFrame'' g f) where
  bimap f g (BPF'' n sgs) = BPF'' (g n) $ bimap f g <$> sgs

instance (Functor f, Foldable f, Opening g) => Opening (BPFrame'' g f) where
  -- Normalization is not incorporated into commitment
  openWith (BPF'' _ sgs) (*:) (+:) !z = foldr (\x z -> openWith x (*:) (+:) z) z sgs

-------------------------
-- Generic Bulletproof --

class Opening f => BPOpening f where
  -- InnerProduct requires witnesses by even length in total. TODO should make
  -- decoding part of the argument so that this can be handled internally
  -- alignWitness :: f v s -> Int -> Int

  -- Given the object, determine the optimal number of rounds to reduce
  optimalRounds :: f v s -> (Int, Int)

  -- Return the two response scalars, response witnesses.
  -- TODO try just computing commitments?
  makeScalarsComs :: (CanCommit v s) => f v s -> (s, f v s, s, f v s)

  -- The pattern to combine, e.g. (e, e^2 - 1), (1/e, e), (1/e^2, e^2)
  -- Accepts a dummy parameter for type
  makeEs :: Fractional s => f x y -> s -> (s, s)

  -- Given commitment, evaluate scalar from vector. NOTE may not necessarily
  -- work for the responses
  evalScalar :: Num s => f x s -> s

  -- Collapse the commitment given the challenge
  collapse :: CanCommit v s => s -> f v s -> f v s

  -- Necessary to write proof out
  getWitness :: Num s => f x s -> [s]

  -- NOTE must configure object to return the correct scalar when we call
  -- evalScalar
  expandChallenges :: CanCommit v s => [s] -> f x0 s -> f x1 s -> f v x2 -> (s, f v s)

---- NOTE the size parameter is not checked sized values
-- Given eisenstein representations, use that
--collapsePoints' :: CanCommit v s => Int -> Eis Integer -> Eis Integer -> (v -> v -> v)
--collapsePoints' n b a lg rg = shamirEis' n b lg a rg
collapsePoints :: CanCommit v s => ReducedScalar s -> ReducedScalar s -> (v -> v -> v)
collapsePoints b a lg rg = projectivePairIP (b, lg) (a, rg)

-- TODO rework this somehow...
class BPOpening f => Weighted f where
  -- Accepts a dummy parameter and changes how the q powers to accomodate the
  -- particular argument
  qPowers' :: (Functor p, Num s) => p (f v s) -> s -> [s]

-----------------------
-- Generic Arguments --

data BPCompose f g v s = BPComp { scalarComp :: s, leftComp :: f v s, rightComp :: g v s }
  deriving (Eq, Show)

instance (Bifunctor f, Bifunctor g) => Bifunctor (BPCompose f g) where
  bimap f g (BPComp s a b) = BPComp (g s) (bimap f g a) (bimap f g b)

instance (Opening f, Opening g) => Opening (BPCompose f g) where
  openWith (BPComp _ a b) (*:) (+:) x = openWith a (*:) (+:) $ openWith b (*:) (+:) x

instance (BPOpening f, BPOpening g) => BPOpening (BPCompose f g) where
  -- If the number of rounds of one of the subproofs is larger, then use that.
  -- If they are the same need to increase by 1
  optimalRounds c = error $ show (aL', bL') -- res
    where
      -- Optimal reduce subproofs, then equalize, then make sure witness is
      -- small enough.
      (aR, aL) = optimalRounds (leftComp c) 
      (bR, bL) = optimalRounds (rightComp c)

      r = max aR bR
      aL' = roundReduceBy aL $ r - aR
      bL' = roundReduceBy bL $ r - bR

      res = if aL' + bL' > 5
              then (r + 1, roundReduce aL' + roundReduce bL')
              else (r, aL' + bL')
 
  -- NOTE if these are not the same, then will fail
  -- could refactor out into a type or something to check compatibility
  makeEs (BPComp _ a _) = makeEs a

  evalScalar (BPComp s a b) = s * (evalScalar a + evalScalar b)
  
  makeScalarsComs (BPComp s a b) = (slA + slB, BPComp s wlA wlB, srA + srB, BPComp s wrA wrB)
    where
      (slA, wlA, srA, wrA) = makeScalarsComs a
      (slB, wlB, srB, wrB) = makeScalarsComs b
  
  --getWitness :: f x s -> [s]
  getWitness (BPComp s a b) = (s *) <$> getWitness a ++ getWitness b

  collapse e (BPComp s a b) = BPComp s (collapse e a) (collapse e b)

  expandChallenges es (BPComp _ a b) (BPComp s ap bp) (BPComp _ ag bg) = res
    where res = bizipPair (+) (BPComp s) (expandChallenges es a ap ag) (expandChallenges es b bp bg)

-- Inherits weights from first parameter. 
instance (Weighted a, BPOpening b) => Weighted (BPCompose a b) where
  qPowers' x q = qPowers' (leftComp <$> x) q -- (BPComp _ a _) q = qPowers' a q

-- Generic Norm Linear proof class to support argument agnostic protocols
class (Weighted p, BPOpening p) => NormLinearBP p where
  type Coll p :: * -> *

  -- Accepts the q, linear weights, linear witness, norm witness, and associated bases
  makeNormLinearBP :: (t ~ Coll p, BPCollection t, CanCommit v s) 
                   => s -> t s -> t s -> t v -> t s -> t v -> p v s
  makeNormLinearBP = makeNormLinearBP' 1
  
  -- Accepts the scalar weight, q, linear witness, norm witness, and associated bases
  makeNormLinearBP' :: (t ~ Coll p, BPCollection t, CanCommit v s) 
                    => s -> s -> t s -> t s -> t v -> t s -> t v -> p v s
  
  -- Given the initial norm length and the initial linear length, returns the
  -- optimal number of rounds to perform to acheive the lowest proof size as
  -- well as the final norm and linear lengths
  optimalWitnessSize :: p v s -> Int -> Int -> (Int, (Int, Int))
 
makeNormLinearBPList :: (NormLinearBP p, BPCollection (Coll p), CanCommit v s) 
                     => s -> [s] -> [s] -> [v] -> [s] -> [v] -> p v s
makeNormLinearBPList s cs nrm gs lin hs = makeNormLinearBP s cs' nrm' (fromList' gs) lin' (fromList' hs)
  where [cs', nrm', lin'] = fromList' <$> [cs, nrm, lin]

-- Given an initial length, returns the number of rounds to reduce and the final
-- reduced length after that many rounds
numberRoundsReduce :: Int -> (Int, Int)
numberRoundsReduce n | n < 5 = (0, n)
numberRoundsReduce n = (1 + r, n')
  where (r, n') = numberRoundsReduce $ roundReduce n
 
-- Reduce to less than 3
numberRoundsReduce' n = if n' > 2 then (r + 1, roundReduce n') else (r, n')
  where (r, n') = numberRoundsReduce n

-- Perform one round of reduction (1 -> 1)
roundReduce :: Int -> Int
roundReduce n = uncurry (+) $ n `divMod` 2

-- Perform a number of round reductions
roundReduceBy :: Int -> Int -> Int
roundReduceBy n 0 = n
roundReduceBy n k = roundReduceBy (roundReduce n) $ k - 1

-------------------------
-- Prover and Verifier --
-------------------------

-- Bulletproof Commitment type, accepts argument
type BPC = PedersenScalarVector

-- NOTE range proofs are instantiated based on the c type
data SetupBP c f v s = SBP { basisBP :: !(BPC f v s), initCom :: !(c v s), publicCs :: !(BPC f v s), rounds :: !Int }
  deriving (Eq, Show)
data WitnessBP (c :: * -> * -> *) f v s = WBP { witnessBP :: !(BPC f v s) }
  deriving (Eq, Show)
data Bulletproof (c :: * -> * -> *) f v s = PBP { responses :: [(v, v)], opening :: !(BPC f v s) }
  deriving (Eq, Show)

instance (Opening c, BPOpening f) => ZKP (Bulletproof c f) where
  type Setup (Bulletproof c f) v s = SetupBP c f v s
  type Witness (Bulletproof c f) v s = WitnessBP c f v s

  -- TODO witness contains basis... could check that they are the same? Doesn't
  -- matter, will just produce proof that won't verify
  -- NOTE assumes that wit is an opening of commit ic ^+^ commit pub
  proveM (SBP _ _ _ n) (WBP wit) = uncurry (flip PBP) <$> proveBPM n wit

  -- Uses pub to avoid extra computation with ic commitment by combining inner
  -- product with the expanded challenges
  verifyM (SBP bss ic pub n) (PBP rs opn) = verifyBPM ic rs pub bss opn

proveRoundM :: (CanCommitM v s m, BPOpening f) => BPC f v s -> m (BPC f v s, (v, v))
proveRoundM com@(PSV s c) = do
  let (as, a, bs, b) = makeScalarsComs c
  let ac = commit $ updatePSV com as a
  let bc = commit $ updatePSV com bs b
  e <- head <$> oracle [ac, bc]
  let (e0, e1) = makeEs c e
  let sc' = scalarCP s + (e0 * as + e1 * bs)
  let com' = updatePSV com sc' $ collapse e c
  return (updatePSV com sc' $ collapse e c, (ac, bc))

proveBPM :: (CanCommitM v s m, BPOpening f) => Int -> BPC f v s -> m (BPC f v s, [(v, v)])
proveBPM n com = foldrM step (com, []) (replicate n ())
  where step () (com, resps) = fmap (: resps) <$> proveRoundM com

-- Used to compute the final inner product
verifyWith :: (CanCommit v s, Opening c, Opening f)
           => c v s -> [s] -> [(v, v)] -> f v s -> (s -> (s,s)) -> (s -> v -> a) -> (a -> b -> b) -> b -> b

verifyWith c es vs wit mkEs = openWith wit .: openWith c .: dotWith es' vs'
  where
    vs' = unPairs vs
    es' = es >>= pairToList . mkEs

verifyBPM :: (CanCommitM v s m, BPOpening f, Opening c)
          => c v s -> [(v, v)] -> BPC f x0 s -> BPC f v x1 -> BPC f x2 s -> m Bool
-- TODO want to not accept the sw so just the BPOpening 
verifyBPM cI rs (PSV sp pub) b@(PSV sg bss) (PSV sw wit) = do
  es <- foldrM (\(a,b) es -> (:) <$> (head <$> oracle [a,b]) <*> return es) [] rs
  let (sc, chs) = expandChallenges es wit pub bss
  let wit' = updatePSV b (scalarCP sp - sc) chs
  let commitIsValid = zeroV == commit (ChC $ verifyWith cI es rs wit' $ makeEs chs)
  return $ commitIsValid

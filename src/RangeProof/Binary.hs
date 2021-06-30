{-# LANGUAGE TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

module RangeProof.Binary where

import Data.Bifunctor
import Control.Monad (replicateM)

import Data.VectorSpace
import Data.List (mapAccumR)

import Utils
import Commitment
import NormLinearProof

import RangeProof.Internal

data BinaryFrame a = BF { base :: a, digit :: a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative BinaryFrame where
  pure a = BF a a
  (BF fb fd) <*> (BF b d) = BF (fb b) (fd d)

makeFrames :: Integral a => Range -> a -> Maybe [BinaryFrame a]
makeFrames (R min max) n = if isValidRange then Just $ map (fmap fromInteger) $ zipWith BF (bn:bs) (dn:ds) else Nothing
  where
    nAdj = toInteger $ n - fromInteger min
    isValidRange = (max > min) && (nAdj >= 0) && (max - min > nAdj)
    n1 = integerLog 2 (max - min - 1)
    bn = (max - min) - 2^n1
    bs = [2^(n1 - i) | i <- [1..n1]]
    (dn, nAdj') = if nAdj > bn then (1, nAdj - bn) else (0, nAdj)
    ds = padLeft (fromInteger n1) 0 $ baseDigits 2 nAdj' []

-- For each sublist use a different power of x and for each element use a
-- different power of q.
publicConsts :: (Fractional a, Integral a) => a -> a -> [Range] -> [[a]] -> (a, [a])
publicConsts q x rs bss = mapAccumR f z $ zip3 bxs (powers' q) (powers' $ 1/q)
  where
    bxs = concat $ zipWith (map . (*)) (powers' x) bss
    z = (2 *) $ negate $ dotZip (fromInteger . minRange <$> rs) $ powers' x
    f s (bx, q, r) = let p = (-1/2) + bx * r^2 in (s + (q * p)^2, p)

-------------------------
-- Prover and Verifier --

data TranscriptBRP v s = TBRP { commits :: [v], xChallenge :: s, tChallenge :: s }
  deriving (Eq, Show)

instance Bifunctor TranscriptBRP where
  bimap f g (TBRP coms x t) = TBRP (f <$> coms) (g x) (g t)

instance Commitment TranscriptBRP where
  commitWith (TBRP (bl2:bl1:dCom:nComs) x t) (*:) (+:) z = dotWith (*:) (+:) ((2 *) <$> powers' x) nComs p
    where p = ((t^2) *: bl2) +: ( (t *: bl1) +: ( (1 *: dCom) +: z ) ) 

type BPBRP = Bulletproof TranscriptBRP (Norm [])

--prepareRanges ns = traverse (uncurry makeFrames . fmap (scalarCP . scalarPS)) ns

-- This handles all the interactions with the actual basis elements.
data SetupBRP v s = SBRP
  { rangesBRP :: [Range]
  , comSBRP :: RPWitness s -> v
  , psvSBRP :: s -> RPWitness s -> PedersenScalarVector (Norm []) v s 
  }

setupBRP :: (CanCommit v s) => [v] -> [Range] -> SetupBRP v s
setupBRP (h : g : gs) rs = SBRP rs com psv
  where
    com (RPW bl sc _ nrm) = commitRPW bl h sc g [] [] nrm gs
    psv q (RPW bl sc _ nrm) = makePSV bl h sc g $ makeNorm q nrm gs

data WitnessBRP v s = WBRP [PedersenScalar v s] [[BinaryFrame s]]

witnessBRP :: (CanCommit v s) => SetupBRP v s -> [PedersenScalar v s] -> Maybe (WitnessBRP v s)
witnessBRP (SBRP rs _ _) ns = fmap (WBRP ns) $ traverse (uncurry makeFrames) $ zip rs $ scalarCP . scalarPS <$> ns

-- Monadic Prover
proveBRPM :: CanCommitM v s m
          => SetupBRP v s -> WitnessBRP v s -> m ([v], Setup BPBRP v s, Witness BPBRP v s)
proveBRPM (SBRP rs commit' makePSV') (WBRP ns fs) = do
  -- Phase 1: commit to digits
  let BF bs ds = sequenceA $ concat fs
  let len = length ds
  (nWits, nComs) <- unzip <$> map (idAp commit') <$> mapM scalarRPW ns
  (dWit, dCom) <- idAp commit' <$> normRPW 0 ds
  qx <- take 2 <$> oracle (dCom:nComs)
  let [q, x] = qx

  -- Phase 2: commit to blinding
  let pub = uncurry (flip (RPW 0) []) $ publicConsts q x rs $ map (map base) fs
  let wit = pub ^+^ dWit ^+^ 2 *^ sumV (zipWith (*^) (powers' x) nWits)
  blsNrm <- replicateM len random
  let (bl1Sc, bl2Sc) = makeBlindingTerms (powers' $ q^2) (getNormRPW wit) blsNrm
  (bl1Wit, bl1Com) <- idAp commit' <$> normRPW bl1Sc blsNrm
  (bl2Wit, bl2Com) <- idAp commit' <$> normRPW bl2Sc [] -- (repeat 0) 
  t <- head <$> oracle [bl1Com, bl2Com]

  -- Phase 3: setup bulletproof
  let coms = bl2Com : bl1Com : dCom : nComs
  let bpCom = TBRP coms x t
  let bpRounds = (fromInteger $ integerLog 2 $ toInteger len) - 1
  let bpWit = makePSV' q $ wit ^+^ t*^bl1Wit ^+^ (t^2)*^bl2Wit

  return (coms, SBP (makePSV' q zeroV) bpCom (makePSV' q pub) bpRounds, WBP bpWit)

-- Checks only the parts that are not part of the bulletproof. That is, all the
-- challenges are properly constructed. Returns the public scalars if valid
verifyBRPM :: CanCommitM v s m => SetupBRP v s -> [v] -> m (Maybe (Setup BPBRP v s))
verifyBRPM (SBRP rs _ makePSV') coms = do
  let Just fs = traverse (uncurry makeFrames) $ idAp (fromInteger . minRange) <$> rs
  let (bl2Com:bl1Com:dCom:nComs) = coms
  qx <- take 2 <$> oracle (dCom:nComs)
  let [q,x] = qx
  t <- head <$> oracle [bl1Com, bl2Com]

  let pub = uncurry (flip (RPW 0) []) $ publicConsts q x rs $ map (map base) fs
  let rounds = (fromInteger $ integerLog 2 $ toInteger $ length fs) - 1

  return $ Just $ SBP (makePSV' q zeroV) (TBRP coms x t) (makePSV' q pub) rounds

-- TODO rename
data BinaryRangeProof v s = BRP [v] (BPBRP v s)

instance ZKP BinaryRangeProof where
  type Setup BinaryRangeProof v s = SetupBRP v s
  type Witness BinaryRangeProof v s = WitnessBRP v s

  proveM s w = do
    (coms, s', w') <- proveBRPM s w
    BRP coms <$> proveM s' w'

  verifyM s (BRP coms p') = do
    maybeSetup <- verifyBRPM s coms
    case maybeSetup of
      Nothing -> return False
      Just s' -> verifyM s' p'

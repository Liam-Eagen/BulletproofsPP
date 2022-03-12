module RangeProof.Binary where

import GHC.Generics
import Data.Bifunctor
import Control.Monad (replicateM)

import Data.VectorSpace
import Data.List (mapAccumR, mapAccumL)
import qualified Data.ByteString.Lazy as BS

import Utils
import Commitment
import ZKP
import Bulletproof

import RangeProof
import RangeProof.Internal

------------
-- README --

-- This works exactly the same as the old binary range proof with the error
-- terms modified to be inline. That means we commit to the digits with two
-- linear terms, plus the scalar.
--
-- Then commit to one blinding commitment with error terms. The polynomial is
--
-- | bl + t d |_r = e0 + e1 t + |d|_r t^2
--
--


------------

-- uncurry3 f (x,y,z) = f x y z

data RangeData = RangeData
  { range :: Range
  , isOutput :: Bool
  , isAssumed :: Bool
  , baseCoeffs :: [Integer]
  } deriving (Eq, Show)

-- Determine how many norm components this RangeData will use
nrmLenRangeData :: RangeData -> Int
nrmLenRangeData rd = length $ baseCoeffs rd

makeRangeData :: Integer -> Range -> Bool -> Bool -> Maybe RangeData
makeRangeData char r@(R min max) isO isA = if isValidRange then Just $ RangeData r isO isA (bn:bs) else Nothing
  where
    isValidRange = (max > min) && (max - min < char)
    n1 = integerLog 2 (max - min - 1)
    bn = (max - min) - 2^n1
    bs = [2^(n1 - i) | i <- [1..n1]]

makeDigits :: Integral a => RangeData -> a -> Maybe [a]
makeDigits rd _ | isAssumed rd = Just []
makeDigits rd@(RangeData (R min max) isO isA (bn:bs)) n = res
  where
    nAdj = toInteger $ n - fromInteger min
    isInRange = (nAdj >= 0) && (max - min > nAdj)
    n1 = integerLog 2 (max - min - 1)
    (dn, nAdj') = if nAdj > bn then (1, nAdj - bn) else (0, nAdj)
    ds = padLeft (fromInteger n1) 0 $ baseDigits 2 nAdj' []

    res = if isInRange 
            then Just $ map fromInteger (dn:ds) 
            else Nothing

-- For each sublist use a different power of x and for each element use a
-- different power of q.
makePublicConsts :: (Fractional a, Integral a, Show a) => Bool -> Integer -> a -> (a, a) -> [RangeData] -> RPWitness a
--makePublicConsts cons x (q0, q0Inv) rds bss = mapAccumR f z $ zip3 bxs q2s q2Invs
makePublicConsts cons netPub x (q0, q0Inv) rds = RPW sc [] nrm --mapAccumR f' z $ zip3 q2s q2Invs $ bss
  where
    -- Use x^2
    bss = concat $ zipWith g (powers' $ x^2) rds
    ((_, _, sc), nrm) = mapAccumL f (q0, q0Inv, z) $ bss
    --(sc', nrm') = mapAccumR f' z $ zip3 q2s q2Invs $ bss
    --nrm'' = zipWith (+) (repeat $ -1/2) (zipWith (*) q2Invs bss)
    --sc'' = weightedDotZip q2s nrm'' nrm''

    q2s = powers' q0
    q2Invs = powers' q0Inv
    mins = [ if isAssumed rd then 0 else fromInteger $ minRange $ range rd | rd <- rds ]
    netPub' = if cons then (-x) * fromInteger netPub else 0
    z = (*) (-2) $ (netPub' +) $ dotZip mins $ powers' $ x^2 -- inputCoeffs cons (isOutput <$> rds) (isAssumed <$> rds) x

    -- Drop public coeffs if assumed
    g xi (RangeData _ isO isA bs) = if isA then [] else (xi *) . fromInteger <$> bs

    -- TODO pick one.
    f (q2, q2Inv, s) bx = let p = (-1/2) + bx * q2Inv in ((q2*q0, q2Inv*q0Inv, s + q2 * p^2), p) 
    --f' (s) (q2, q2Inv, bx) = let p = (-1/2) + bx * q2Inv in ((s + q2 * p^2), p) 

-------------------------
-- Prover and Verifier --

--data TranscriptBRP v s = TBRP { commits :: [v], xChallenge :: s, tChallenge :: s }
data TranscriptBRP v s = TBRP { cons :: Bool, isOs :: [Bool], isAs :: [Bool], commits :: [v], xChallenge :: s, tChallenge :: s }
  deriving (Eq, Show)

instance Bifunctor TranscriptBRP where
  bimap f g (TBRP cons isOs isAs coms x t) = TBRP cons isOs isAs (f <$> coms) (g x) (g t)

instance Opening TranscriptBRP where
  openWith (TBRP cons isOs isAs (blCom:dCom:nComs) x t) = c
    where 
      xs = (*) (2*t^2) <$> inputCoeffs cons isOs isAs x
      c = dotWith xs nComs .: dotWith [1, t] [blCom, dCom]

instance RPOpening TranscriptBRP where
  type SetupRP TranscriptBRP = SetupBRP
  type WitnessRP TranscriptBRP = WitnessBRP
  type InputWitnessRP TranscriptBRP = PedersenScalar

  witnessRP = witnessBRP
  proveRP = proveBRPM
  verifyRP = verifyBRPM
  infoRP s = (2, nrmLen s, 2)

type BPBRP = Bulletproof TranscriptBRP
type Binary = TranscriptBRP

-- Depending on whether the value is assumed, the proof does a conservation
-- check, and whether each commitment is an input or an output vary the
-- coefficients
inputCoeffs :: Integral a => Bool -> [Bool] -> [Bool] -> a -> [a]
inputCoeffs cons isOs isAs x = zipWith3 f isOs isAs $ powers' $ x^2
  where f isO isA x2 = (if isA then 0 else x2) + (if cons then (if isO then -x else x) else 0)

data SetupBRP arg v s = SBRP
  { nrmLen :: Int
  , rangesBRP :: [RangeData]
  , netPublic :: Integer        -- net public amount
  , conserve :: Bool            -- If true, check that the amounts of inputs sum to outputs
  , qPowers :: s -> [s]
  , comSBRP :: RPWitness s -> v
  , psvSBRP :: s -> s -> s -> RPWitness s -> BPC arg v s 
  }

-- NOTE added basis elements for blinding
setupBRP :: (CanCommit v s, NormLinearBP arg, BPCollection (Coll arg)) => [v] -> Bool -> [RangeData] -> Integer -> Maybe (SetupBRP arg v s)
setupBRP ps cons rds netPub = do
  -- Check that we have enough basis elements
  let nrmLen = sum $ length . baseCoeffs <$> rds
  ([h,g,h0,h1],ps') <- splitAtMaybe 4 ps
  gs <- takeMaybe nrmLen ps'

  let com (RPW sc lin nrm) = commitRPW sc g lin [h0, h1] nrm gs
  let psv q r t (RPW sc lin nrm) = makePSV sc g $ makeNormLinearBP' 1 q cs' (fromList' nrm) (fromList' gs) (fromList' lin) $ fromList' [h0,h1]
                                     where cs' = fromList' [0, r * t]
  
  let qPowers = qPowers' $ proxy' $ vectorPSV $ psv undefined undefined undefined undefined

  return $ SBRP nrmLen rds netPub cons qPowers com psv

data WitnessBRP v s = WBRP [PedersenScalar v s] [s]

-- TODO check that the amounts sum to 0
witnessBRP :: (CanCommit v s) => SetupBRP arg v s -> [PedersenScalar v s] -> Maybe (WitnessBRP v s)
witnessBRP (SBRP _ rs netPub cons _ _ _) ns = do
  let vs = scalarCP . scalarPS <$> ns
  let vSum = sum [ if io then -v else v | (io, v) <- zip (isOutput <$> rs) vs ]
  if cons && (fromInteger netPub + vSum == 0)       -- Check amounts sum to zero
    then return ()
    else Nothing
  fmap (WBRP ns . concat) $ traverse (uncurry makeDigits) $ zip rs vs

-- Monadic Prover
proveBRPM :: (CanCommitM v s m, NormLinearBP arg)
          => SetupBRP arg v s -> WitnessBRP v s -> m ([v], Setup (BPBRP arg) v s, Witness (BPBRP arg) v s)
proveBRPM (SBRP len rds netPub cons qPowers commit' makePSV') (WBRP ns ds) = do
  -- Phase 1: commit to digits
  (nWits, nComs) <- unzip <$> map (idAp commit') <$> mapM scalarRPW' ns
  T2 sBl lBl0 <- sequence $ pure random
  (dWit, dCom) <- idAp commit' <$> unblindedRPW sBl [lBl0, 0] ds
  T3 q x r <- oracle' (dCom:nComs)
  let rInv = recip r
  let q0 = head $ qPowers q
  let qInv = recip q
  let q0Inv = recip q0 

  -- Phase 2: commit to blinding
  let pubWit@(RPW pubSc [] pubNrm) = makePublicConsts cons netPub x (q0, q0Inv) rds
  blsNrm <- replicateM len random
  blBl <- random
  let [bl0Sc, bl1Sc, _] = makePolyTerms (qPowers q) [blsNrm, getNormRPW $ dWit ^+^ pubWit]
  (blWit, blCom) <- idAp commit' <$> unblindedRPW (bl0Sc) [blBl, rInv * (sBl - bl1Sc)] blsNrm
  t <- head <$> oracle [blCom]

  -- Phase 3: setup bulletproof
  let coms = blCom : dCom : nComs
  let bpCom = TBRP cons (isOutput <$> rds) (isAssumed <$> rds) coms x t
  let bpRounds = (fromInteger $ integerLog 2 $ toInteger len) - 1
  -- NOTE Need to scale the public scalar, maps like (s; x) -> (t^2 s; t x)
  let pub' = RPW (t*pubSc) [] pubNrm
  let wit' = pub' ^+^ dWit ^+^ (2 * t) *^ sumV (zipWith (*^) (inputCoeffs cons (isOutput <$> rds) (isAssumed <$> rds) x) nWits)
  let bpWit = makePSV' q r t $ blWit ^+^ t *^ wit'

  let pubBP = (makePSV' q r t $ t *^ pub')
  let (rounds, _) = optimalWitnessSize (vectorPSV $ pubBP) len 2
  
  return (coms, SBP (makePSV' q r t zeroV) bpCom pubBP bpRounds, WBP bpWit)

verifyBRPM :: (CanCommitM v s m, NormLinearBP arg) => SetupBRP arg v s -> [v] -> m (Setup (BPBRP arg) v s)
verifyBRPM (SBRP len rds netPub cons qPowers _ makePSV') coms = do
  let (blCom:dCom:nComs) = coms
  T3 q x r <- oracle' (dCom:nComs)
  let q0 = head $ qPowers q
  let qInv = recip q
  let q0Inv = recip q0
  t <- head <$> oracle [blCom]

  let RPW pubSc [] pubNrm = makePublicConsts cons netPub x (q0, q0Inv) rds
  let pub = RPW (t * pubSc) [] pubNrm
  let pubBP = (makePSV' q r t $ t *^ pub)
  let (rounds, _) = optimalWitnessSize (vectorPSV $ pubBP) len 2
  --let rounds = (fromInteger $ integerLog 2 $ toInteger $ len) - 1

  return $ SBP (makePSV' q r t zeroV) (TBRP cons (isOutput <$> rds) (isAssumed <$> rds) coms x t) pubBP rounds

-- ------------------
-- -- ZKP Instance --
-- 
-- data BinaryRangeProof arg v s = BRP [v] (BPBRP arg v s)
-- 
-- instance NormLinearBP arg => ZKP (BinaryRangeProof arg) where
--   type Setup (BinaryRangeProof arg) v s = SetupBRP arg v s
--   type Witness (BinaryRangeProof arg) v s = WitnessBRP v s
-- 
--   proveM s w = do
--     (coms, s', w') <- proveBRPM s w
--     BRP coms <$> proveM s' w'
-- 
--   verifyM s (BRP coms p') = do
--     s' <- verifyBRPM s coms
--     verifyM s' p'

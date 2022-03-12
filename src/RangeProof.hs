{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module RangeProof where

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

import RangeProof.Internal

-----------------------
-- Range Proof Class --

-- Factor out common interface with the bulletproof code
class Opening p => RPOpening p where
  -- Could write in terms of this instead
  type family SetupRP p = (r :: (* -> * -> *) -> * -> * -> *) | r -> p
  type WitnessRP p :: * -> * -> *
  type InputWitnessRP p :: * -> * -> *

  -- Makes witness
  witnessRP :: (CanCommit v s, NormLinearBP arg)
            => SetupRP p arg v s -> [InputWitnessRP p v s] -> Maybe (WitnessRP p v s)

  -- Meant to be called from ZKP interface, do pre bulletproof proving
  proveRP :: (CanCommitM v s m, NormLinearBP arg)
          => SetupRP p arg v s -> WitnessRP p v s -> m ([v], Setup (Bulletproof p arg) v s, Witness (Bulletproof p arg) v s)

  -- Pre bulletproof verification/construction of the BP Setup
  verifyRP :: (CanCommitM v s m, NormLinearBP arg)
           => SetupRP p arg v s -> [v] -> m (Setup (Bulletproof p arg) v s)

  -- Sufficient to encode and decode
  infoRP :: SetupRP p arg v s -> (Int, Int, Int)

  -- Utility functions for encoding/decoding
  encodeProof :: (BinaryEncodeCurve v, BPOpening arg, s ~ BECScalar v, CanCommit v s)
              => SetupRP p arg v s -> RangeProof p arg v s -> ([v], BS.ByteString)
  encodeProof setup rp = encodeProof' numRpComs nrmLen linLen setup rp
    where (numRpComs, nrmLen, linLen) = infoRP setup

  decodeProof :: (BinaryEncodeCurve v, NormLinearBP arg, s ~ BECScalar v, CanCommit v s, BPCollection (Coll arg))
              => SetupRP p arg v s -> [v] -> BS.ByteString -> Maybe (RangeProof p arg v s)
  decodeProof setup nComs bs = decodeProof' numRpComs nrmLen linLen setup nComs bs
    where (numRpComs, nrmLen, linLen) = infoRP setup

 
-- Given this extra informatino, generic encode/decoding. Can't default because
-- of type families
encodeProof' numRpComs nrmLen linLen setup rp@(RP coms (PBP respPairs bpc)) = (nComs, bs)
  where
    bpComs = unPairs respPairs
    (rpComs, nComs) = splitAt numRpComs coms
    coms' = rpComs ++ bpComs
    scs = getWitness $ vectorPSV bpc
    bs = encodeScalarsCurvePoints scs coms'

decodeProof' numRpComs nrmLen linLen setup nComs bs = do
  -- Determine how many bpRounds were performed
  let dummy = makeNormLinearBP 1 empty' empty' empty' empty' empty'
  let (rounds, (numNrm, numLin)) = optimalWitnessSize dummy nrmLen linLen
  let numComs = numRpComs + 2 * rounds

  -- Decode points and check that there are enough (may be redundant)
  (scs, coms) <- decodeScalarsCurvePoints (numLin + numNrm) numComs bs
  (nrmScs, linScs) <- splitAtMaybe numNrm scs
  (rpComs, bpComs) <- splitAtMaybe numRpComs coms

  -- TODO need to change inteface so we don't need a scalar?
  let nl = makeNormLinearBP 1 empty' (fromList' nrmScs) empty' (fromList' linScs) empty'
  let bpc = PSV (CP 0 zeroV) nl
  let rp = RP (rpComs ++ nComs) $ PBP (pairs bpComs) bpc
  let _ = sameType nl dummy

  return rp

-- ZKP wrapper for a range proof that calls the bulletproof internally
data RangeProof p arg v s = RP { getComsRP :: [v], getBPRP :: Bulletproof p arg v s }
  deriving (Eq, Show)

instance (RPOpening p, NormLinearBP arg) => ZKP (RangeProof p arg) where
  type Setup (RangeProof p arg) v s = SetupRP p arg v s
  type Witness (RangeProof p arg) v s = WitnessRP p v s

  proveM s w = do
    (!coms, !s', !w') <- proveRP s w
    RP coms <$> proveM s' w'

  verifyM s (RP coms p) = do
    s <- verifyRP s coms
    verifyM s p

-- TODO BatchRangeProof type that encapsulates multiple range proofs to be
-- simultaneously verified. The Bulletproof batch verifier currently doesn't fit
-- into the ZKP interface and technically the higher level structure of the
-- range proofs does not matter for batch bulletproof verification.


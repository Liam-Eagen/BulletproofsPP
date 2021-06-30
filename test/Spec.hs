{-# LANGUAGE NoImplicitPrelude, BangPatterns, DataKinds, OverloadedStrings #-}
-- {-# LANGUAGE BangPatterns, DataKinds, OverloadedStrings #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}

--module Main where

import Protolude hiding (hash, fromStrict)

import Data.List (zip3, zip4, zipWith3, zipWith4, unzip3, unzip4, unzip5, zipWith6)
import Data.Maybe (catMaybes, fromJust)
import qualified Data.Map as M

import Data.Curve
import Data.Curve.Weierstrass (WCurve, WPoint, WAPoint, WPPoint, WJPoint, WACurve, Point(A))
import Data.Curve.Weierstrass.SECP256K1 (PA, PP, PJ, Fq, Fr)

import Data.Field.Galois (PrimeField(..), sr, toP, Prime, pow)
import Data.Digest.Pure.SHA (integerDigest, sha256)
import Data.ByteString.Lazy (fromStrict)

import Utils
import Commitment
import NormLinearProof
import qualified RangeProof.Binary as BRP
import qualified RangeProof.TypedReciprocal as TRRP
import qualified RangeProof.Internal as IntRP
import Data.VectorSpace ((*^), (^+^), zeroV, sumV)

-- Given some seed generates a lazy list of random points
getPoints :: (Num q, Curve c f e q r) => ByteString -> [Point c f e q r]
getPoints s = catMaybes $ rec s 0
  where
    rec s n = maybePoint (s <> show n) : rec s (n+1)
    maybePoint = pointX . fromInteger . integerDigest . sha256 . fromStrict

-- Oracle takes points returns deterministic list of scalars
shaOracle :: (WCurve c e q r, WACurve e q r) => [WPoint c e q r] -> [r]
shaOracle ps = fromInteger . integerDigest <$> hashes
  where
    coords :: WACurve e q r => WAPoint e q r -> ByteString
    coords (A x y) = show x <> show y
    hashes = [ sha256 $ fromStrict $ show n <> show (length ps) <> foldMap (coords . toA) ps | n <- [1..] ]

-- Hash to scalar for convenience
testString :: ByteString
testString = show "Random Prefix"

hashToScalar :: PrimeField p => ByteString -> p
hashToScalar s = fromInteger $ integerDigest $ sha256 $ fromStrict $ testString <> s

hashToScalars :: PrimeField p => ByteString -> [p]
hashToScalars s = map (hashToScalar . (s <>) . show) [1..]

main :: IO ()
main = do
  print "Hi"

  -- Deterministically generated base points and blinding randomness for proofs
  let ps@(h:g:ht:_) = fromA <$> getPoints "Test Points" :: [PJ]
  let bls = hashToScalars "Vector Blinds"

  --let bases = [16, 16]
  let bases = [3, 16]
  let ranges = [R 0 $ 2^64, R (-20) $ 2^66 - 1] -- , R 12 $ 2^64 - 311, R (-345) $ 2^64 + 2003]
  let values = [123, 123]
  let types = [1, 1]
  let blinds = hashToScalars "Values blinds" :: [Fr]
  
  -- NOTE the range proofs ignore the basis elements and just use the witness
  -- data. Committing to these values directly will yield different results if
  -- they do not agree with prover about basis.
  let valuePSs = [ makePS bl h n g | (n, bl) <- zip values blinds]
  let valuePSPs = [ makePSP bl h n g t ht | (n, bl, t) <- zip3 values blinds types]
  
  ----------------------------
  -- Reciprocal Range Proof --
  
  let useTypes = True
  let publicCommits = []
  let commitments = zip4 bases ranges [False, True] [True, False]
  let Just (trrpSetup@(TRRP.STRRP hasTypes mBases pubVT rcs makeBaseMap' commit' makePSV')) = TRRP.setupTRRP ps useTypes publicCommits commitments
  let Just (trrpWit@(TRRP.WTRRP valuePSPs' baseMss ph1ss)) = TRRP.witnessTRRP trrpSetup valuePSPs

  print $ mBases 
  print trrpWit
  print ph1ss

  trrpProof <- runZKPT (return . shaOracle) bls $ proveM trrpSetup trrpWit
  let _ = trrpProof :: TRRP.TypedReciprocalRangeProof PJ Fr
  trrpWorked <- runZKPT (return . shaOracle) [] $ verifyM trrpSetup trrpProof
  print trrpWorked

  (trrpComs, ss', ww', pp') <- runZKPT (return . shaOracle) (bls)  $ do
    (coms, setup', witness') <- TRRP.proveTRRPM trrpSetup trrpWit
    lift $ print $ "Post Prover TRRP"
    bpProofM <- proveM setup' witness'
    lift $ do
      print $ "Post Prover BP"
      print $ evalScalar $ vectorPSV $ witnessBP $ witness'
      print $ scalarCP $ scalarPSV $ witnessBP $ witness'
      print $ evalScalar $ vectorPSV $ opening $ bpProofM
      print $ scalarCP $ scalarPSV $ opening $ bpProofM
    let _ = bpProofM :: Bulletproof TRRP.TranscriptTRRP (NormLinear []) PJ Fr
    return $ (coms, setup', witness', bpProofM)

  runZKPT (return . shaOracle) [] $ do
    lift $ do
      print "initCom"
      print $ initCom ss'
      print $ vectorPSV $ opening $ pp'
    pubs <- TRRP.verifyTRRPM trrpSetup trrpComs
    lift $ do
      print ("pubs", pubs)
      print $ idAp length $ responses pp'
    lift $ print "Post Verify TRRP"
    success <- verifyM pubs pp'
    lift $ print ("Worked?", success)

  ------------------------
  -- Binary Range Proof --
  
  -- (TODO must provide finite basis list to print)
  let brpSetup = BRP.setupBRP (take 200 ps) ranges
  let Just brpWit = BRP.witnessBRP brpSetup valuePSs

  brpProof <- runZKPT (return . shaOracle) bls $ proveM brpSetup brpWit
  let _ = brpProof :: BRP.BinaryRangeProof PJ Fr
  brpWorked <- runZKPT (return . shaOracle) [] $ verifyM brpSetup brpProof
  print brpWorked
  
  (brpComs, ss', ww', pp') <- runZKPT (return . shaOracle) (bls)  $ do
    (coms, setup', witness') <- BRP.proveBRPM brpSetup brpWit
    lift $ print $ "Post Prover BRP"
    bpProofM <- proveM setup' witness'
    lift $ do
      print $ "Post Prover BP"
      print $ evalScalar $ vectorPSV $ witnessBP $ witness'
      print $ scalarCP $ scalarPSV $ witnessBP $ witness'
      print $ evalScalar $ vectorPSV $ opening $ bpProofM
      print $ scalarCP $ scalarPSV $ opening $ bpProofM
    let _ = bpProofM :: Bulletproof BRP.TranscriptBRP (Norm []) PJ Fr
    return $ (coms, setup', witness', bpProofM)

  runZKPT (return . shaOracle) [] $ do
    lift $ do
      print "initCom"
      print $ initCom ss'
      print $ vectorPSV $ opening $ pp'
    pubMaybe <- BRP.verifyBRPM brpSetup brpComs
    lift $ do
      print ("pubs", pubMaybe)
      print $ idAp length $ responses pp'
    lift $ print "Post Verify BRP"
    success <- verifyM (fromJust pubMaybe) pp'
    lift $ print ("Worked?", success)
  
  return ()


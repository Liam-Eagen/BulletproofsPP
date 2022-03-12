{-# LANGUAGE NoImplicitPrelude, BangPatterns, DataKinds, OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Main where

import Protolude hiding (hash, fromStrict, put, get, option)

import Data.Binary
import Data.Binary.Get (runGetOrFail, runGet)
import Data.Binary.Put (runPut)
import Data.List (zip3, unzip3)
import Data.Maybe (catMaybes)

import Data.Curve
import Data.Curve.Weierstrass (WCurve, WPoint, WAPoint, WPPoint, WJPoint, WACurve, Point(A))
-- Somewhat slower
import Data.Curve.Weierstrass.SECP256K1 (PA, PP, PJ, Fq, Fr)

-- Untested implementation of field operation using unboxed values. Can be ~50%
-- faster
--import Data.Curve.Weierstrass.FastSECP256K1 (PA, PP, PJ, Fq, Fr)

import Data.Bits
import Data.Field.Galois (PrimeField(..)) --, sr, toP, Prime, pow)
-- Also slower
-- import Data.Digest.Pure.SHA (integerDigest, sha256)
import qualified Crypto.Hash.SHA256 as SHA (hash)
import qualified Data.ByteString.Lazy as BSL (readFile, writeFile, ByteString)
import Data.ByteString.Lazy (fromStrict)

import Utils
import Commitment
import ZKP
import Encoding 

import Bulletproof
import qualified Bulletproof.InnerProductArgument as IP
import qualified Bulletproof.NormArgument as NL

import RangeProof
import qualified RangeProof.Binary as BRP
import qualified RangeProof.TypedReciprocal as TRRP

import Data.VectorSpace ((*^), (^+^), zeroV, sumV)

import Data.Field.Eis
import Data.Curve.CM

--import Data.Field.Galois.FastPrime
--import Data.Field.Galois.FastPrime.Internal
--import GHC.Natural

--import qualified Data.Curve.FastCurve as FC
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU

import Options.Applicative

import Parse
import qualified Parse
import qualified Data.Aeson as AS

-- hash = fromInteger . integerDigest . sha256 . fromStrict
hash :: (Binary a) => ByteString -> a
hash = decode . fromStrict . SHA.hash

-- Given some seed generates a lazy list of random points
getPoints :: (Num q, Curve c f e q r, Binary q) => ByteString -> [Point c f e q r]
getPoints s = catMaybes $ rec s 0
  where
    rec s n = maybePoint (s <> show n) : rec s (n+1)
    maybePoint = pointX . hash

-- Oracle takes points returns deterministic list of scalars
shaOracle :: (WCurve c e q r, WACurve e q r, Binary r) => [WPoint c e q r] -> [r]
shaOracle ps = hashes
  where
    coords :: WACurve e q r => WAPoint e q r -> ByteString
    coords (A x y) = show x <> show y
    hashes = [ hash $ show n <> show (length ps) <> foldMap (coords . toA) ps | n <- [1..] ]

-- Hash to scalar for convenience
hashToScalar :: (PrimeField p, Binary p) => ByteString -> ByteString -> p
hashToScalar p s = hash $ p <> s

hashToScalars :: (PrimeField p, Binary p) => ByteString -> [p]
hashToScalars s = map (hashToScalar s . show) [1..]

-- TODO move
-- Stores both x and y coordinates of curve points
newtype WideEncoding c e q r = WE { getWE :: WPoint c e q r }

instance (WCurve c e q r, WACurve e q r, Binary q) => Binary (WideEncoding c e q r) where
  put (WE p) = let A x y = toA p in put x <> put y
  get = do
    x <- get
    y <- get
    return $ WE $ fromA $ A x y

-- NOTE Change this to change the types for the proofs
type ArgColl = []

-- NOTE Change this to change coordinates
-- TODO why is projective faster??
type PX = PP

-- Stores file names and command
data CmdOpts s
  = PrvOpts
    { specOpts :: s
    , witOpts :: s
    , comsOpts :: s
    , proofOpts :: s
    , verbOpts :: Int
    , writePts :: Int } 
  | VerOpts
    { specOpts :: s
    , comsOpts :: s
    , proofOpts :: s
    , verbOpts :: Int
    , writePts :: Int } 
  | TstOpts  
    { specOpts :: s
    , witOpts :: s
    , comsOpts :: s
    , proofOpts :: s
    , verbOpts :: Int
    , writePts :: Int
    } deriving (Eq, Show)

-- Command line parser
cmdParser :: (Show s, IsString s) => ParserInfo (CmdOpts s)
cmdParser = info hlp dsc
  where
    hlp = (helper <*> options)
    dsc = fullDesc <> progDesc "Prove and Verify Bulletproof++ Zero Knowledge Proofs" <> header "Bulletproof++"
    options = (subparser 
                (command "prove" (info (helper <*> prove) $ fullDesc <> progDesc "prove witness satisfies specification") <>
                 command "verify" (info (helper <*> verify) $ fullDesc <> progDesc "verify proof satisfies specification") <>
                 command "test" (info (helper <*> test) $ fullDesc <> progDesc "prove and verify witness for testing purposes")))

    spec = strArgument (showDefault <> value "schema.json" <> metavar "spec-file" <> help "json specification file")
    proof msg = strArgument (showDefault <> value "proof.bin" <> metavar "proof-file" <> help msg)
    witness = strArgument (showDefault <> value "witness.json" <> metavar "witness-file" <> help "json witness file")
    coms msg = strArgument (showDefault <> value "commits.bin" <> metavar "commits-file" <> help msg)
    verbosity = option auto (long "verbosity" <> metavar "level" <> value 0 <> help "verbosity level between 0 and 2")
    writePts = option auto (long "write-points" <> metavar "num-pts" <> value 0 <> help "write points generated from seed to file")

    -- TODO could support a repl mode?
    prove = PrvOpts <$> spec <*> witness <*> coms "binary commitment file to write" <*> proof "binary proof file to write" <*> verbosity <*> writePts
    verify = VerOpts <$> spec <*> coms "binary commitment file to read" <*> proof "binary proof file to read" <*> verbosity <*> writePts
    test = TstOpts <$> spec <*> witness <*> coms "binary commitment file to write" <*> proof "binary proof file to write" <*> verbosity <*> writePts

-- TODO better error handling?
justFail :: Text -> Maybe a -> a
justFail msg Nothing = panic msg
justFail _ (Just x) = x

jsonFail :: (StringConv s Text) => Either s a -> a
jsonFail (Left err) = panic $ toS err
jsonFail (Right x) = x

doIf :: Applicative m => Bool -> m a -> m ()
doIf True x = const () <$> x 
doIf False _ = pure ()

failIf :: Applicative m => Bool -> Text -> m ()
failIf True msg = panic $ msg
failIf False _ = pure ()

--------------------------------------------
-- Generic Proving/Verification Functions --

-- TODO type signatures. They aren't ambiguous, just long

-- Could use non monadic version
runProverWithWit rn setup wit = runZKPT (return . shaOracle) (hashToScalar rn . show) $ proveM setup wit

writeProof comsFile proofFile setup proof = do
  let (inComs, bs) = encodeProof setup proof
  BSL.writeFile (comsFile) $ runPut $ encodeCommitments inComs
  BSL.writeFile (proofFile) $ bs 

--runProver :: (RPCommitment p, NormLinearBP arg, CanCommit v s, BinaryEncodeCurve v, CanEncode c e q v s)
--          => Text -> Bool -> FilePath -> FilePath -> ByteString
--          -> SetupRP p arg v s -> [InputWitnessRP p v s]
--          -> IO (RangeProof p arg v s)
runProver err toV comsFile proofFile rn setup values = do
  let wit = justFail (err <> "invalid witness") $ witnessRP setup values
  proof <- runProverWithWit rn setup wit

  doIf toV $ do
    worked <- runZKPT (return . shaOracle) (panic $ "No Random in Verifier") $ verifyM setup proof
    print worked
    
    --runVerbose prove verify rn setup wit $ getBP proof
    runVerbose rn setup wit $ getBPRP proof

  -- Write out
  writeProof comsFile proofFile setup proof
  
  return proof

runVerifier err comsFile proofFile numComs setup = do
  -- Load proof and commitments from file
  coms <- justFail (err <> "invalid coms file") . runGet (decodeCommitments numComs) <$> BSL.readFile comsFile
  proof <- justFail (err <> "invalid proof file") . decodeProof setup coms <$> BSL.readFile proofFile

  -- Run verifier on the proof
  worked <- runZKPT (return . shaOracle) (panic $ "No random in verifier") $ verifyM setup proof
  print ("Proof from file: ", worked)

-- TODO currently runs in test mode regardless of verbosity
runVerbose rn setup wit proof = do
  (coms, ss', ww', pp') <- runZKPT (return . shaOracle) (hashToScalar rn . show) $ do
    (coms, setup', witness') <- proveRP setup wit
    lift $ print $ "Post Range Proof Prover"
    bpProofM <- proveM setup' witness'
    lift $ do
      print $ "Post Bulletproof Prover"
      print $ evalScalar $ vectorPSV $ witnessBP $ witness'
      print $ scalarCP $ scalarPSV $ witnessBP $ witness'
      print $ evalScalar $ vectorPSV $ opening $ bpProofM
      print $ scalarCP $ scalarPSV $ opening $ bpProofM
    let _ = sameType bpProofM proof
    return $ (coms, setup', witness', bpProofM)

  runZKPT (return . shaOracle) (panic $ "No random in verifier") $ do
    lift $ do
      print "initCom"
      print $ initCom ss'
      print $ vectorPSV $ opening $ pp'
    pub <- verifyRP setup coms
    lift $ do
      print ("pubs", pub)
      print $ idAp length $ responses pp'
    lift $ print "Post Range Proof Verify"
    success <- verifyM pub pp'
    lift $ print ("Worked?", success)


main :: IO ()
main = do
  -- Parse command line arguments
  cmd <- execParser cmdParser :: IO (CmdOpts FilePath)
  (toProve, toVerify, specFile, witnessFile, comsFile, proofFile, verbosity, numPointsWrite) <- do
    return $ case cmd of
      VerOpts sp    cs pr vr npts -> (False, True,  sp, "", cs, pr, vr, npts)
      PrvOpts sp wt cs pr vr npts -> (True,  False, sp, wt, cs, pr, vr, npts)
      TstOpts sp wt cs pr vr npts -> (True,  True,  sp, wt, cs, pr, vr, npts)

  print $ (proofFile, comsFile)

  -- Parse json specification file
  prs <- fmap jsonFail $ AS.eitherDecodeFileStrict' $ specFile

  -- Determine how to generate points and randomness
  -- TODO file only has 1 + 6 + 256 + 8 * 512 points
  let Ext bs rn = Parse.external prs
  ps <- either (return . getPoints . toS) (fmap (map getWE) . decodeFile) bs
  if isLeft bs && numPointsWrite > 0
    then encodeFile "points.bin" $ take numPointsWrite $ WE <$> ps
    else return ()

  -- TODO do away with this
  let (h:g:ht:_) = ps :: [PX]

  valuesParse <- if toProve
    then fmap jsonFail $ AS.eitherDecodeFileStrict' $ witnessFile
    else return []
  
  let (values, types, blinds') = unzip3 $ [(a, t, b) | PubSpec a t b _ <- fmap fromInteger <$> valuesParse]

  -- User random blinds for the inputs that don't specify
  let blindsGen = hashToScalars ("Blinding " <> toS rn) :: [Fr]
  let blinds = zipWith (flip maybe identity) blindsGen blinds'

  -- TODO better error handling?
  case prs of
    ----------------------------
    -- Reciprocal Range Proof --
    
    Parse.RecPrf SECP256K1 arg _ useTypes rngs pubs -> do
      let trrpErr = "Reciprocal Range Proof: "
      failIf (toProve && length valuesParse /= length rngs) "Different number of values and ranges"

      -- TODO these curve points are not actually used by the prover
      let valuePSPs = [ makePSP bl h n g t ht | (n, bl, t) <- zip3 values blinds types]
      let publicCommits = [(io, t, v) | PubSpec v t _ io <- pubs]

      -- Prove
      case arg of
        NL -> do
          -- NormLinear (Module in second line)
          let trrpSetup = justFail (trrpErr <> "setup failed") $ TRRP.setup ps useTypes publicCommits rngs
          print $ (TRRP.nrmLen trrpSetup, TRRP.linLen trrpSetup)
          let _ = trrpSetup :: SetupRP TRRP.TypedReciprocal (NL.NormLinear ArgColl) PX Fr
          doIf toProve $ runProver trrpErr toVerify comsFile proofFile (toS rn) trrpSetup valuePSPs
          doIf toVerify $ runVerifier trrpErr comsFile proofFile (length rngs) trrpSetup
        IP -> do
          -- InnerProduct (Module in second line)
          let trrpSetup = justFail (trrpErr <> "setup failed") $ TRRP.setup ps useTypes publicCommits rngs
          print $ (TRRP.nrmLen trrpSetup, TRRP.linLen trrpSetup)
          let _ = trrpSetup :: SetupRP TRRP.TypedReciprocal (IP.NormLinear ArgColl) PX Fr
          doIf toProve $ runProver trrpErr toVerify comsFile proofFile (toS rn) trrpSetup valuePSPs
          doIf toVerify $ runVerifier trrpErr comsFile proofFile (length rngs) trrpSetup
    
    ------------------------
    -- Binary Range Proof --
    
    BinPrf SECP256K1 arg ext cons rngs pubs -> do
      let brpErr = "Binary Range Proof: "
      failIf (length valuesParse /= length rngs) "Different number of values and ranges"
      -- Fail if any inputs specify a non zero type
      failIf (not $ all (== 0) $ types) $ brpErr <> "no typed inputs"
      
      -- Since binary range proofs only support one type, we can net the amounts
      -- here and pass a single integer net public amount
      --let publicCommits = [(io, t, v)
      let netPub = sum [ if io then -v else v | PubSpec v _ _ io <- pubs]
      let valuePSs = [ makePS bl h n g | (n, bl) <- zip values blinds]

      case arg of
        NL -> do
          -- Prove/Verify/Test NormLinear
          let brpSetup = justFail (brpErr <> "setup failed") $ BRP.setupBRP ps cons rngs netPub
          let _ = brpSetup :: SetupRP BRP.Binary (NL.NormLinear ArgColl) PX Fr
          doIf toProve $ runProver brpErr toVerify comsFile proofFile (toS rn) brpSetup valuePSs
          doIf toVerify $ runVerifier brpErr comsFile proofFile (length rngs) brpSetup
        IP -> do
          -- Prove/Verify/Test Inner Product
          let brpSetup = justFail (brpErr <> "setup failed") $ BRP.setupBRP ps cons rngs netPub
          let _ = brpSetup :: SetupRP BRP.Binary (IP.NormLinear ArgColl) PX Fr
          doIf toProve $ runProver brpErr toVerify comsFile proofFile (toS rn) brpSetup valuePSs
          doIf toVerify $ runVerifier brpErr comsFile proofFile (length rngs) brpSetup

    
    _ -> panic "Unsupported Proof Type"
  return ()

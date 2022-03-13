module RangeProof.TypedReciprocal where

import Data.Proxy
import Data.Bifunctor
import Control.Monad (replicateM)
import Data.Maybe (catMaybes)
import Data.List (unzip5, zipWith4, zipWith5, zipWith6, sortOn, foldl', mapAccumL)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.VectorSpace

import qualified Data.ByteString.Lazy as BS
import Data.Field.Galois hiding ((*^), recip)
import Data.Field.BatchInverse

import Utils
import Commitment
import ZKP

import Bulletproof
import RangeProof
import RangeProof.Internal

-------------
-- Summary --

-- See paper for detailed discussion. Implements the typed confidential
-- transaction protocol, which is (almost) a super set of the inline digit
-- and the shared digit reciprocal range proofs.
--
-- The basic organization of these range proofs isto three data commitments and
-- one blinding commitment. The prover will first compute the digit
-- representations of each value in its respective base. Then, for the shared
-- digits, the prover will sum the multiplicities for each base. 
--
-- The prover will commit to the inline mulitplicities in the M commitment and
-- the shared multiplicities and the digits in the D commitment. The verifier
-- will choose the challenge for the reciprocal and the prover will commit to
-- the reciprocals in the the R commitment (phase 2).
--
-- Then, the prover will commit to the blinding values for the
-- digits/reciprocals in the norm vector and the shared digits in the linear
-- vector as necessary. This commitment also uses the blinding procedure from
-- the paper to blind the error terms.
--
-- Control is then handed over the generic range proof protocol which will
-- invoke the appropriate bulletproof argument prover.

-------------
-- Phase 1 --

-- a is public b is private
data Phase1 a b
  = Ph1Inline Int Integer a b b a       -- Stores base, digit coeff, digit value, mult and symbol
  | Ph1Shared Int Integer a b           -- Doesn't store mults or symbol inline
  | Ph1Typing Int Bool Bool b b         -- Stores amount and type and isOutput (True output, False input) isAssumed
  deriving (Eq, Show, Functor)

instance Bifunctor Phase1 where
  bimap f g (Ph1Inline n base  b d m s) =   Ph1Inline n base  (f b) (g d) (g m) (f s)
  bimap f g (Ph1Shared n base  b d) =       Ph1Shared n base  (f b) (g d)
  bimap f g (Ph1Typing n io ia v t) = Ph1Typing n io ia (g v) (g t)

indexPh1 :: Phase1 a b -> Int
indexPh1 (Ph1Inline n _ _ _ _ _) = n
indexPh1 (Ph1Shared n _ _ _) = n
indexPh1 (Ph1Typing n _ _ _ _) = n

-- Adds zeros where multiplicity vectors are implicitly zero
getDsMs :: Num b => [Phase1 a b] -> ([b], [b])
getDsMs ph1s = unzip $ getDM <$> ph1s
  where
    getDM (Ph1Inline _ _ b d m s) = (d, m)
    getDM (Ph1Shared _ _ b d)     = (d, 0) 
    getDM (Ph1Typing _ _ _ v t)   = (t, 0)

-- Stores the data for a valid range. Do not construct directly. Consider adding
-- Field phantom type parameter to indicate characteristic check?
data RangeData = RangeData
  { base :: Integer
  , range :: Range
  , isShared :: Bool
  , isOutput :: Bool            -- If false then input
  , isAssumed :: Bool           -- If true, don't range proof only type check
  , hasBit :: Bool
  , baseCoeffs :: [Integer]
  } deriving (Eq, Show)

-- Determine how many norm components this range data will use
nrmLenRangeData :: RangeData -> Int
nrmLenRangeData rd = if isShared rd then len else max (fromInteger $ base rd - 1) len
  where len = length $ baseCoeffs rd

-- Given all the range datas, compute the total number of linear components.
-- Repeated bases are only counted once, hence the set
linLenRangeDatas :: [RangeData] -> Int
linLenRangeDatas rds = fromInteger $ 6 + sum s
  where s = S.fromList $ pred . base <$> filter isShared rds

-- Accepts field characteristic, base, range [min, max) and flags for whether
-- digits are shared and whether output (or input). Returns RangeData if the
-- range is valid
makeRangeData :: Integer -> Integer -> Range -> Bool -> Bool -> Bool -> Maybe RangeData
makeRangeData char b r@(R min max) isS isO isAss = if isValidRange then Just (RangeData b r isS isO isAss hasBit bs') else Nothing
  where
    -- It is probably possible to support negative bases without too much work,
    -- but isn't practically necessary.
    isValidRange = (max > min) && (b > 1) && max - min < char
    -- Number of base b digits
    n1 = integerLog b (max - min - 1)
    -- If range divisible by b-1, do not need bit
    hasBit = ((max - min - 1) `mod` (b - 1)) /= 0
    bs' = if isAss then [] else bs
    bs = if not hasBit
           then ((max - min - b^n1) `quot` (b - 1)) : [b^(n1 - i) | i <- [1..n1]]
           else if (max - min < 2 * b^n1)
                  then (max - min - b^n1) : [b^(n1 - i) | i <- [1..n1]]
                  else let bn1 = 1 + (max - min) `quot` (2 * (b-1)) - (b^n1 - 1) `quot` (b - 1)
                       in (max - min - bn1 * (b-1) - b^n1) : bn1 : [b^(n1 - i) | i <- [1..n1]]


-- Returns the digits for the given value and base values. If hasBit is true,
-- first digit is treated as binary.
digits :: RangeData -> Integer -> [Integer]
digits rd n = snd $ mapAccumL f n $ zip (baseCoeffs rd) $ appIf (2:) (hasBit rd) $ repeat (base rd)
  where f n (b, base) = let d = min (base - 1) $ n `quot` b in (n - d * b, d) 

-- Given the public information for a range and the witness for a range, if the
-- witness is valid returns the Phase1 data for each digit and if the range has
-- shared digits returns the multiplicities for each digit. Also accepts index
-- in list of ranges
makePhase1s :: (Show a, Integral a, Integral b) => Int -> RangeData -> b -> Maybe ([Phase1 a b], Maybe [b])
makePhase1s ind rd _ | isAssumed rd = Just ([], Nothing)                       -- If assumed, no digits
makePhase1s ind rd@(RangeData base (R min max) isShared _ False hasBit bs) n = res
  where
    nAdj = toInteger $ n - fromInteger min
    isInRange = (nAdj >= 0) && (max - min > nAdj)
    ds = digits rd nAdj
    -- NOTE this removes the zero digit and adds bit
    ms = if hasBit then head ds : (counts [1..base-1] $ tail ds) else counts [1..base-1] ds
    ns = appIf (1 :) hasBit $ [1..base-1]
    wits = [bs, ds, ms, ns]
    bases = appIf (2 :) hasBit $ repeat base
    fromInt' = bimap fromInteger fromInteger

    res = if not isInRange 
      then Nothing 
      else if isShared
             then let ph1s = fromInt' <$> zipWith4 Ph1Shared (repeat ind) bases bs ds
                  in Just (ph1s, Just $ fromInteger <$> ms)
             else let [bs', ds', ms', ns'] = padRight (maximum $ length <$> wits) 0 <$> wits
                      ph1s = fromInt' <$> zipWith6 Ph1Inline (repeat ind) bases bs' ds' ms' ns'
                  in Just (ph1s, Nothing)

-- Make Phase1s with empty witness data. Used by the verifier. Since the data is
-- empty, it cannot fail and the Just case is safe
makePhase1sVer :: (Show a, Integral a) => Int -> RangeData -> [Phase1 a ()]
makePhase1sVer n rd = ph1s
  where Just (ph1s, _) = makePhase1s n rd ()

-------------
-- Phase 2 --

-- The polynomial is (for reference):
--
-- qi bl + qi m t + (qi (e + d) + 1/qi v) t^2 + (qi r + 1/qi u) t^3 + 1/qi c t^4
--
-- Plus the modifications of ui in the type components depending on q
data Phase2 a b = Ph2 { isT :: Bool, dPh2 :: b, mPh2 :: b, uPh2 :: a, vPh2 :: a, rPh2 :: b, cPh2 :: a }
  deriving (Eq, Show, Functor)

-- Takes x and the sorted list of bases to produce the phase 2 values. Each value
-- i=0..n gets x^(2(i+1)) each reciprocal sum gets x^(2i+1). This computes the 
makePhase2s :: (Fractional a, Integral a, Fractional b, Integral b, Show a) 
            => (a -> b -> b) -> Bool -> (a, a) -> a -> M.Map Integer a -> [Phase1 a b] -> [Phase2 a b]
makePhase2s (*:) hasTypes (e, eInv) x baseMap ph1s = zipWith3 (($) . ($)) fs rs cs
  where
    -- Lets us use b ~ () for verification with the same code
    e' = e *: 1
    (ds, ss, ps, vs, fs) = unzip5 $ do
      ph1 <- ph1s
      let x' = x^(2 * (indexPh1 ph1 + 1))
      return $ case ph1 of
        Ph1Typing _ io ia v t     -> let x'' = if io then -x else x                    -- Subtract output recips
                                     in ( e' + t, 0
                                        , v,     x'', Ph2 True t 0 (if ia then 0 else x') x'')
        Ph1Inline _ base  b d m s -> let x'' = baseMap M.! base
                                     in ( e' + d, if s == 0 then 0 else e + s
                                        , 1,     x'', Ph2 False d m (x'*b) x'')
        Ph1Shared _ base  b d     -> let x'' = baseMap M.! base
                                     in ( e' + d, 0
                                        , 1,     x'', Ph2 False d 0 (x'*b) x'')

    rs = zipWith (*) ps $ batchInverse ds
    cs = zipWith (*) vs $ [ if s == 0 then 0 else eInv - s | s <- batchInverse ss ]     -- Same x powers as the reciprocal

-- NOTE cs has been scaled above already by u's and is zero if digits are not
-- inline.
err7Term :: (Functor f, Foldable f, Integral a) => f (Phase2 a a) -> a
err7Term ph2s = sum $ err7 <$> ph2s
  where err7 (Ph2 _ _ _ _ _ r c) = 2 * r * c

-- Computes public coefficients for the shared bases
makeSharedCoeffs :: (Integral a, Fractional a) => (a, a) -> [Integer] -> M.Map Integer a -> [a]
makeSharedCoeffs (e, eInv) mBases baseMap = zipWith (*) sharedXs $ map (eInv -) $ batchInverse sharedSs
  where (sharedXs, sharedSs) = unzip $ [ (baseMap M.! b, e + fromInteger s) | b <- mBases, s <- [1..b-1] ]

-------------
-- Phase 3 --

-- Stores (q^2i, q^-2i) and blinding 
-- Type a is for public data and b is for private
data Phase3 a b = Ph3 (Phase2 a b) (a, a) b
  deriving (Eq, Show, Functor)

-- This can only be called with the actual witnesses, hence the same type
makeErrorTerms :: Num a => a -> a -> [a] -> [a] -> [Phase3 a a] -> [a]
makeErrorTerms e x' sharedCs blsMs ph3s = sums $ ([0, 0, 0, aug, 0, 0] :) $ errorTerms <$> ph3s
  where
    -- From linear terms
    aug = 2 * dotZip sharedCs blsMs
    errorTerms (Ph3 (Ph2 isT d m u v r c) (q2, _) bl) = [err0, err1, err2, err3, err4, err6]
      where
        rC = if (isT) then x' * (u + q2) else u
        dC = v + q2 * e
        err0 = q2 * bl^2            -- NOTE this goes in scalar component
        err1 = 2 * q2 * m * bl
        err2 = q2 * m^2 + 2 * bl * (q2 * d + dC)
        err3 = 2 * (bl * (q2 * r + rC) + m * (q2 * d + dC))
        err4 = (q2 * d^2 + 2 * d * dC) + 2 * (bl * c + m * (q2 * r + rC))
        err6 = (q2 * r^2 + 2 * r * rC) + 2 * c * d
        -- err7 already known

-- TODO just accept the setup object?
makePublicConsts :: (Fractional a, Integral a, Show a) => (a, a) -> a -> a -> (a, a) -> a
--                 -> Bool -> [Bool] -> [Range] -> [(Bool, Integer, Integer)] -> [Phase2 a b] -> RPWitness a
                 -> Bool -> [RangeData] -> [(Bool, Integer, Integer)] -> [Phase2 a b] -> RPWitness a
makePublicConsts (e, eInv) x x' (q0, q0Inv) t hasTypes rds pubVT ph2s = RPW (z + sum ts0) [] ts1
  where
    -- Values occur on t^5, remove public inputs if using types
    isAs = [ (isAssumed rd) | rd <- rds ]
    mins = replaceIf isAs 0 $ fromInteger . minRange . range <$> rds
    z = -2 * t^5 * (dotZip mins $ powers' $ x^2) - if hasTypes then 2 * t^5 * x * pubSum else 0
    (ts0, ts1) = unzip $ publicTerms <$> zip3 ph2s (powers' q0) (powers' $ q0Inv)

    (pubOuts, pubTs, pubVs) = unzip3 pubVT
    pubRs = batchInverse $ map (e +) $ fromInteger <$> pubTs
    pubSum = sum [appIf negate isOut $ r * fromInteger v | (isOut, v, r) <- zip3 pubOuts pubVs pubRs]

    -- Inline/Shared digits
    publicTerms ((Ph2 isT _ _ u v _ c), q2, qInv2) = (p2, p)
      where
        (rC, p2C) = if (isT) 
          then ( x' * (qInv2 * u + 1), 0 )
          -- TODO only if base is defined here
          else ( qInv2 * u, (2 * q2 + 2 * eInv * v) )
        p = t^2 * (e + qInv2 * v) + t^3 * rC + t^4 * (qInv2 * c)
        p2 = q2 * (p^2) + t^5 * p2C

-------------------------
-- Prover and Verifier --

-- For n inputs, we have 4 + n commitments
data TranscriptTRRP v s
  = TTRRP 
  { ht :: Bool
  , ia :: [Bool]       -- No x power for these
  , commits :: [v]
  , eChallenge :: s
  , xChallenge :: s
  , q0Challenge :: s
  , tChallenge :: s 
  } deriving (Eq, Show)

instance Bifunctor TranscriptTRRP where
  bimap f g (TTRRP ht ia coms e x q0 t) = TTRRP ht ia (f <$> coms) (g e) (g x) (g q0) (g t)

instance Opening TranscriptTRRP where
  openWith (TTRRP hasTypes isAs (blCom:rCom:dmCom:mCom:nComs) e x q0 t) = c
    where
      ss = (*) (2 * t^5) <$> inputCoeffs hasTypes isAs x q0
      c = dotWith ss nComs .: dotWith [1, t, t^2, t^3] [blCom, mCom, dmCom, rCom]

instance RPOpening TranscriptTRRP where
  type SetupRP TranscriptTRRP = SetupTRRP
  type WitnessRP TranscriptTRRP = WitnessTRRP
  type InputWitnessRP TranscriptTRRP = PedersenScalarPair

  witnessRP = witnessTRRP
  proveRP = proveTRRPM
  verifyRP = verifyTRRPM
  infoRP s = (4, nrmLen s, linLen s)

type BPTRRP = Bulletproof TranscriptTRRP
type TypedReciprocal = TranscriptTRRP

-- TODO: improvements
--
-- Does not support eliminating the M commitment in the case that all the inputs
-- use shared digits.
--
-- Currently the hasTypes = False just drops types from the norm vector, it
-- still leaves the error term for types in the linear vector. This allows
-- passing typed commitments but ignores the types, treating all amounts as the
-- same type. Doesn't affect proof size for 8 or more digits.

-- This abstracts interactions with the specifics of the proof system as much as
-- possible, i.e. group elements, commitment function, etc.
data SetupTRRP arg v s = STRRP
  { hasTypes :: Bool                                -- If False, modify input coeffs
  , sortedSharedBases :: [Integer]
  , nrmLen :: Int
  , linLen :: Int
  , publicAmounts :: [(Bool, Integer, Integer)]     -- Stores public amounts (isOutput, v, t)
  , processedRanges :: [RangeData]
  , baseMapSTRRP :: s -> M.Map Integer s            -- Returns mapping of input powers to bases
  , qPowersTRRP :: s -> [s] 
  , comSTRRP :: RPWitness s -> v
  , psvSTRRP :: s -> [s] -> RPWitness s -> BPC arg v s
  , setupSTRRP :: s -> [s] -> RPWitness s -> TypedReciprocal v s -> Setup (BPTRRP arg) v s
  }

-- We want to drop the commitment that are assumed. Typically used in
-- conjunction with inputs that have already been proven
inputCoeffs :: Integral a => Bool -> [Bool] -> a -> a -> [a]
inputCoeffs hasTypes assumed x q0 = appIf (zipWith (+) (powers' $ q0)) hasTypes $ xPowers
  where xPowers = zipWith cond assumed $ powers' $ x^2
          where cond f x = if f then 0 else x

-- Accepts basis points, flag for whether to use types, public values, and
-- RangeData. Constructs the setup object
setup :: (CanCommit v s, NormLinearBP arg, BPCollection (Coll arg)) 
          => [v] -> Bool -> [(Bool, Integer, Integer)] -> [RangeData] -> Maybe (SetupTRRP arg v s)
setup (h : g : ps) hasTypes pubVT rangeDatas = do
  let (bases, isSs, isAs) = unzip3 [(base rd, isShared rd, isAssumed rd) | rd <- rangeDatas]
  let anyHasBit = any hasBit $ dropIf isAs $ rangeDatas
  let anySharedHasBit = any (uncurry $ (&&) . hasBit) $ dropIf isAs $ zip rangeDatas isSs

  -- Each base, and each shared base, gets a unique x power. Common bases share
  -- an x power, including base 2 for the bit of other ranges/bases
  let sortedPairs = sortOn snd $ dropIf isAs $ zip isSs bases
  let mBases = deDup $ appIf (2 :) anySharedHasBit $ map snd $ filter fst sortedPairs
  let sortedBases = deDup $ appIf (2 :) anyHasBit $ map snd sortedPairs

  -- Allocate one nrm term per digit, one term per type and (b-1) linear terms per shared base
  let nrmLen = sum $ map (appIf succ hasTypes . length . baseCoeffs) rangeDatas
  let linLen = fromInteger $ 6 + sum (map pred mBases)
  (hs, ps') <- splitAtMaybe linLen ps
  gs <- takeMaybe nrmLen ps'

  -- Utility functions
  let com (RPW sc lin nrm) = commitRPW sc g lin hs nrm gs
  let makeBaseMap x = M.fromList $ zip sortedBases (powers'' (x^3) (x^2))
  let psv q cs (RPW sc lin nrm) = makePSV sc g $ makeNormLinearBPList q cs nrm gs lin hs
  let qPowers = qPowers' $ proxy' $ vectorPSV $ psv 1 empty' zeroV
  let setup' q cs pub init = SBP (psv q cs zeroV) init bpPub $ fst $ optimalWitnessSize pubVec nrmLen linLen
        where bpPub@(PSV _ pubVec) = psv q cs pub
  
  return $ STRRP hasTypes mBases nrmLen linLen pubVT rangeDatas makeBaseMap qPowers com psv setup'

data WitnessTRRP v s = WTRRP [PedersenScalarPair v s] [Phase1 s s] [(Integer, [s])]
  deriving (Eq, Show)

-- The shared bases are Just multiplicites. Add all multiplicities of like
-- bases
baseMss :: (Show a, Num a) => [Maybe [a]] -> [Integer] -> [Bool] -> [(Integer, [a])]
baseMss mssMaybe bases bits = M.assocs $ M.fromListWith (zipWith (+)) $ do
  (bit, base, ms) <- catMaybes $ zipWith3 (\a b c -> (a, b, ) <$> c) bits bases mssMaybe
  if bit
    then [(2, [head ms]), (base, tail ms)]
    else [(base, ms)]

witnessTRRP :: (CanCommit v s, NormLinearBP arg) => SetupTRRP arg v s -> [PedersenScalarPair v s] -> Maybe (WitnessTRRP v s)
witnessTRRP (STRRP hasTypes _ _ _ pubAmnts rds _ _ _ _ _) nPSs = do
  let (vs, ts) = unzip $ dup scalarCP . pairPSP <$> nPSs 
  
  -- If uses types, then check that the values of each type add up correctly
  let pubSums =  M.fromListWith (+) [ (fromInteger $ t, fromInteger $ appIf negate io v) | (io, t, v) <- pubAmnts ]
  let typeSums = M.fromListWith (+) [ (t, appIf negate (isOutput r) v) | (t, v, r) <- zip3 ts vs rds ] 
  if hasTypes && not (all (== 0) $ M.elems $ M.unionWith (+) pubSums typeSums)
    then error $ show $  M.unionWith (+) pubSums typeSums
    else Just ()

  -- Make phase1 data and organize types to come first, if present
  (ph1ss, mssMaybe) <- fmap unzip $ sequence $ zipWith3 makePhase1s [0..] rds vs
  let types = zipWith5 Ph1Typing [0..] (isOutput <$> rds) (isAssumed <$> rds) vs ts
  let ph1s = appIf (types ++) hasTypes $ concat ph1ss
  return $ WTRRP nPSs ph1s $ baseMss mssMaybe (base <$> rds) (hasBit <$> rds)

-- Produces linear coefficient vector for bulletproof
makeBpCoeffs :: PrimeField a => Bool -> a -> a -> a -> a -> [a] -> [a]
makeBpCoeffs hasTypes x' r0 r1 t cs = ct : (rs*t) : (rs*t^2) : (rs*t^3) : (r0*t^4) : (rs*t^6) : cs'
  where
    rs = r0 * r1
    cs' = (*) (2 * t^3) <$> cs
    ct = if hasTypes then -x' else 0

-- Monadic prover
proveTRRPM :: (CanCommitM v s m, NormLinearBP arg)
          => SetupTRRP arg v s -> WitnessTRRP v s -> m ([v], Setup (BPTRRP arg) v s, Witness (BPTRRP arg) v s)
proveTRRPM (STRRP hasTypes mBases nrmLen linLen pubVT rds makeBaseMap' qPowers commit' makePSV' setup') (WTRRP nPSs ph1s baseMss) = do
  -- Phase 1: commit to digits and multiplicities
  let numTerms = 3
  let isAs = isAssumed <$> rds
  let (mBases, msShared) = concat <$> unzip baseMss
  let (ds, msInline) = getDsMs ph1s

  (nWits, nComs) <- unzip <$> map (idAp commit') <$> mapM scalarPairRPW' nPSs
  (dmWit, dmCom) <- idAp commit' <$> blindWitness numTerms 2 msShared ds
  (mWit, mCom) <- idAp commit' <$> blindWitness numTerms 1 [] msInline 
  
  T3 e x r0 <- oracle' (dmCom : mCom : nComs)
  let [eInv, r0Inv] = batchInverse [e, r0]

  -- Phase 2: compute and commit to recips
  let baseMap = makeBaseMap' x
  let ph2s = makePhase2s (*) hasTypes (e, eInv) x baseMap ph1s
  let err7 = r0Inv * negate (err7Term ph2s)
  (rWit, rCom) <- idAp commit' <$> blindErrWitness numTerms [err7] [] (rPh2 <$> ph2s)
 
  T3 q x' r1 <- oracle' [rCom]
  let q0 = head $ qPowers q
  let [qInv, q0Inv, r1Inv] = batchInverse [q, q0, r1]
  let sharedCs = makeSharedCoeffs (e, eInv) mBases baseMap
  let tC = if hasTypes then x' else 0

  -- Phase 3: compute and commit to error terms and norm blinding
  blBls@(RPW _ blsLin blsNrm) <- RPW 0 <$> replicateM (linLen - 5) random <*> replicateM nrmLen random
  let blType:blsMs = blsLin

  let nWitSum@(RPW _ [_, inputBl] _) = sumV (zipWith (*^) (inputCoeffs hasTypes isAs x q0) nWits)
  let ph3s = zipWith3 Ph3 ph2s ( zip (qPowers q) (qPowers qInv) ) blsNrm
  let errs = makeErrorTerms e x' sharedCs blsMs ph3s
  (blWit, blCom) <- idAp commit' <$> blindBlindingTerm blBls tC (r0, r0Inv) (r1, r1Inv) errs [mWit, dmWit, rWit] inputBl
  t <- head <$> oracle [blCom]
 
  -- Phase 4: setup bulletproof
  let pub = makePublicConsts (e, eInv) x x' (q0, q0Inv) t hasTypes rds pubVT ph2s
  let wit = pub ^+^ blWit ^+^ t*^mWit ^+^ (t^2)*^dmWit ^+^ (t^3)*^rWit ^+^ (2 * t^5) *^ nWitSum

  let coms = blCom : rCom : dmCom : mCom : nComs
  let bpCom = TTRRP hasTypes isAs coms e x q0 t
  let bpCoeffs = makeBpCoeffs hasTypes x' r0 r1 t sharedCs
  return (coms, setup' q bpCoeffs pub bpCom, WBP $ makePSV' q bpCoeffs wit)

-- Monadic verifier. 
verifyTRRPM :: (CanCommitM v s m, NormLinearBP arg) => SetupTRRP arg v s -> [v] -> m (Setup (BPTRRP arg) v s)
verifyTRRPM (STRRP hasTypes mBases _ _ pubVT rds makeBaseMap' qPowers _ _ setup') coms = do
  -- Initialize ph1s to be empty
  let ph1ss = zipWith makePhase1sVer [0..] rds
  let types = zipWith (\ind rc -> Ph1Typing ind (isOutput rc) (isAssumed rc) () ()) [0..] rds
  let ph1s = appIf (types ++) hasTypes $ concat ph1ss

  -- Get commitments and compute challenges
  let (blCom : rCom : dmCom : mCom : nComs) = coms
  T3 e x r0 <- oracle' (dmCom : mCom : nComs)
  T3 q x' r1 <- oracle' [rCom]
  let q0 = head $ qPowers q
  t <- head <$> oracle [blCom]
  let [eInv, qInv, q0Inv] = batchInverse [e, q, q0]
  let baseMap = makeBaseMap' x
  let ph2s = makePhase2s (flip const) hasTypes (e, eInv) x baseMap ph1s
  let pub = makePublicConsts (e, eInv) x x' (q0, q0Inv) t hasTypes rds pubVT ph2s
  
  -- Prepare bulletproof
  let bpCoeffs = makeBpCoeffs hasTypes x' r0 r1 t $ makeSharedCoeffs (e, eInv) mBases baseMap
  return $ setup' q bpCoeffs pub (TTRRP hasTypes (isAssumed <$> rds) coms e x q0 t)

-- TODO : Batch Verifier
-- Batch verifier accepts a list of proofs as witness, takes a random linear
-- combination, computes the scalars in the same manner as the bulletproof, and
-- and then performs a single ec inner product to verify all of them at once.

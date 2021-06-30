{-# LANGUAGE TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts, BangPatterns #-}

module RangeProof.TypedReciprocal where

import Data.Bifunctor
import Control.Monad (replicateM)
import Data.Maybe (catMaybes, fromJust)
import Data.List (uncons, unzip4, unzip5, zipWith5, zipWith6, sortOn, foldl')
import qualified Data.Map as M
import Data.VectorSpace

import Utils
import Commitment
import NormLinearProof

import RangeProof.Internal

-- NOTE see paper for complete description
--
-- Implements the superset of inline reciprocal range proofs, shared reciprocal
-- range proofs, and typed confidential transactions. Takes a colletion of
-- commitments each of which: is tx input or output, has inline or shared digits,
-- has a range [A, B) B - A < p and has an integer base b s.t. 1 < b < p. Each
-- commitment has a value and a type, but typed conservation of money can be
-- disabled.
--
-- To show that all the digits of every number belong to the correct set of
-- symbol values (0..b-1 for base b) we use the reciprocal technique and show
-- that, given ds and ms commitments:
--
-- sum[i=0..n-1] 1/(e + d[i]) - sum[j=1..b-1] m[j] ( 1/(e + j) - 1/e ) = n/e
--
-- For typed conservation of money we use a similar argument and show that for
-- sets I and O and commitments to vs and ts:
--
-- sum[(v,t) in I] v/(e + t) - sum[(v,t) in O] v/(e + t) = 0
--
-- In both cases we want to show 


-- Implements the reciprocal range proof construction for typed inputs. That is,
-- given a collection of inputs containing a value and a type, we check that
-- every value lies in the appropriate range and that the sum of the input
-- amounts of each type equals the amounts of each type. We do this in zero
-- knowledge with respect to the type of each value and which/how many types are
-- involved in the transaction, besides the obvious restriction that there
-- cannot be more types that the total number of inputs and outputs and whatever
-- the fee amount is (TODO add this).
--
-- This is accomplished buy summing:
--
-- sum[i] v[i] / (e - t[i]) - sum[o] v[o] / (e - t[o]) = 0
--
-- Where (t[i], v[i]) are the inputs and (t[o], v[o]) are the outputs. More
-- concretely, we can piggy back on the existing range proof structure and add
-- one linear term where all the types a will be cannonically committed to and
-- then append the vector of types to the d vector and the vector of reciprocals
-- to the r vector.
--
-- We then scale the inputs by (x^i + q^j) to balance the corresponding products
--
-- (t - e) r = v
--
-- We will then scale the types linearly by a different linear vector added to
-- the reciprocals to balance the sum of types by these weights on the values,
-- with the overall sum scaled to lie on linearly independent q powers. We use
-- the basic technique
--
-- (Q v + q^a (Q + X Q^-1) 1) y + (Q (e - t) + q^b Q^-1 1) y^3
--
-- This puts all the data on the <r, d> term (y^4) and avoids adding any new
-- error terms. So long as q^a and q^b are chosen so that the types do not
-- overlap with the rest of the q powers, this is sound.
--
-- NOTE if the ranges used include zero anyone can create/destroy a value of
-- any type with balance zero. If this is undesirable, start the range at 1.

-------------
-- Phase 1 --

--data Phase1 a = Ph1Inline { bit :: Bool, b :: a, d :: a, m :: a, s :: a }
data Phase1 a 
  = Ph1Inline Integer a a a a       -- Stores base, digit coeff, digit value, mult and symbol
  | Ph1Shared Integer a a           -- Doesn't store mults or symbol inline
  | Ph1Typing Bool a a              -- Stores amount and type and isOutput (True output, False input)
  deriving (Eq, Show, Functor)

isTyping :: Phase1 a -> Bool
isTyping (Ph1Typing _ _ _) = True
isTyping _ = False

-- NOTE assumes type : digits per range
getDsMs :: Integral a => [[Phase1 a]] -> ([a], [a])
getDsMs ph1ss = unzip $ getDM <$> concat (types : values)
  where
    types = map head ph1ss
    values = map tail ph1ss
    getDM (Ph1Inline base  b d m s) = (d, m)
    getDM (Ph1Shared base  b d)     = (d, 0) 
    getDM (Ph1Typing isOut v t)     = (t, 0)

data RangeData = RangeData
  { base :: Integer
  , range :: Range
  , isShared :: Bool
  , isOutput :: Bool
  , hasBit :: Bool
  , baseCoeffs :: [Integer]
  }

processRanges :: Integer -> Range -> Maybe (Bool, [Integer])
processRanges b (R min max) = if isValidRange then Just (hasBit, bs) else Nothing
  where
    -- TODO characteristic
    isValidRange = (max > min) && (b > 1)
    n1 = integerLog b (max - min - 1)
    hasBit = ((max - min - 1) `mod` (b - 1)) /= 0
    bs = if not hasBit
           then ((max - min - b^n1) `quot` (b - 1)) : [b^(n1 - i) | i <- [1..n1]]
           else if (max - min < 2 * b^n1)
                  then (max - min - b^n1) : [b^(n1 - i) | i <- [1..n1]]
                  else let bn1 = 1 + (max - min) `quot` (2 * (b-1)) - (b^n1 - 1) `quot` (b - 1)
                       in (max - min - bn1 * (b-1) - b^n1) : bn1 : [b^(n1 - i) | i <- [1..n1]]

-- Returns the digits for the given value and base values. If hasBit is true,
-- first digit is treated as binary.
digits :: Bool -> Integer -> [Integer] -> Integer -> [Integer]
digits True base (b:bs) n = bit : digits False base bs n'
  where (bit, n') = if n > b then (1, n - b) else (0, n)
-- Kinda awkward. 
digits False base bs n = reverse $ fst $ foldl' (uncurry f) ([], n) bs
  where f rs n b = let d = min (base-1) $ n `quot` b in (d : rs, n - d * b) 

makePhase1s :: Integral a => RangeData -> a -> Maybe ([Phase1 a], Maybe [a])
makePhase1s (RangeData base (R min max) isShared _ hasBit bs) n = if not isInRange then Nothing else if isShared
  then let ph1s = fmap fromInteger <$> zipWith3 Ph1Shared bases bs ds
       in Just (ph1s, Just $ fromInteger <$> ms)
  else let ((bs', ds'), (ms', ns')) = dup unzip $ unzip $ zipWithDef'' (,) (0, 0) (0, 0) (zip bs ds) (zip ms ns)
           ph1s = fmap fromInteger <$> zipWith5 Ph1Inline bases bs' ds' ms' ns'
       in Just (ph1s, Nothing)
  where 
    nAdj = toInteger $ n - fromInteger min
    isInRange = (nAdj >= 0) && (max - min > nAdj)
    ds = digits hasBit base bs nAdj
    -- NOTE this removes the zero digit
    ms = if hasBit then head ds : (counts [1..base-1] $ tail ds) else counts [1..base-1] ds
    ns = appIf (1 :) hasBit $ [1..base-1]
    bases = appIf (2 :) hasBit $ repeat base

-------------
-- Phase 2 --

-- Eqn: qi m y + (qi r + 1/qi u) y^3 + (qi (e + d) + 1/qi v) y^5 + 1/qi c y^7
--
-- The y^3 term is modified for types so that u = q * (u + qi^2).
-- Otherwise, the phase 2 stores all the information except for q, y to encode
-- the polynomial.
data Phase2 a = Ph2 { ph1 :: Phase1 a, d :: a, m :: a, u :: a, v :: a, r :: a, c :: a }
  deriving (Eq, Show, Functor)

-- Takes x and the sorted list of bases to produce the phase 2 values. Each value
-- i=0..n gets x^(2(i+1)) each reciprocal sum gets x^(2i+1). This computes the 
makePhase2s :: (Fractional a, Integral a) => (a, a) -> a -> M.Map Integer a -> [[Phase1 a]] -> [Phase2 a]
makePhase2s (e, eInv) x baseMap ph1ss = zipWith3 (($) . ($)) fs rs cs
  where
    types = map ( (:[]) . head ) ph1ss
    values = map tail ph1ss

    (ds, ss, ps, vs, fs) = unzip5 $ do
      (ph1s, x') <- (zip types $ powers' $ x^2) ++ (zip values $ powers' $ x^2)
      ph1 <- ph1s
      return $ case ph1 of
        Ph1Typing isOut v t     -> let x'' = if isOut then -x else x                    -- Subtract output recips
                                   in (e + t, 0,     v, x'', Ph2 ph1 t 0 x'     x'') 
        Ph1Inline base  b d m s -> let x'' = baseMap M.! base
                                   in (e + d, if s == 0 then 0 else e + s, 1, x'', Ph2 ph1 d m (x'*b) x'')
        Ph1Shared base  b d     -> let x'' = baseMap M.! base
                                   in (e + d, 0,     1, x'', Ph2 ph1 d 0 (x'*b) x'')

    rs = zipWith (*) ps $ batchInverse ds
    cs = zipWith (*) vs $ [ if s == 0 then 0 else eInv - s | s <- batchInverse ss ]     -- Same x powers as the reciprocal

-- Computes scalar for the r commitment to cancel the y^12 term
scalarError :: Integral a => [Phase2 a] -> a
scalarError ph2s = sum $ scErr <$> ph2s
  where
    -- NOTE cs has been scaled above already by us and is zero if digits are not
    -- inline.
    scErr (Ph2 _ d _ _ _ _ c) = d * c

-- Computes public coefficients for the shared bases
makeSharedCoeffs :: (Integral a, Fractional a) => (a, a) -> [Integer] -> M.Map Integer a -> [a]
makeSharedCoeffs (e, eInv) mBases baseMap = zipWith (*) sharedXs $ map (eInv -) $ batchInverse sharedSs
  where (sharedXs, sharedSs) = unzip $ [ (baseMap M.! b, e + fromInteger s) | b <- mBases, s <- [1..b-1] ]

-------------
-- Phase 3 --

-- Stores (q^2i, q^-2i) and blinding 
data Phase3 a = Ph3 (Phase2 a) (a, a) a
  deriving (Eq, Show)

makeLinearTerms :: Num a => a -> a -> [Phase3 a] -> [a]
makeLinearTerms e q ph3s = let (a,b,c,d) = sumQuad $ errorTerms <$> ph3s in [a,b,c,d]
  where
    errorTerms (Ph3 (Ph2 ph1 d m u v r c) (q2, _) bl) = (err2, err4, err6, err10)
      where
        rC = if (isTyping ph1) then q * (u + q2) else u
        dC = v + q2 * e
        err2  = q2 * m^2
        err4  = 2 * (q2 * m * r + m * rC)
        err6  = q2 * ( r^2 + 2 * d * m ) + 2 * r * rC + 2 * m * dC
        err10 = q2 * d^2 + 2 * d * dC + 2 * r * c

makePublicConsts :: (Fractional a, Integral a) => (a, a) -> a -> a -> (a, a)
                 -> [Range] -> [(Bool, Integer, Integer)] -> [Phase3 a] -> RPWitness a
makePublicConsts (e, eInv) x q (y, yInv) rngs pubVT ph3s = RPW 0 (z + sum ts0) [pubSum] ts1
  where
    -- Implicitly scaled by y^9 to get y^8 (same as inputs)
    -- Only add back to the digit sums (the x powers) not the products (q powers)
    z = -2 * yInv * (dotZip (fromInteger . minRange <$> rngs) $ powers' $ x^2)
    (ts0, ts1) = unzip $ publicTerms <$> ph3s
  
    (pubOuts, pubVs, pubTs) = unzip3 pubVT
    pubRs = batchInverse $ map (e +) $ fromInteger <$> pubTs
    pubSum = sum [appIf negate isOut $ r * fromInteger v | (isOut, v, r) <- zip3 pubOuts pubVs pubRs]

    -- Inline/Shared digits
    publicTerms (Ph3 (Ph2 ph1 d _ u v _ c) (q2, qInv2) _) = (p2, p)
      where
        (rC, p2C) = if (isTyping ph1) 
          then ( q * (qInv2 * u + 1), 0 )
          -- TODO only if base is defined here
          else ( qInv2 * u, (2 * q2 + 2 * eInv * v) * yInv )
        p = y^3 * rC + y^5 * (e + qInv2 * v) + y^7 * (qInv2 * c)
        p2 = q2 * (yInv^9 * p^2) + p2C

-------------------------
-- Prover and Verifier --

data TranscriptTRRP v s = TTRRP { ht :: Bool, commits :: [v], eChallenge :: s, xChallenge :: s
                              , qChallenge :: s, yChallenge :: s, tChallenge :: s }
                              deriving (Eq, Show)

instance Bifunctor TranscriptTRRP where
  bimap f g (TTRRP ht coms e x q y t) = TTRRP ht (f <$> coms) (g e) (g x) (g q) (g y) (g t)

instance Commitment TranscriptTRRP where
  commitWith (TTRRP hasTypes (bl2:bl1:rCom:dmCom:mCom:nComs) e x q y t) (*:) (+:) z = dotWith (*:) (+:) ss nComs p
    where
      ss = (*) (2 * recip y) <$> inputCoeffs hasTypes x q      -- Scale scalar by y^9, divide by 1/y to get back to y^8
      p = sumWith (+:) [(t^2) *: bl2, t *: bl1, y *: mCom, (y^3) *: rCom, (y^5) *: dmCom] z

type BPTRRP = Bulletproof TranscriptTRRP (NormLinear [])

-- TODO this produces a range proof for every commitment and does not support
-- eliminating the extra error terms in the case that all digits are shared.
-- 
-- Currently the hasTypes = False just drops types from the norm vector, it
-- still leaves the error term for types in the linear vector. This allows
-- passing typed commitments but ignores the types, treating all amounts as the
-- same type. Doesn't affecto proof size for 8 or more digits.


-- This handles all the interactions with the actual basis elements.
data SetupTRRP v s = STRRP
  { hasTypes :: Bool                                -- If False, modify input coeffs
  , sortedSharedBases :: [Integer]
  , publicAmounts :: [(Bool, Integer, Integer)]     -- Stores e.g. public fee amounts (v, t)
  , processedRanges :: [RangeData]
  , baseMapSTRRP :: s -> M.Map Integer s            -- Returns mapping of input powers to bases
  , comSTRRP :: RPWitness s -> v
  , psvSTRRP :: s -> s -> [s] -> RPWitness s -> PedersenScalarVector (NormLinear []) v s
  }

-- If no types, do not add the q^2 powers
inputCoeffs :: Integral a => Bool -> a -> a -> [a]
inputCoeffs hasTypes x q = appIf (zipWith (+) (powers' $ q^2)) hasTypes $ powers' $ x^2

setupTRRP :: (CanCommit v s) => [v] -> Bool -> [(Bool, Integer, Integer)] -> [(Integer, Range, Bool, Bool)] -> Maybe (SetupTRRP v s)
setupTRRP (h : g : ps) hasTypes pubVT setupComs = do
  let (bases, ranges, isShareds, isOuts) = unzip4 setupComs

  -- Extract base values for every commitment [(Bool, [Integer])]
  (bits, bss) <- fmap unzip $ sequence $ zipWith processRanges bases ranges
  let anyHasBit = any id bits
  let anySharedHasBit = any (uncurry (&&)) $ zip bits isShareds

  -- Gives a sorted list of all bases and all shared bases present in proof 
  let sortedPairs = sortOn snd $ zip isShareds bases
  let mBases = deDup $ appIf (2 :) anySharedHasBit $ map snd $ filter fst sortedPairs
  let sortedBases = deDup $ appIf (2 :) anyHasBit $ map snd sortedPairs

  -- Allocate one nrm term per digit, one term per type and (b-1) linear terms per shared base
  let nrmLen = sum $ map (appIf succ hasTypes . length) bss
  let linLen = fromInteger $ 5 + sum (map pred mBases)
  
  (hs, ps') <- splitAtMaybe linLen ps
  gs <- takeMaybe nrmLen ps'

  let com (RPW bl sc lin nrm) = commitRPW bl h sc g lin hs nrm gs
  let makeBaseMap x = M.fromList $ zip sortedBases (powers'' (x^3) (x^2))

  -- The scalar is scaled by y^9 to move the r term (y^3) to y^12. This is done
  -- by scaling the linear and norm by 1/y^9.
  let psv q yInv cs (RPW bl sc lin nrm) = makePSV bl h sc g $ makeNormLinearWithScalar (yInv^9) q cs nrm gs lin hs

  return $ STRRP hasTypes mBases pubVT (zipWith6 RangeData bases ranges isShareds isOuts bits bss) makeBaseMap com psv

data WitnessTRRP v s = WTRRP [PedersenScalarPair v s] [[Phase1 s]] [(Integer, [s])]
  deriving (Eq, Show)

-- The shared bases are Just multiplicites. Add all multiplicities of like
-- bases
baseMss :: Num a => [Maybe [a]] -> [Integer] -> [Bool] -> [(Integer, [a])]
baseMss mssMaybe bases bits = M.assocs $ M.fromListWith (zipWith (+)) $ do
  (bit, base, ms) <- catMaybes $ zipWith3 (\a b c -> (a, b, ) <$> c) bits bases mssMaybe
  if bit
    then [(2, [head ms]), (base, tail ms)]
    else [(base, ms)]

witnessTRRP :: CanCommit v s => SetupTRRP v s -> [PedersenScalarPair v s] -> Maybe (WitnessTRRP v s)
witnessTRRP (STRRP hasTypes mBases _ rcs _ _ _) nPSs = do
  let (vs, ts) = unzip $ dup scalarCP . pairPSP <$> nPSs 
  (ph1ss, mssMaybe) <- fmap unzip $ sequence $ zipWith makePhase1s rcs vs
  let ph1ss' = appIf (zipWith (:) (zipWith3 Ph1Typing (isOutput <$> rcs) vs ts)) hasTypes $ ph1ss
  return $ WTRRP nPSs ph1ss' $ baseMss mssMaybe (base <$> rcs) (hasBit <$> rcs)

-- Produces linear coefficient vector for bulletproof
makeBpCoeffs :: Integral a => Bool -> a -> (a, a) -> a -> [a] -> [a]
makeBpCoeffs hasTypes q (y, yInv) tInv cs = ct : (-tInv*y^2) : (-tInv*y^4) : (-tInv*y^6) : (-tInv*y^10) : cs'
  where
    cs' = (*) (2 * y^3) <$> cs
    ct = if hasTypes then -q*y^9 else 0

-- Monadic prover
proveTRRPM :: CanCommitM v s m
          => SetupTRRP v s -> WitnessTRRP v s -> m ([v], Setup BPTRRP v s, Witness BPTRRP v s)

proveTRRPM (STRRP hasTypes mBases pubVT rcs makeBaseMap' commit' makePSV') (WTRRP nPSs ph1ss baseMss) = do
  -- Phase 1: commit to digits and multiplicities
  let ranges = map range rcs
  let (mBases, msShared) = concat <$> unzip baseMss
  let (ds, msInline) = getDsMs ph1ss
  let len = length ds

  (nWits, nComs) <- unzip <$> map (idAp commit') <$> mapM scalarPairRPW nPSs
  (dmWit, dmCom) <- idAp commit' <$> blindedRPW 0 (0 : 0 : 0 : 0 : 0 : msShared) ds
  (mWit, mCom) <- idAp commit' <$> normRPW 0 msInline
  ex <- take 2 <$> oracle (dmCom : mCom : nComs)
  let [e, x] = ex
  let eInv = recip e

  -- Phase 2: compute and commit to recips
  let baseMap = makeBaseMap' x
  let ph2s = makePhase2s (e, eInv) x baseMap ph1ss
  (rWit, rCom) <- idAp commit' <$> normRPW (scalarError ph2s) [ r | Ph2 _ _ _ _ _ r _ <- ph2s]
  q <- head <$> oracle [rCom]
  let sharedCs = makeSharedCoeffs (e, eInv) mBases baseMap

  -- Phase 3: compute and commit to error terms and norm blinding
  bl1Sc <- random
  blsMs <- replicateM (length msShared) random
  blType <- random
  blsNrm <- replicateM len random
  let ph3s = zipWith3 Ph3 ph2s ( zip (powers' $ q^2) (powers' $ (recip q)^2) ) blsNrm
  (bl1Wit, bl1Com) <- idAp commit' <$> blindedRPW bl1Sc (blType : makeLinearTerms e q ph3s ++ blsMs) blsNrm
  y <- head <$> oracle [bl1Com]
  let yInv = recip y

  -- Phase 4: compute and commit to error term blinding
  let pub = makePublicConsts (e, eInv) x q (y, yInv) ranges pubVT ph3s
  let wit = pub ^+^ y*^mWit ^+^ (y^3)*^rWit ^+^ (y^5)*^dmWit ^+^ (2 * yInv) *^ sumV (zipWith (*^) (inputCoeffs hasTypes x q) nWits)
  let (bl1Tm, bl2Sc) = makeBlindingTerms (powers' $ q^2) (getNormRPW wit) blsNrm
  T3 err4Bl err6Bl err10Bl <- random'
  let errSumBl = yInv^2 * bl1Tm - y^7 * (bl1Sc + if hasTypes then q * blType else 0) + 2 * y * dotZip sharedCs blsMs 
  let err2Bl = errSumBl - (err4Bl * y^2 + err6Bl * y^4 + err10Bl * y^8)
  (bl2Wit, bl2Com) <- idAp commit' <$> linearRPW (bl2Sc * yInv^9) [0, err2Bl, err4Bl, err6Bl, err10Bl]
  t <- head <$> oracle [bl2Com]
  let tInv = recip t

  -- Phase 5: setup bulletproof
  let coms = bl2Com : bl1Com : rCom : dmCom : mCom : nComs
  let bpCom = TTRRP hasTypes coms e x q y t
  let bpRounds = (fromInteger $ integerLog 2 $ toInteger len) - 1
  let makeCom = makePSV' q yInv $ makeBpCoeffs hasTypes q (y, yInv) tInv sharedCs
  let bpWit = makeCom $ wit ^+^ t*^bl1Wit ^+^ (t^2)*^bl2Wit

  return (coms, SBP (makeCom zeroV) bpCom (makeCom pub) bpRounds, WBP bpWit)

-- Monadic verifier. 
verifyTRRPM :: CanCommitM v s m => SetupTRRP v s -> [v] -> m (Setup BPTRRP v s)
verifyTRRPM (STRRP hasTypes mBases pubVT rcs makeBaseMap' _ makePSV') coms = do
  let ranges = map range rcs
  let mins = fromInteger . minRange <$> ranges
  let Just ph1ss = fmap (fst . unzip) $ sequence $ zipWith makePhase1s rcs mins
  let ph1ss' = appIf (zipWith (:) (map (\rc -> Ph1Typing (isOutput rc) 0 0) rcs)) hasTypes ph1ss
  
  let (bl2Com : bl1Com : rCom : dmCom : mCom : nComs) = coms
  ex <- take 2 <$> oracle (dmCom : mCom : nComs)
  let [e,x] = ex
  q <- head <$> oracle [rCom]
  y <- head <$> oracle [bl1Com]
  t <- head <$> oracle [bl2Com]
  let [eInv, qInv, yInv, tInv] = batchInverse [e, q, y, t]

  let baseMap = makeBaseMap' x
  let ph2s = makePhase2s (e, eInv) x baseMap ph1ss'
  let ph3s = zipWith3 Ph3 ph2s ( zip (powers' $ q^2) (powers' $ qInv^2) ) $ repeat 0

  let rounds = (fromInteger $ integerLog 2 $ toInteger $ length ph2s) - 1
  let pub = makePublicConsts (e, eInv) x q (y, yInv) ranges pubVT ph3s
  let makeCom = makePSV' q yInv $ makeBpCoeffs hasTypes q (y, yInv) tInv $ makeSharedCoeffs (e, eInv) mBases baseMap

  return $ SBP (makeCom zeroV) (TTRRP hasTypes coms e x q y t) (makeCom pub) rounds 

data TypedReciprocalRangeProof v s = TRRP [v] (BPTRRP v s)

instance ZKP TypedReciprocalRangeProof where
  type Setup TypedReciprocalRangeProof v s = SetupTRRP v s
  type Witness TypedReciprocalRangeProof v s = WitnessTRRP v s
  
  proveM s w = do
    (coms, s', w') <- proveTRRPM s w
    TRRP coms <$> proveM s' w'

  verifyM s (TRRP coms p') = do
    s' <- verifyTRRPM s coms
    verifyM s' p'

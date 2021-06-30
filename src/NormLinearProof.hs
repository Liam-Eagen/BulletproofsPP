{-# LANGUAGE RecordWildCards, BangPatterns, DataKinds, FlexibleContexts #-}
{-# LANGUAGE TupleSections, KindSignatures, TypeFamilies, RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

module NormLinearProof where

import Data.Bifunctor
import Data.Foldable (foldrM)
import Control.Monad (replicateM)

import Data.VectorSpace
import Data.Field.Galois (PrimeField)
import qualified Data.Field.Galois as GF
import Data.Curve hiding (id)
import qualified Data.Curve as Curve
import Data.Curve.Weierstrass hiding (id)

-- import Math.NumberTheory.Logarithms (integerLog2)

import Utils
import Commitment

-------------------------
-- Generic Bulletproof --

class (Foldable f, Zip f) => BPCollect f where
  empty' :: f a
  single' :: a -> f a
  halves' :: f a -> (f a, f a)
  unHalves' :: f a -> f a -> f a
  tensor' :: Num a => f a -> [a] -> [a] -> f a
  eq' :: Eq a => f a -> f a -> Bool

  -- Takes shorter sequence, dots with subsequences of same length in longer
  -- sequence. 
  contract' :: Num a => f a -> f a -> f a

instance BPCollect [] where
  empty' = []
  single' x = [x]

  -- NOTE currently uses interleaved halves since this is easier to work with
  -- the q powers. May be less performant than splitAt form?
  -- halves' xs = splitAt (uncurry (+) $ quotRem (length xs) 2) xs
  halves' (x:y:zs) = let (xs, ys) = halves' zs in (x:xs, y:ys)
  halves' (x:[]) = ([x], [])
  halves' [] = ([], [])
  
  -- Obviously must agree with halves'
  unHalves' xs [] = xs
  unHalves' (x:xs) (y:ys) = x : y : unHalves' xs ys

  -- Accepts the base case, challenges in reverse order and q powers in correct
  -- order. TODO should maybe refactor?
  tensor' bs es qs = (*) <$> bs <*> (fst $ foldr step ([1], qs) es)
    where step e (ts, q:qs) = ( (*) <$> [1, e * q] <*> ts, qs )

  -- TODO just Eq (f a)?
  eq' = (==)

  contract' xs ys = map (dotZip xs) $ chunks (length xs) ys

-- Stores data for a round of the Bulletproof
data BPFrame f v s = BPF { nrmlz :: s, leftS :: f s, leftG :: f v, rightS :: f s, rightG :: f v }
  deriving (Eq, Show)

makeBPFrame :: (CanCommit v s, BPCollect f) => s -> f s -> f v -> BPFrame f v s
makeBPFrame n ss gs = let (ls, rs) = halves' ss in let (lg, rg) = halves' gs in BPF n ls lg rs rg

instance Functor f => Bifunctor (BPFrame f) where
  bimap f g (BPF n ls lg rs rg) = BPF (g n) (g <$> ls) (f <$> lg) (g <$> rs) (f <$> rg)

instance (Zip f, Foldable f) => Commitment (BPFrame f) where
  -- Normalization is not incorporated into commitment
  commitWith (BPF _ ls lg rs rg) (*:) (+:) z = let (.:) = dotWith (*:) (+:) in ls .: lg $ rs .: rg $ z

makeXRFrames :: (CanCommit v s, BPCollect f) => BPFrame f v s -> (BPFrame f v s, BPFrame f v s) 
makeXRFrames (BPF n ls lg rs rg) = (BPF n ls rg rs lg, BPF n empty' empty' rs rg)

class Commitment f => BPCommitment f where
  -- Compute scalar of responses (TODO use f a s to limit access to basis)
  crossScalar :: Num s => f x s -> s
  rightScalar :: Num s => f x s -> s
  
  -- NOTE : evalScalar . fst . makeXR =/= crossScalar in general
  evalScalar :: Num s => f x s -> s

  -- Create responses, collapse responses given the challenge
  makeXR :: CanCommit v s => f v s -> (f v s, f v s)
  collapse :: CanCommit v s => s -> f v s -> f v s

  -- TODO currently has linear coefficient check
  expandChallenges :: CanCommit v s => [s] -> f x0 s -> f x1 s -> f v x2 -> Maybe (f v s)

collapsePoints :: CanCommit v s => s -> s -> Integer -> (v -> v -> v)
collapsePoints b a s lg rg = shamir lg b (signumV s rg) (a*fromInteger s)

------------
-- Linear --

data Linear f v s = L { leftC :: f s, rightC :: f s, linear :: BPFrame f v s }
  deriving (Eq, Show)

makeLinear :: (CanCommit v s, BPCollect f) => f s -> f s -> f v -> Linear f v s
makeLinear cs ss gs = uncurry L (halves' cs) $ makeBPFrame 1 ss gs

instance Functor f => Bifunctor (Linear f) where
  bimap f g (L lc rc bpf) = L (g <$> lc) (g <$> rc) (bimap f g bpf)

instance (Zip f, Foldable f) => Commitment (Linear f) where
  commitWith = commitWith . linear

--instance (Monoid m, Zip f) => Zip (Linear f m) where
--  liftZip x = L (liftZip x) (liftZip x) (liftZip x)
--  zipWith' f (L lc0 rc0 bpf0) (L lc1 rc1 bpf1) = L (zipWith' f lc0 lc1) (zipWith' f rc0 rc1) (zipWith' f bfp0 bf1)
--  zipWithDef' f z (L lc0 rc0 bpf0) (L lc1 rc1 bpf1) = L lc2 rc2 bf2
--    where
--      lc2 = zipWithDef' f z lc0 lc1
--      rc2 = zipWithDef' f z rc0 rc1
--      bpf2 = zipWithDef' f z bpf0 bpf1

instance BPCollect f => BPCommitment (Linear f) where
  crossScalar (L lcs rcs (BPF _ ls _ rs _)) = dotZip lcs rs + dotZip rcs ls
  rightScalar (L _   rcs (BPF _ _  _ rs _)) = dotZip rcs rs
  evalScalar (L lcs rcs (BPF _ ls _ rs _)) = dotZip lcs ls + dotZip rcs rs

  makeXR (L lcs rcs bpf) = bimap (L lcs rcs) (L empty' rcs) $ makeXRFrames bpf

  collapse e (L lcs rcs (BPF n ls lg rs rg)) = uncurry L (halves' cs') $ makeBPFrame (n*b) ss' gs'
    where
      (a, b, bInv, s) = splitScalar e
      cs' = linCombZipDef b a lcs rcs
      ss' = linCombZipDef bInv (e*bInv) ls rs
      gs' = zipWithDef' (collapsePoints b a s) zeroV lg rg

  -- Checks that lc', rc' are generated via challenges from lc rc
  expandChallenges es (L lc' rc' scl) (L lc rc (BPF _ lp _ rp _)) (L _ _ (BPF _ _ lg _ rg)) = if validCoeffs
    then Just $ L lc rc $ BPF 1 ls' lg rs' rg
    else Nothing
    where
      expEs = tensor' (single' $ nrmlz scl) es $ repeat 1
      validCoeffs = unHalves' lc' rc' `eq'` (contract' expEs $ unHalves' lc rc)
      vs = (nrmlz scl *) <$> unHalves' (leftS scl) (rightS scl)
      (ls', rs') = uncurry bimap ((dup $ flip $ zipWithDef' (flip (-)) 0) (lp, rp)) $ halves' $ tensor' vs es $ repeat 1

----------
-- Norm --

data Norm f v s = N { qN :: s, rN :: s, norm :: BPFrame f v s }
  deriving (Eq, Show)

makeNorm :: (CanCommit v s, BPCollect f) => s -> f s -> f v -> Norm f v s
makeNorm q ss gs = N q (recip q) $ makeBPFrame q ss gs

instance Functor f => Bifunctor (Norm f) where
  bimap f g (N q r bpf) = N (g q) (g r) (bimap f g bpf) 

instance (Zip f, Foldable f) => Commitment (Norm f) where
  commitWith = commitWith . norm

instance BPCollect f => BPCommitment (Norm f) where
  crossScalar (N q r (BPF n ls _ rs _)) = 2 * q * n^2 * weightedDotZip (powers $ q^4) ls rs
  rightScalar (N q r (BPF n ls  _ rs _)) = q^2 * n^2 * weightedDotZip (powers $ q^4) rs rs
  evalScalar (N q r (BPF n ls _ rs _)) = n^2 * (weightedDotZip (powers $ q^4) ls ls + q^2 * weightedDotZip (powers $ q^4) rs rs)

  makeXR (N q r bpf) = dup (N q r) $ (BPF n ((*r) <$> xls) xlg ((*q) <$> xrs) xrg, rf)
    where (BPF n xls xlg xrs xrg, rf) = makeXRFrames bpf
  
  collapse e (N q r (BPF n ls lg rs rg)) = N (q^2) (r^2) $ makeBPFrame (n*b) ss' gs'
    where
      (a, b, bInv, s) = splitScalar (e * r)
      ss' = linCombZipDef bInv (e * q * bInv) ls rs
      gs' = zipWithDef' (collapsePoints b a s) zeroV lg rg
  
  expandChallenges es (N q' _ scl) (N q r (BPF _ lp _ rp _)) (N _ _ (BPF _ _ lg _ rg)) = Just $ N 1 1 $ BPF 1 ls' lg rs' rg
    where
      vs = ((nrmlz scl*r) *) <$> unHalves' (leftS scl) (rightS scl)
      (ls', rs') = uncurry bimap ((dup $ flip $ zipWithDef' (flip (-)) 0) (lp, rp)) $ halves' $ tensor' vs es $ iterate (^2) r

----------------
-- NormLinear --

-- Scales the scalar by the inverse of scalarNL by multiplying the evaluated
-- scalars from the norm and linear substructures. Avoids modifying the scalar
-- basis element.
data NormLinear f v s = NL { scalarNL :: s, normNL :: Norm f v s, linearNL :: Linear f v s }
  deriving (Eq, Show)

makeNormLinear :: (CanCommit v s, BPCollect f) => s -> f s -> f s -> f v -> f s -> f v -> NormLinear f v s
makeNormLinear q cs nss ngs lss lgs = NL 1 (makeNorm q nss ngs) (makeLinear cs lss lgs)

makeNormLinearWithScalar :: (CanCommit v s, BPCollect f) => s -> s -> f s -> f s -> f v -> f s -> f v -> NormLinear f v s
makeNormLinearWithScalar s q cs nss ngs lss lgs = NL s (makeNorm q nss ngs) (makeLinear cs lss lgs)

instance Functor f => Bifunctor (NormLinear f) where
  bimap f g (NL s n l) = NL (g s) (bimap f g n) (bimap f g l)

instance (Zip f, Foldable f) => Commitment (NormLinear f) where
  commitWith (NL _ n l) (*:) (+:) x = commitWith n (*:) (+:) $ commitWith l (*:) (+:) x

instance BPCollect f => BPCommitment (NormLinear f) where
  crossScalar (NL s n l) = s * (crossScalar n + crossScalar l)
  rightScalar (NL s n l) = s * (rightScalar n + rightScalar l)
  evalScalar (NL s n l) = s * (evalScalar n + evalScalar l)

  makeXR (NL s n l) = uncurry bimap (dup (NL s) $ makeXR n) $ makeXR l
  collapse e (NL s n l) = NL s (collapse e n) (collapse e l)

  expandChallenges es (NL _ n l) (NL s np lp) (NL _ ng lg) = NL s <$> (expandChallenges es n np ng) <*> (expandChallenges es l lp lg)

-------------------------
-- Prover and Verifier --
-------------------------

-- Accepts: BPC f v s
type BPC = PedersenScalarVector

-- TODO replace initCom with function: commitWith c. Avoids passing the type
-- parameter in the first place, which is unused in the other types.
data SetupBP c f v s = SBP { basisBP :: BPC f v s, initCom :: c v s, publicCs :: BPC f v s , rounds :: Int }
  deriving (Eq, Show)

-- To implement Show for the Committer v s we would need to do something like
-- commitWith (,) (:) []

data WitnessBP (c :: * -> * -> *) f v s = WBP { witnessBP :: BPC f v s }
  deriving (Eq, Show)
data Bulletproof (c :: * -> * -> *) f v s = PBP { responses :: [(v, v)], opening :: BPC f v s }
  deriving (Eq, Show)

instance (Commitment c, BPCommitment f) => ZKP (Bulletproof c f) where
  type Setup (Bulletproof c f) v s = SetupBP c f v s
  type Witness (Bulletproof c f) v s = WitnessBP c f v s

  -- TODO witness contains basis... could check that they are the same? Doesn't
  -- matter, will just produce proof that won't verify
  -- NOTE assumes that wit is an opening of commit ic ^+^ commit pub
  proveM (SBP _ _ _ n) (WBP wit) = uncurry (flip PBP) <$> proveBPM n wit

  -- Uses pub to avoid extra computation with ic commitment by combining inner
  -- product with the expanded challenges
  verifyM (SBP bss ic pub n) (PBP rs opn) = verifyBPM ic rs pub bss opn

proveRoundM :: (CanCommitM v s m, BPCommitment f) => BPC f v s -> m (BPC f v s, (v, v))
proveRoundM com@(PSV b s c) = do
  T2 xbl rbl <- random'
  let (x, r) = makeXR c
  let xs = crossScalar c
  let rs = rightScalar c
  let xc = commit $ updatePSV com xbl xs x
  let rc = commit $ updatePSV com rbl rs r
  e <- head <$> oracle [xc, rc]
  let bl' = scalarCP b + (e * xbl + (e*e - 1) * rbl)
  let sc' = scalarCP s + (e * xs + (e*e - 1) * rs)
  return (updatePSV com bl' sc' $ collapse e c, (xc, rc))

proveBPM :: (CanCommitM v s m, BPCommitment f) => Int -> BPC f v s -> m (BPC f v s, [(v, v)])
proveBPM n com = foldrM step (com, []) (replicate n ())
  where step () (com, resps) = fmap (: resps) <$> proveRoundM com

-- Used to compute the final inner product
verifyWith :: (CanCommit v s, Commitment c, Commitment f)
           => c v s -> [s] -> [(v, v)] -> f v s -> (s -> v -> a) -> (a -> b -> b) -> b -> b

verifyWith c es vs wit (*:) (+:) z = commitWith wit (*:) (+:) $ commitWith c (*:) (+:) $ dotWith (*:) (+:) es' vs' z
  where
    -- cw x z = commitWith x (*:) (+:) z
    vs' = foldr (\(x,r) l -> x : r : l) [] vs
    es' = es >>= \e -> [e, e*e - 1]

verifyBPM :: (CanCommitM v s m, BPCommitment f, Commitment c)
          => c v s -> [(v, v)] -> BPC f x0 s -> BPC f v x1 -> BPC f x2 s -> m Bool

verifyBPM cI rs (PSV bp sp pub) b@(PSV bg sg bss) (PSV bw sw wit) = do
  es <- foldrM (\(x,r) es -> (:) <$> (head <$> oracle [x,r]) <*> return es) [] rs
  case expandChallenges es wit pub bss of
    Nothing -> return $ False
    Just chs -> do
      let wit' = updatePSV b (scalarCP bp - scalarCP bw) (scalarCP sp - scalarCP sw) chs
      let scalarIsValid = scalarCP sw == evalScalar wit
      let commitIsValid = zeroV == shamirWith (verifyWith cI es rs wit') zeroV
      return $ scalarIsValid && commitIsValid

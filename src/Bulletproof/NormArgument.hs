{-# LANGUAGE StandaloneDeriving #-}

module Bulletproof.NormArgument where

import Data.Bifunctor
import Data.Foldable (foldrM, toList)
import Control.Monad (replicateM)

import Data.VectorSpace
import Utils
import Commitment

import Bulletproof

import Control.Parallel.Strategies

-- Returns functions for committing to x and r, as well as the computed scalar
-- values. Normalization can be handled by caller. For norms q scaling can occur
-- in the sc function
foldXR :: (CanCommit v s, BPCollection f)
       => (a -> s -> s -> g v s -> g v s -> (a, s, s, g v s, g v s))  -- Swaps the scalars/basis points
       -> a
       -> g v s                                     -- Zeros
       -> BPFrame'' g f v s -> (s, BPFrame'' g f v s, s, BPFrame'' g f v s)
foldXR swap a z (BPF'' n sgs) = (xFin, BPF'' n $ unHalves'' $ fst <$> fs, rFin, BPF'' n $ snd <$> fs)
  where
    ((_, xFin, rFin), fs) = foldMapHalves go z (a, 0, 0) sgs 
    go l r (!a, !xS, !rS) = ((a', xS', rS'), ((l', r'), r))
      where (a', xS', rS', l', r') = swap a xS rS l r

------------
-- Linear --

data LinearF v s = LF { cLF :: s, xLF :: s, gLF :: v } deriving (Eq, Show)

instance Bifunctor LinearF where
  bimap f g (LF c x p) = LF (g c) (g x) (f p)

instance Opening LinearF where
  openWith (LF _ x g) (*:) (+:) z = (x *: g) +: z

newtype Linear f v s = L { linF :: (BPFrame'' LinearF f v s) }
  deriving (Bifunctor, Opening)
deriving instance (Eq v, Eq s, BPCollection f) => Eq (Linear f v s)
deriving instance (Show v, Show s, BPCollection f) => Show (Linear f v s)

makeLinear :: (CanCommit v s, BPCollection f) => f s -> f s -> f v -> Linear f v s
makeLinear cs ss gs = L $ BPF'' 1 $ zipWithDef'' (uncurry LF) (0, 0) zeroV (zipWithDef'' (,) 0 0 cs ss) gs

instance BPCollection f => BPOpening (Linear f) where
  optimalRounds (L (BPF'' _ sgs)) = numberRoundsReduce $ length $ toList sgs
  makeEs _ e = (e, e^2 - 1)
  evalScalar (L (BPF'' _ sgs)) = sum $ sc <$> sgs
    where sc (LF c x _) = c * x
  
  makeScalarsComs (L bpf) = (sL', L wL', sR', L wR')
    where 
      (sL', wL', sR', wR') = foldXR swap () (LF 0 0 zeroV) bpf
      swap _ x r (LF cL xL gL) (LF cR xR gR) = ((), x + cL * xR + cR * xL, r + cR * xR, LF cL xR gL, LF cR xL gR)

  -- Must normalize 
  getWitness (L bpf) = toList $ (nrmlz'' bpf *) . xLF <$> body'' bpf

  collapse e (L (BPF'' n sgs)) = L $ BPF'' (n*b0) sgs''
    where
      (a', b') = rationalReduceScalar e
      a0 = extractScalar a'
      b0 = extractScalar b'
      b0Inv = recip b0
      sgs'' = mapHalves cps (LF 0 0 zeroV) sgs 
      cps (LF cL xL gL) (LF cR xR gR) = LF (b0*cL + a0*cR) (b0Inv*xL + e*b0Inv*xR) (collapsePoints b' a' gL gR) --`using` parColl rdeepseq

  expandChallenges es wit@(L (BPF'' n b)) (L (BPF'' _ sps)) (L (BPF'' _ sgs)) = (sc, L $ BPF'' 1 sgs')
    where
      expEs = tensor' (single' 1) es $ repeat 1
      cs' = contract' expEs $ cLF <$> sps
      vs = (n *) . xLF <$> b
      sc = dotZip cs' vs
    
      exp ((LF c p _), (LF _ _ g)) eP = LF c (p - eP) g
      sgs' = zipWithDef' exp 0 (zip' sps sgs) $ tensor' vs es $ repeat 1

----------
-- Norm --

data NormF v s = NF { xNF :: s, gNF :: v } deriving (Eq, Show)

instance Bifunctor NormF where
  bimap f g (NF x p) = NF (g x) (f p)

instance Opening NormF where
  openWith (NF x g) (*:) (+:) z = (x *: g) +: z

data Norm f v s = N { qN :: s, qInvN :: s, norm :: BPFrame'' NormF f v s }
deriving instance (Eq v, Eq s, BPCollection f) => Eq (Norm f v s)
deriving instance (Show v, Show s, BPCollection f) => Show (Norm f v s)

makeNorm :: (CanCommit v s, BPCollection f) => s -> f s -> f v -> Norm f v s
makeNorm q ss gs = N q (recip q) $ BPF'' 1 $ zipWithDef'' NF 0 zeroV ss gs

instance Functor f => Bifunctor (Norm f) where
  bimap f g (N q qInv bpf) = N (g q) (g qInv) (bimap f g bpf) 

instance (Zip f, Foldable f) => Opening (Norm f) where
  openWith = openWith . norm

instance BPCollection f => BPOpening (Norm f) where
  optimalRounds (N _ _ (BPF'' _ sgs)) = numberRoundsReduce $ length $ toList $ sgs
  makeEs _ e = (e, e^2 - 1)
  evalScalar (N q qInv (BPF'' n sgs)) = n^2 * weightedDotZip (powers' $ q^2) ss ss
    where ss = xNF <$> sgs
  
  makeScalarsComs (N q qInv bpf@(BPF'' n _)) = (2 * n^2 * q^3 * sX', N q qInv wX', n^2 * q^4 * sR', N q qInv wR')
    where 
      q4 = q^4
      (sX', wX', sR', wR') = foldXR swap 1 (NF 0 zeroV) bpf
      swap !s !x !r (NF xL gL) (NF xR gR) = (s', x + s * xL * xR, r + s * xR^2, NF (q * xR) gL, NF (qInv * xL) gR)
        where s' = q4 * s

  -- Must normalize witness
  getWitness (N _ _ bpf) = toList $ (* nrmlz'' bpf) . xNF <$> body'' bpf
  
  collapse e (N q qInv (BPF'' n sgs)) = N (q^2) (qInv^2) $ BPF'' (n*b0*qInv) sgs''
    where
      (a', b') = rationalReduceScalar (e * qInv)
      b0 = extractScalar b'
      b0Inv = recip b0
      sgs'' = mapHalves cps (NF 0 zeroV) sgs 
      cps (NF xL gL) (NF xR gR) = NF (b0Inv*xL + e*q*b0Inv*xR) (collapsePoints b' a' gL gR) --`using` parColl rdeepseq

  expandChallenges es wit@(N q' _ (BPF'' n b)) pub@(N q qInv (BPF'' _ sps)) (N _ _ (BPF'' _ sgs)) = ret
    where
      vs = (n *) . xNF <$> b
      qF = head $ drop (length es) $ iterate (^2) $ q
      sc = weightedDotZip (powers' $ qF^2) vs vs

      -- TODO, if we subtract off the public constants seperately via a
      -- VectorSpace instance or something, we might be able to call evalScalar
      -- on the tensor vector. Need to set normalization to something like the
      -- product of the (1 + e^2), not sure

      exp ((NF p _), (NF _ g)) eP = NF (p - eP) g
      sgs' = zipWithDef' exp 0 (zip' sps sgs) $ tensor' vs es $ iterate (^2) q

      ret = (sc, N 1 1 $ BPF'' 1 sgs')

instance BPCollection f => Weighted (Norm f) where
  qPowers' _ = powers' . (^2)

----------------
-- NormLinear --

newtype NormLinear f v s = NL { compNL :: BPCompose (Norm f) (Linear f) v s }
  deriving (Eq, Show, Bifunctor, Opening, BPOpening)

instance BPCollection f => Weighted (NormLinear f) where
  qPowers' = qPowers' . fmap compNL

instance BPCollection f => NormLinearBP (NormLinear f) where
  type Coll (NormLinear f) = f

  makeNormLinearBP' s q cs nss ngs lss lgs = NL $ BPComp s (makeNorm q nss ngs) (makeLinear cs lss lgs)

  -- Reduce until the next reduction only eliminates two scalars
  optimalWitnessSize _ nLen lLen = res
    where
      (nR, nLen') = numberRoundsReduce nLen     -- Either 1, 2, 3, 4
      (lR, lLen') = numberRoundsReduce lLen     -- Also

      -- Perform the same number of reduction on both
      r = max nR lR
      nLen'' = roundReduceBy nLen' $ r - nR
      lLen'' = roundReduceBy lLen' $ r - lR

      -- In the (4, n) with n > 1 case do one more reduction
      res = if nLen'' + lLen'' > 5 
              then (r + 1, (roundReduce nLen'', roundReduce lLen''))
              else (r, (nLen'', lLen''))



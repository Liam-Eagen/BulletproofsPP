{-# LANGUAGE StandaloneDeriving #-}

module Bulletproof.InnerProductArgument where

import Data.Bifunctor
import Data.Foldable (foldrM, toList)
import Control.Monad (replicateM)

import Data.VectorSpace
import Control.Parallel.Strategies

import Utils
import Commitment 
import Bulletproof


foldLR :: (CanCommit v s, BPCollection f)
       => (a -> s -> s -> g v s -> g v s -> (a, s, s, g v s, g v s))  -- Swaps the scalars/basis points
       -> a
       -> g v s                                     -- Zeros
       -> BPFrame'' g f v s -> (s, BPFrame'' g f v s, s, BPFrame'' g f v s)
foldLR swap a z (BPF'' n sgs) = (lFin, BPF'' n $ fst <$> fs, rFin, BPF'' n $ snd <$> fs)
  where
    ((_, lFin, rFin), fs) = foldMapHalves go z (a, 0, 0) sgs 
    go l r (!a, !lS, !rS) = ((a', lS', rS'), (l', r'))
      where (a', lS', rS', l', r') = swap a lS rS l r


-------------------
-- Inner Product --

data IPF v s = IPF { xIPF :: s, gIPF :: v, yIPF :: s, hIPF :: v } deriving (Eq, Show)

instance Bifunctor IPF where
  bimap f g (IPF x p y q) = IPF (g x) (f p) (g y) (f q)

instance Opening IPF where
  openWith (IPF x g y h) (*:) (+:) z = (x *: g) +: ( (y *: h) +: z )

-- the vectors are normalized differently due to weight and BPF only keeps track
-- of one normalization value. However, storing them is more convenient for
-- locality
data InnerProduct f v s = IP { sIP :: s, nrmlzYIP :: s, qIP :: s, qInvIP :: s, bodyIP :: BPFrame'' IPF f v s }
deriving instance (Eq v, Eq s, BPCollection f) => Eq (InnerProduct f v s)
deriving instance (Show v, Show s, BPCollection f) => Show (InnerProduct f v s)

makeIP :: (CanCommit v s, BPCollection f) => s -> s -> f s -> f v -> f s -> f v -> InnerProduct f v s
makeIP s q ss0 gs0 ss1 gs1 = IP s 1 q (recip q) $ BPF'' 1 ips
  where ips = zipWithDef'' (uncurry $ uncurry IPF) ((0, zeroV), 0) zeroV (zipWithDef'' (,) (0, zeroV) 0 (zipWithDef'' (,) 0 zeroV ss0 gs0) ss1) gs1

instance Functor f => Bifunctor (InnerProduct f) where
  bimap f g (IP s ny q qInv bpf) = IP (g s) (g ny) (g q) (g qInv) (bimap f g bpf)

instance (Zip f, Foldable f) => Opening (InnerProduct f) where
  openWith = openWith . bodyIP

instance BPCollection f => BPOpening (InnerProduct f) where
  -- The inner product must reduce the vectors to either 1 or 2 since there are
  -- two of them. Length already < 5, so just need one more round
  optimalRounds (IP _ _ _ _ (BPF'' _ sgs)) = numberRoundsReduce' $ length $ toList $ sgs
  
  -- Better way to do this?
  evalScalar (IP s ny q qInv bpf@(BPF'' nx ws)) = s * nx * ny * dotZip scs (fromList' $ powers' $ q)
    where
       sc (IPF x _ y _) = x * y
       scs = sc <$> ws

  makeEs _ e = (recip e, e)

  makeScalarsComs (IP s ny q qInv bpf@(BPF'' nx _)) = (sL'', mkIP 1 wL', sR'', mkIP qInv wR')
    where
      q2 = q^2
      (sL', wL', sR', wR') = foldLR swap 1 (IPF 0 zeroV 0 zeroV) bpf
      sL'' = s * q  * nx * ny * sL'
      sR'' = s * q2 * nx * ny * sR'
      mkIP t (BPF'' nx bpf) = IP s ny (q^2) (qInv^2) $ BPF'' (t*nx) bpf
      swap s l r (IPF xL gL yL hL) (IPF xR gR yR hR) = (s', l + s * xL * yR, r + s * xR * yL, l', r')
        where
          s' = q2*s
          l' = IPF (qInv * xL) gR yR hL
          r' = IPF (q    * xR) gL yL hR

  getWitness (IP s ny _ _ (BPF'' nx sgs)) = unPairs $ toList $ go <$> sgs
    where go (IPF x _ y _) = (nx * x, ny * y)

  collapse e (IP s ny q qInv (BPF'' nx sgs)) = IP s (ny * d0) (q^2) (qInv^2) $ BPF'' (nx * b0 * qInv) sgs'
    where
      eInv = recip e
      (a', b') = rationalReduceScalar (qInv * eInv)
      b0 = extractScalar b'
      b0Inv = recip b0

      (c', d') = rationalReduceScalar e
      d0 = extractScalar d'
      d0Inv = recip d0

      sgs' = mapHalves cps (IPF 0 zeroV 0 zeroV) sgs
      cps (IPF xL gL yL hL) (IPF xR gR yR hR) = IPF (b0Inv * (xL + e*q*xR)) g' (d0Inv * (yL + eInv*yR)) h'
        where
          g' = collapsePoints b' a' gL gR
          h' = collapsePoints d' c' hL hR

  expandChallenges esY wit@(IP s ny q' _ (BPF'' nx b)) ipP ipG = res 
    where
      IP s _ q qInv (BPF'' _ bP) = ipP
      IP _ _ _ _    (BPF'' _ bG) = ipG

      -- For evaluation of scalar
      qF = head $ drop (length esY) $ iterate (^2) $ q
      qFInv = recip qF      -- TODO not necessary

      esX = recip <$> esY
      -- NOTE this is why independent normalization is necessary
      vsX = (nx *) . xIPF <$> b
      vsY = (ny *) . yIPF <$> b
      sc = s * weightedDotZip (powers' $ qF) vsX vsY

      tsX = tensor' vsX esX $ iterate (^2) q
      tsY = tensor' vsY esY $ repeat 1
      sgs' = zipWithDef' exp (0,0) (zip' bP bG) $ zip' tsX tsY
      
      exp ((IPF pX _ pY _), (IPF _ g _ h)) (eX, eY) = IPF (pX - eX) g (pY - eY) h

      res = (sc, IP s 1 qF qFInv $ BPF'' 1 sgs')

instance BPCollection f => Weighted (InnerProduct f) where
  qPowers' _ = powers'

------------
-- Linear --

data LinearF v s = LF { cLF :: s, xLF :: s, gLF :: v } deriving (Eq, Show)

instance Bifunctor LinearF where
  bimap f g (LF c x p) = LF (g c) (g x) (f p)

instance Opening LinearF where
  openWith (LF _ x g) (*:) (+:) z = (x *: g) +: z

-- TODO not sure if the order of public scalars/witness is swapped wrt paper
newtype Linear f v s = L { linF :: BPFrame'' LinearF f v s }
  deriving (Bifunctor, Opening)
deriving instance (Eq v, Eq s, BPCollection f) => Eq (Linear f v s)
deriving instance (Show v, Show s, BPCollection f) => Show (Linear f v s)

makeLinear :: (CanCommit v s, BPCollection f) => f s -> f s -> f v -> Linear f v s
makeLinear cs ss gs = L $ BPF'' 1 $ zipWithDef'' (uncurry LF) (0, 0) zeroV (zipWithDef'' (,) 0 0 cs ss) gs

instance BPCollection f => BPOpening (Linear f) where
  optimalRounds (L (BPF'' _ sgs)) = numberRoundsReduce $ length $ toList sgs
  makeEs _ e = (recip e, e)
  evalScalar (L (BPF'' _ scs)) = sum $ sc <$> scs
    where sc (LF c x _) = c * x

  makeScalarsComs (L bpf) = (sL', L wL', sR', L wR')
    where
      (sL', wL', sR', wR') = foldLR swap () (LF 0 0 zeroV) bpf
      swap _ l r (LF cL xL gL) (LF cR xR gR) = ((), l + cR * xL, r + cL * xR, LF cR xL gR, LF cL xR gL)

  getWitness (L bpf) = toList $ (nrmlz'' bpf *) . xLF <$> body'' bpf

  collapse e (L (BPF'' n sgs)) = L $ BPF'' (n*b0) sgs''
    where
      (a', b') = rationalReduceScalar $ recip e
      a0 = extractScalar a'
      b0 = extractScalar b'
      b0Inv = recip b0
      
      sgs'' = mapHalves cps (LF 0 0 zeroV) sgs 
      cps (LF cL xL gL) (LF cR xR gR) = LF (b0*cL + a0*cR) (b0Inv*xL + e*b0Inv*xR) (collapsePoints b' a' gL gR)

  expandChallenges es' (L (BPF'' n b)) (L (BPF'' _ sps)) (L (BPF'' _ sgs)) = (sc, L $ BPF'' 1 sgs')
    where
      es = recip <$> es'
      expEs = tensor' (single' 1) es $ repeat 1
      cs' = contract' expEs $ cLF <$> sps
      vs = (n *) . xLF <$> b
      sc = dotZip cs' vs

      exp ((LF c p _), (LF _ _ g)) eP = LF c (p - eP) g
      sgs' = zipWithDef' exp 0 (zip' sps sgs) $ tensor' vs es $ repeat 1

----------
-- Norm --

-- Norm wraps the inner product and does basis modification, but otherwise works
-- exactly the same internally. TODO we need to bypass the basis computation in
-- the verifier case, it takes way too long. Probably requires a different
-- organization to defer until the first collapse or something
newtype Norm f v s = N { norm :: InnerProduct f v s }
  deriving (Eq, Show, Bifunctor, Opening) --, BPOpening)

-- Does the basis transformation. Accepts the r such that q = -r^2
makeNorm :: (CanCommit v s, BPCollection f) => s -> f s -> f v -> Norm f v s
makeNorm r ss gs = N $ IP 4 1 q (recip q) $ BPF'' 1 $ mapHalves mkIP (0, zeroV) $ zipWithDef'' (,) 0 zeroV ss gs
  where
    q = r^4
    half = recip 2
    r2Inv = recip (2*r)
    mkIP (s0, g0) (s1, g1) = IPF x' g' y' h'
      where
        x' = r2Inv * s0 + half * s1
        y' = -r2Inv * s0 + half * s1
        p = commit $ CP r g0
        g' = g1 ^+^ p
        h' = g1 ^-^ p

instance BPCollection f => BPOpening (Norm f) where
  optimalRounds = optimalRounds . norm

  -- These functions are all the same
  evalScalar = evalScalar . norm
  makeEs = makeEs . norm
  makeScalarsComs (N w) = (sL, N wL, sR, N wR)
    where (sL, wL, sR, wR) = makeScalarsComs w

  collapse e (N w) = N $ collapse e w

  -- This returns a vector such that calling makeNorm 1 with that witness yields
  -- the original value. This is so that encodeing/decoding work generically in
  -- the range proofs.
  getWitness (N (IP s ny _ _ (BPF'' nx sgs))) = unPairs $ toList $ go <$> sgs
    where go (IPF x _ y _) = (nx * x - ny * y, nx * x + ny * y)

  -- TODO currently, this performs the inital basis transformation before
  -- calling this, which we don't want. Modifying to not do this requires
  -- defering the basis transformation.
  expandChallenges es (N w) (N p) (N b) = N <$> expandChallenges es w p b

instance BPCollection f => Weighted (Norm f) where
  qPowers' _ q = powers' $ negate $ q^2

----------------
-- NormLinear --

-- Scales the scalar by the inverse of scalarNL by multiplying the evaluated
-- scalars from the norm and linear substructures. Avoids modifying the scalar
-- basis element.
newtype NormLinear f v s = NL { compNL :: BPCompose (Norm f) (Linear f) v s }
  deriving (Eq, Show, Bifunctor, Opening, BPOpening)

instance BPCollection f => Weighted (NormLinear f) where
  qPowers' = qPowers' . fmap compNL

instance BPCollection f =>  NormLinearBP (NormLinear f) where
  type Coll (NormLinear f) = f

  makeNormLinearBP' s q cs nss ngs lss lgs = NL $ BPComp s (makeNorm q nss ngs) (makeLinear cs lss lgs)

  -- NOTE nLen is the length of the norm vector, not the length of the inner
  -- product vectors. First need to pad to an even length and then need to
  -- reduce half
  optimalWitnessSize _ nLen lLen = res
    where
      nLenEven = (nLen + (nLen `mod` 2)) `div` 2
      (nR, nLen') = numberRoundsReduce' nLenEven -- Either 1, 2, 3, 4
      (lR, lLen') = numberRoundsReduce lLen     -- Also

      -- Perform the same number of reduction on both
      r = max nR lR
      nLen'' = roundReduceBy nLen' $ r - nR
      lLen'' = roundReduceBy lLen' $ r - lR

      -- In the (4, n) with n > 1 case do one more reduction
      res = if 2*nLen'' + lLen'' > 5 
              then (r + 1, (2*roundReduce nLen'', roundReduce lLen''))
              else (r, (2*nLen'', lLen''))


{-# LANGUAGE BangPatterns, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, ConstrainedClassMethods #-}
{-# LANGUAGE RankNTypes, DeriveFunctor, DeriveFoldable, UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures, ScopedTypeVariables, FlexibleInstances #-}

-- Code for computing commitments, as well as for dealing with openings of
-- commitments. Abstracts all the elliptic curve code into a vectors space, and
-- the FastInnerProduct class.
--
-- Openings are containers that store both the scalars and curve points
-- necessary to compute a commitment. 

module Commitment where

import GHC.TypeLits (KnownNat)
import Data.List (zip6, unzip6)
import Data.Traversable (mapAccumL)
import Data.Bits (testBit)
import Data.Functor
import Data.Functor.Identity
import Data.Foldable
import Data.Bifunctor
import Control.DeepSeq

import Control.Monad.Trans
import Control.Monad.RWS.Strict

import Data.Field.Galois hiding ((*^), recip)
import qualified Data.Field.Galois as G (char)
import Data.Field.BatchInverse

import Data.Curve
import Data.Curve.Weierstrass
import Data.Curve.Edwards hiding (A, P)
import qualified Data.Curve.Edwards as E
import qualified Data.Curve as Curve

import Data.VectorSpace

import Utils
import Data.Field.Galois.FastPrime
import Data.Field.Eis
import Data.Curve.CM

-- TODO issues with stack supporting both the Data.Curve/Field code and
-- versions of these that support field operations. 
--
--import qualified Crypto.ECC.Edwards25519 as EC
--import qualified Crypto.Error as ECErr

-----------------------
-- Operation Classes --

-- To expose more control over the elliptic curves while retaining generality
-- over types, certain operations are generalized to classes.

-- Exposes doubling operation for elliptic curves
class AdditiveGroup a => FastDouble a where
  dbl' :: a -> a

-- Exposes fast complex multiplication for elliptic curves
class AdditiveGroup a => CMMult a where
  cmMul :: a -> a

-- Misc operations on elliptic curves including doubling, point normalization,
-- and potentially faster normalized point addition to a projective point. For
-- large number of additions, normalization can reduce the number of operations
-- per scalar multiplication and amortize the division over a large number of
-- points.
class AdditiveGroup a => NormalAdd a where
  type Normalized a

  normalize :: a -> Normalized a
  normalize x = head $ normalizes [x]
  
  normalizes :: [a] -> [Normalized a]
  normalizes = map normalize

  nrmlAdd :: Normalized a -> a -> a

  -- TODO function that performs a bunch of additions using affine rules but
  -- batches all the slope computations? Hard to use

---------------------------
-- VectorSpace instances --

instance (Num f, Field f) => FastDouble (WrapV f) where
  dbl' x = x + x
  {-# INLINABLE dbl' #-}

instance (Num f, Field f, HasEis f) => CMMult (WrapV f) where
  cmMul (WV p) = WV $ unity3 * p

instance (Curve f c e q p) => AdditiveGroup (Point f c e q p) where
  zeroV = Curve.id
  {-# INLINE zeroV #-}

  -- TODO might need to check that they aren't the same if used directly
  p ^+^ q = p `add` q
  {-# INLINE (^+^) #-}

  negateV p = Curve.inv p
  {-# INLINE negateV #-}

instance (Curve f c e q p) => VectorSpace (Point f c e q p) where
  type Scalar (Point f c e q p) = p
  s *^ p = p `mul` s
  {-# INLINE (*^) #-}

-- NOTE vector addition is not defined for the point with itself. Must use this
instance (Curve f c e q p) => FastDouble (Point f c e q p) where
  dbl' = dbl
  {-# INLINE dbl' #-}

instance (CMCurve f c e q p) => CMMult (Point f c e q p) where
  cmMul = cmConj

instance (WJCurve e q p, WACurve e q p) => NormalAdd (WJPoint e q p) where
  type Normalized (WJPoint e q p) = WAPoint e q p

  normalize p@(J x y z) = jacToAff p $ recip z

  normalizes js = as
    where
      zInvs = batchInverse [ z | J x y z <- js ]
      as = [ jacToAff p zInv | (p, zInv) <- zip js zInvs ]
  
  nrmlAdd O p = p
  nrmlAdd (A x y) (J _ _ 0) = J x y 1
  nrmlAdd (A x2 y2) (J x1 y1 z1) = J x3 y3 z3
    where
      z1z1 = z1^2
      u2 = x2*z1z1
      s2 = y2*z1*z1z1
      h = u2-x1
      hh = h^2
      i = let x = hh + hh in x + x
      j = h*i
      r = let x = (s2-y1) in x + x
      v = x1*i
      t = y1*j
      x3 = (r^2)-j-(v + v)
      y3 = r*(v-x3)-(t + t)
      z3 = (z1+h)^2-z1z1-hh

instance (WPCurve e q p, WACurve e q p) => NormalAdd (WPPoint e q p) where
  type Normalized (WPPoint e q p) = WAPoint e q p

  normalize p@(P x y z) = projToAff p $ recip z

  normalizes ps = as
    where
      zInvs = batchInverse [ z | P x y z <- ps ]
      as = [ projToAff p zInv | (p, zInv) <- zip ps zInvs ]
  
  nrmlAdd O p = p
  nrmlAdd (A x y) (P _ _ 0) = P x y 1
  nrmlAdd (A x2 y2) (P x1 y1 z1) = P x3 y3 z3
    where
      u = y2*z1-y1
      uu = u^2
      v = x2*z1-x1
      vv = v^2
      vvv = v*vv
      r = vv*x1
      a = uu*z1-vvv-2*r
      x3 = v*a
      y3 = u*(r-a)-vvv*y1
      z3 = vvv*z1

-- Accepts inverse as input, does not verify. Not meant to be called directly
jacToAff :: (WJCurve e q p, WACurve e q p) => WJPoint e q p -> q -> WAPoint e q p
jacToAff (J x y z) zInv = if z == 0 then O else A (x * zInv^2) (y * zInv^3)

projToAff :: (WPCurve e q p, WACurve e q p) => WPPoint e q p -> q -> WAPoint e q p
projToAff (P x y z) zInv = if z == 0 then O else A (x * zInv) (y * zInv)

-- TODO specialized formulae for these
instance EACurve e q p => FastDouble (EAPoint e q p) where
  dbl' = dbl

instance EACurve e q p => NormalAdd (EAPoint e q p) where
  type Normalized (EAPoint e q p) = (EAPoint e q p)
  normalize xs = xs
  nrmlAdd = add

instance EPCurve e q p => FastDouble (EPPoint e q p) where
  dbl' = dbl

instance EPCurve e q p => NormalAdd (EPPoint e q p) where
  type Normalized (EPPoint e q p) = (EPPoint e q p)
  normalize xs = xs
  nrmlAdd = add

-------------------------------
-- Wrapper fo Cryptonite points

--newtype ECWrap a = ECWrap (EC.Point a)
--  deriving (Eq, Show)

--instance Num (EC.Scalar) where
--  (+) = EC.scalarAdd
--  (*) = EC.scalarMul
--  -- For some reason doesn't have subtraction or negation?????
--  negate x = x * (fromInteger $ -1)
--
--  -- Not sure how this fails..
--  fromInteger x = ECErr.onCryptoFailure (error "Failed EC fromInteger") Prelude.id $ EC.scalarFromInteger x

--------------------------------
-- Generic Commitment Classes --

-- The SplitScalar and FastInnerProduct classes abstract the internal logic of
-- how to compute commitments. Currently they are selected based on the scalar
-- field type, as FastPrime => HasCM. May need wrappers in the future.

type CanCommit v s 
  = (Show v, Eq v, Integral s, Fractional s
  , Show (Normalized v), PrimeField s
  , VectorSpace v, s ~ Scalar v, Show s, NFData s, NFData v
  , FastInnerProduct v, SplitScalar (Scalar v), Integral (ReducedScalar (Scalar v)))

-- Given a scalar, implements the operations necessary to split the scalar for
-- either GLV using the fast endomorphism and/or rational reduction for the
-- bulletproof chage of basis computations
class PrimeField p => SplitScalar p where
  type ReducedScalar p

  reducedChar :: p -> ReducedScalar p

  -- Needs to behave with the euclidean algorithm in rational
  normScalar :: Either p (ReducedScalar p) -> Integer

  -- Either signed toInteger or decomposeEis
  reduceScalar :: p -> ReducedScalar p

  -- Extract scalar
  extractScalar :: ReducedScalar p -> p

  -- Given n return (a, b) such that a / b = n
  -- Not very fast, but called infrequently so it should be fine for now
  rationalReduceScalar :: Integral (ReducedScalar p) => p -> (ReducedScalar p, ReducedScalar p)
  rationalReduceScalar (x :: p) = (a, b)
    where
      p = toInteger $ G.char x
      pRed = reducedChar x
      cond (r,s) = (normScalar r')^2 > 2 * p
        where r' = Right r :: Either p (ReducedScalar p)
      (a, b) = head $ dropWhile cond $ egcd (pRed, 0) (reduceScalar x, 1)
      
      -- Assumes initial |a| > |b|
      egcd a b = b : egcd b c
        where
          q = fst a `quot` fst b
          c = (fst a - q * fst b, snd a - q * snd b)

  -- TODO I think this is the spot that it makes sense to implement the generic
  -- bit components of the scalar 
  type ScalarDigit p

  -- scalarLength :: p -> Int
  reducedScalarLength :: p -> Int
  getDigit :: p -> Int -> ReducedScalar p -> ScalarDigit p

  -- Should be ceil(len/2)
  rationalReducedScalarLength :: p -> Int

-- Default instance for general elliptic curves
instance KnownNat p => SplitScalar (Prime p) where
  type ReducedScalar (Prime p) = Integer
  
  reducedChar x = toInteger $ G.char x
  normScalar = abs . either reduceScalar Prelude.id
  extractScalar = fromInteger
  
  reduceScalar x = inferSign $ fromP x
    where
      p = toInteger $ G.char x
      inferSign n = if n > (p - n) then -(p - n) else n

  -- Switch to NAF?
  type ScalarDigit (Prime p) = Bool

  -- TODO might not work
  reducedScalarLength x = 256
  rationalReducedScalarLength x = 129

  getDigit _ b n = testBit (abs n) b


-- FastPrime currently only used for SECP256K1, so this works. Uses a split
-- representation by the cm endomorphism
instance (ValidFastPrime p, HasEis (FastPrime p)) => SplitScalar (FastPrime p) where
  type ReducedScalar (FastPrime p) = Eis Integer

  -- NOTE conj is important to make egcd work
  reducedChar = conjEis . charEis
  normScalar = either (normEis . reduceScalar) normEis
  reduceScalar = decomposeEis
  extractScalar = recomposeEis . fmap fromInteger

  type ScalarDigit (FastPrime p) = (Bool, Bool)

  reducedScalarLength _ = 129
  rationalReducedScalarLength _ = 65
  getDigit _ n (Eis a b) = (testBit a n, testBit b n)

-- Takes a particular vector space and implements an inner product function that
-- is optimal for the vector space. Encapsulates various techniques to improve
-- like GLV scalars, normalizing points, etc.
class (VectorSpace v, FastDouble v) => FastInnerProduct v where
  -- type ScalarMult v = (Scalar s, v)
  type Basis v
  --type Coeff v      -- Store info for multiplications

  -- Computes the correct point to add based on the digit and adds
  addBasis :: SplitScalar (Scalar v) => ScalarDigit (Scalar v) -> Basis v -> v -> v
  --addBasis :: SplitScalar (Scalar v) => Int -> Coeff v -> Basis v -> v -> v

  -- Given points, construct the basis, meant to be called internally
  normalizeBasis :: [(ReducedScalar (Scalar v), v)] -> [(ReducedScalar (Scalar v), Basis v)]
  --normalizeBasis :: [(ReducedScalar (Scalar v), v)] -> [(Coeff v, Basis v)]

  -- Default behavior is to just normalize and add row-wise
  innerProduct :: SplitScalar (Scalar v) => [(Scalar v, v)] -> v
  innerProduct sgs = go len zeroV
    where
      pxy = fst $ head sgs
      sbs = normalizeBasis $ first reduceScalar <$> sgs
      len = reducedScalarLength pxy
      addBasis' n !v (s, b) = addBasis (getDigit pxy (n-1) s) b v

      -- Add up rows in most to least significance
      go 0 v = v
      go n !v = go (n-1) $ foldl' (addBasis' n) (dbl' v) sbs

  -- TODO reuse normalization?
  -- innerProductNormalized :: SplitScalar (Scalar v) => [Basis v] -> [Scalar v] -> v

  -- Given (s0, s1, 1) ~ (s0', s1', s2') take (s0', v0) and (s1', v1)
  -- and return v2 such that
  -- s0 *^ v0 ^+^ s1 *^ v1 == s2' *^ v2
  projectivePairIP :: SplitScalar (Scalar v) => (ReducedScalar (Scalar v), v) -> (ReducedScalar (Scalar v), v) -> v
  projectivePairIP (s0, g0 :: v) (s1, g1) = go len zeroV
    where
      pxy = undefined :: Scalar v
      sbs = normalizeBasis [(s0, g0), (s1, g1)]
      len = rationalReducedScalarLength pxy
      addBasis' n !v (s, b) = addBasis (getDigit pxy (n-1) s) b v

      -- Add up rows in most to least significance
      go 0 v = v
      go n !v = go (n-1) $ foldl' (addBasis' n) (dbl' v) sbs

instance (KnownNat p, Curve f c e q (Prime p), NormalAdd (Point f c e q (Prime p))) 
         => FastInnerProduct (Point f c e q (Prime p)) where
  -- Sign is just incorporated into the point
  type Basis (Point f c e q (Prime p)) = Normalized (Point f c e q (Prime p))

  addBasis True p !q = p `nrmlAdd` q
  addBasis False _ !q = q

  -- Extract signs and then normalize according to point representation
  normalizeBasis sgs = zip ss $ normalizes gs
    where 
      sign (n, g) = if n < 0 then (-n, negateV g) else (n, g)
      (ss, gs) = unzip $ sign <$> sgs

-- The type class is conditioned on field type, as above, since FastPrime is
-- currently only implemented for curves with complex multiplication. Will
-- probably need some kind wrapper to be fully general.
type NPFP f c e q p = Normalized (Point f c e q (FastPrime p))

instance (ValidFastPrime p, CMCurve f c e q (FastPrime p), SplitScalar (FastPrime p)
         , NormalAdd (Point f c e q (FastPrime p)), CMMult (Normalized (Point f c e q (FastPrime p)))) 
         => FastInnerProduct (Point f c e q (FastPrime p)) where
  -- Stores a pair of points and sign difference
  type Basis (Point f c e q (FastPrime p)) = (Bool, (NPFP f c e q p, NPFP f c e q p))

  -- Cache p11 because in the case the scalar is a + b unity3, signum a /=
  -- signum b the point requires an addition.
  addBasis (False, False) _ !q = q
  addBasis (True, False) (s, (p00, p11)) !q = p00 `nrmlAdd` q
  addBasis (False, True) (s, (p00, p11)) !q = negIfV s (cmMul p00) `nrmlAdd` q
  addBasis (True, True)  (s, (p00, p11)) !q = p11 `nrmlAdd` q

  normalizeBasis sgs = zip ss $ zip bs $ pairs $ normalizes $ unPairs gs
    where 
      (ss, (bs, gs)) = second unzip $ unzip $ sign <$> sgs
      sign ((Eis a b), g) = (eis', (s0 /= s1, (g', h')))
        where
          s0 = signum a
          s1 = signum b
          eis' = Eis (abs a) (abs b)
          g' = negIfV (s0 == -1) g
          h' = if s0 == s1 
                 then negateV $ cmMul $ cmMul g'
                 else g' ^-^ cmMul g'

--------------
-- Openings --

-- Represents an opened commitment, from which we can derive the actual
-- commitment if defined over a suitable vector space
class Bifunctor c => Opening c where
  -- Behaves like a fold over pairs
  openWith :: CanCommit v s => c v s -> (s -> v -> a) -> (a -> b -> b) -> b -> b
  openWith c m p z = dotWith ss gs m p z
    where (ss, gs) = unzip $ openToList c

  -- Can define this instead
  openToList :: CanCommit v s => c v s -> [(s, v)]
  openToList c = openWith c (,) (:) []
  
-- Commit using shamir's trick
commit :: (CanCommit v s, Opening c) => c v s -> v
commit c = innerProduct (openToList c)

sumWith :: Foldable f => (a -> b -> b) -> f a -> b -> b
sumWith = flip . foldl' . flip

--dotWith :: (Foldable f, Zip f, CanCommit v s) => (s -> v -> a) -> (a -> b -> b) -> f s -> f v -> b -> b
dotWith :: (Foldable f, Zip f, CanCommit v s) => f s -> f v -> (s -> v -> a) -> (a -> b -> b) -> b -> b
dotWith xs ys (*:) (+:) = sumWith (+:) $ zipWithDef'' (*:) 0 zeroV xs ys

-- Compose commitment operations
type CommitFold v s = forall a b. (s -> v -> a) -> (a -> b -> b) -> b -> b

composeWith :: CommitFold v s -> CommitFold v s -> CommitFold v s
composeWith a b (+:) (*:) z = a (+:) (*:) $ b (+:) (*:) z

(.:) :: CommitFold v s -> CommitFold v s -> CommitFold v s
(.:) = composeWith

-- Church encoding of a commitment, convenient for unamed types
newtype ChurchCommit v s = ChC { runChC :: forall a b. (s -> v -> a) -> (a -> b -> b) -> b -> b }
  deriving Functor

instance Bifunctor ChurchCommit where
  bimap f g (ChC c) = ChC $ \m -> c (\s v -> m (g s) (f v))

instance Opening ChurchCommit where
  openWith = runChC

-- Basic commitment is a pair of scalar and vector
data CommitPoint v s = CP { scalarCP :: !s, basisCP :: !v }
  deriving (Eq, Show, Functor, Foldable)

-- Pair of a scalar and curve point
instance Bifunctor CommitPoint where
  bimap f g (CP s b) = CP (g s) (f b)

mapScalarCP :: CommitPoint v s -> (s -> t) -> CommitPoint v t
mapScalarCP = flip second 

instance Opening CommitPoint where
  openWith (CP s g) (*:) (+:) !z = (s *: g) +: z

-- Pedersen scalar commitments have blinding
data PedersenScalar v s = PS { blindingPS :: !(CommitPoint v s), scalarPS :: !(CommitPoint v s) }
  deriving (Eq, Show, Functor)

makePS :: CanCommit v s => s -> v -> s -> v -> PedersenScalar v s
makePS bl blG sc scG = PS (CP bl blG) (CP sc scG)

instance Bifunctor PedersenScalar where
  bimap f g (PS bl sc) = PS (bimap f g bl) (bimap f g sc)

instance Opening PedersenScalar where
  -- commit (PS (CP bs bg) (CP ss sg)) = shamir bg bs sg ss
  openWith (PS b s) (*:) (+:) !z = let cw x z = openWith x (*:) (+:) z in cw s $ cw b z

data PedersenScalarPair v s = PSP { blindingPSP :: CommitPoint v s, pairPSP :: (CommitPoint v s, CommitPoint v s) }
  deriving (Eq, Show, Functor)

makePSP :: CanCommit v s => s -> v -> s -> v -> s -> v -> PedersenScalarPair v s
makePSP bl blG sc0 scG0 sc1 scG1 = PSP (CP bl blG) (CP sc0 scG0, CP sc1 scG1)

instance Bifunctor PedersenScalarPair where
  bimap f g (PSP bl sc) = PSP (bimap f g bl) (dup (bimap f g) sc)

instance Opening PedersenScalarPair where
  openWith (PSP b (s0, s1)) (*:) (+:) !z = let cw x z = openWith x (*:) (+:) z in cw s1 $ cw s0 $ cw b z

-- Doesn't have blinding, used for Bulletproof protocols that handle blinding
-- internally to the protocol
data PedersenScalarVector f v s = PSV { scalarPSV :: (CommitPoint v s), vectorPSV :: (f v s) }
  deriving (Eq, Show, Functor)

makePSV :: CanCommit v s => s -> v -> f v s -> PedersenScalarVector f v s
makePSV sc scG = PSV (CP sc scG)

updatePSV :: PedersenScalarVector f v s -> t -> f v t -> PedersenScalarVector f v t
updatePSV (PSV s _) s' c' = PSV (mapScalarCP s $ const s') c'

instance Bifunctor f => Bifunctor (PedersenScalarVector f) where
  bimap f g (PSV sc xs) = PSV (bimap f g sc) (bimap f g xs)

instance Opening f => Opening (PedersenScalarVector f) where
  openWith (PSV s v) (*:) (+:) !z = openWith v (*:) (+:) $ cw s z
    where cw x = openWith x (*:) (+:)

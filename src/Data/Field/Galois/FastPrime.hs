{-# LANGUAGE DataKinds, MagicHash, KindSignatures, TypeFamilies #-}
{-# LANGUAGE UnboxedTuples, OverloadedStrings, ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude, TypeApplications, TypeOperators #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.Field.Galois.FastPrime where

import Prelude (Show(..))

import Protolude hiding (Semiring, natVal, rem, get, put)
--import Protolude (Show(..))

--import Data.Field.Galois
import Data.Binary
import System.Random
import Test.QuickCheck.Arbitrary
import Text.PrettyPrint.Leijen.Text hiding (char, (<$>))

import Data.Euclidean as S (Euclidean(..), GcdDomain)
import Data.Field (Field)
import Data.Field.Galois (GaloisField(..), PrimeField(..))
import Data.Group (Group(..))
import Data.Semiring (Ring(..), Semiring(..))
import GHC.Natural (Natural(..))
import GHC.TypeNats (natVal, Nat, KnownNat)
import qualified GHC.TypeNats as TN

import GHC.Integer.GMP.Internals
import GHC.Generics

import Test.QuickCheck

-- import qualified Debug.Trace as DT

import Data.Field.Galois.FastPrime.Internal

import GHC.Exts (isTrue#, word2Int#, int2Word#, Word(..))

import Data.Field.Eis
import Data.Bits
import Data.List (minimumBy)

-- Implements faster field operations for primes of the form p = 2^256 - r for
-- small r, i.e. r^2 < 2p. Multiplication can be done considerably faster for
-- such primes than for general primes, and both the fields associated to the
-- SECP256K1[Dual] curves are of this form.
--
-- Besides these higher level optimizations, all operations are done on unboxed
-- 4-tuples of 64 bit words. See FastPrime.Internal for the details of this.
--
-- NOTE all code is implemented in Haskell, better performance is probably
-- acheivable by FFI with libsecp256k1.

-- Stores unboxed 4-tuple of 64 bit words
data FastPrime (p :: Nat) = FP# { unFP# :: Field# }

fp0 :: FastPrime p
fp0 = FP# (wordToField# (int2Word# 0#))

data ProxyNat (n :: Nat) = ProxyNat

-- TODO also 2^256 - p < 2^130
type ValidFastPrime p = (KnownNat p, p TN.<= (2 TN.^ 256))

prime# :: forall t p. ValidFastPrime p => t p -> Prime#
prime# _ = let (NatJ# pBigNat) = natVal (ProxyNat @p) in uncheckedBigNatToField# pBigNat
{-# INLINE prime# #-}

primeInc# :: forall t p. ValidFastPrime p => t p -> PrimeInc#
primeInc# _ = let (NatJ# pBigNat) = natVal (ProxyNat @(p TN.+ 1)) in uncheckedBigNatToField# pBigNat
{-# INLINE primeInc# #-}

primeBigNat :: forall t p. ValidFastPrime p => t p -> BigNat
primeBigNat _ = let (NatJ# pBigNat) = natVal (ProxyNat @p) in pBigNat
{-# INLINE primeBigNat #-}

primeInteger :: forall t p. ValidFastPrime p => t p -> Integer
primeInteger _ = let (NatJ# pBigNat) = natVal (ProxyNat @p) in Jp# pBigNat
{-# INLINE primeInteger #-}

primeNatural :: forall t p. ValidFastPrime p => t p -> Natural
primeNatural _ = natVal (ProxyNat @p)
{-# INLINE primeNatural #-}

-- Uses 2^257 to prevent insufficiently large BigNat, truncates the upper bit so
-- we get: 2^(257) - (2^256 - r) = 2^256 + r = r mod 2^129
offset# :: forall t p. ValidFastPrime p => t p -> PrimeOffset#
offset# _ = let (NatJ# rBigNat) = natVal (ProxyNat @((2 TN.^ 257) TN.- p)) in uncheckedBigNatToTrunc# rBigNat
{-# INLINE offset# #-}

-- NOTE this might be wrong if we don't truncate
offsetInteger :: forall t p. ValidFastPrime p => t p -> Integer
offsetInteger _ = let (NatJ# pBigNat) = natVal (ProxyNat @( (2 TN.^ 257) TN.- p )) in (Jp# pBigNat) `mod` 2^129
{-# INLINE offsetInteger #-}

---------------
-- Instances --
---------------

-- Should allow generic deriving other typical classes
instance ValidFastPrime p => Generic (FastPrime p) where
  type Rep (FastPrime p) = K1 C Integer

  from (FP# x#) = K1 $ fieldToInteger# x#
  to (K1 n) = FP# (integerToField# (prime# px) (offset# px) (primeInc# px) (primeBigNat px) n)
    where px = Proxy @p

-- NOTE assumes 64 bit words
instance ValidFastPrime p => Binary (FastPrime p) where
  put (FP# (# x0#, x1#, x2#, x3# #)) = put (W# x0#) <> put (W# x1#) <> put (W# x2#) <> put (W# x3#)
  get = do
    W# x0# <- get
    W# x1# <- get
    W# x2# <- get
    W# x3# <- get
    -- Hack to do fast mod p reduction, since all representable 256 bit values
    -- less than 2p, addition reduction is valid
    return $ 0 + (FP# (# x0#, x1#, x2#, x3# #))

instance (ValidFastPrime p) => Hashable (FastPrime p)
instance (ValidFastPrime p) => NFData (FastPrime p)

instance (ValidFastPrime p) => Ord (FastPrime p) where
  compare a b = compare (toInteger a) (toInteger b)

instance {- (ValidFastPrime p) => -} Show (FastPrime p) where
  show (FP# x#) = Prelude.show $ fieldToInteger# x# -- toInteger

-- NOTE assumes reduced representatives
--instance (ValidFastPrime p) => Eq (FastPrime p) where
instance {- (ValidFastPrime p) => -} Eq (FastPrime p) where
  FP# x# == FP# y# = isTrue# (word2Int# (eq256# x# y#))
  {-# INLINE (==) #-}

-- Prime fields are convertible.
instance (ValidFastPrime p) => PrimeField (FastPrime p) where
  fromP (FP# x) = fieldToInteger# x
  {-# INLINE fromP #-}

instance (ValidFastPrime p) => GaloisField (FastPrime p) where
  char = primeNatural
  {-# INLINE char #-}
  deg  = const 1
  {-# INLINE deg #-}
  frob = identity
  {-# INLINE frob #-}

-- Prime fields are multiplicative groups.
instance (ValidFastPrime p) => Group (FastPrime p) where
  invert = recip
  {-# INLINE invert #-}
  pow (FP# x#) n = FP# (powFieldInteger# (prime# px) (offset# px) (primeBigNat px) x# (toInteger n))
    where px = ProxyNat @p
  {-# INLINE pow #-}

-- Prime fields are multiplicative monoids.
instance (ValidFastPrime p) => Monoid (FastPrime p) where
  mempty = fromIntegral 1
  {-# INLINE mempty #-}

-- Prime fields are multiplicative semigroups.
instance (ValidFastPrime p) => Semigroup (FastPrime p) where
  (<>)   = (*)
  {-# INLINE (<>) #-}
  stimes = flip pow
  {-# INLINE stimes #-}

-- 

----------------------------------
-- Fast Prime Fields are Primitive
-- TODO
-- instance ValidFastPrime p => Prim (FastPrime p) where
--   sizeOf# _ = 256#
--   alignment# _ = 

-- Used to instantiate Eis, kinda confusing, want to use smaller factors in the
-- actual multiplciation, so xInt * charEis x because of how they currently are
-- TODO use 129 by 256 bit multiplications instead of full 256 bit for factors?
--
-- NOTE this is the same as the Eis quot function with the integer quot replaced
-- by a 256 bit shift
decomposeFastPrimeEis :: (ValidFastPrime p, HasEis (FastPrime p)) => FastPrime p -> Eis Integer
decomposeFastPrimeEis x = xInt - q * pFac
  where
    pInt = toInteger $ char x
    pFac = conjEis $ charEis x
    xInt = Eis (toInteger x) 0      -- TODO sign?
    Eis u v = xInt * conjEis pFac
    qU' = unsafeShiftR u 256
    qV' = unsafeShiftR v 256
      
    -- Does this work?
    q = Eis (round u qU') (round v qV')
    round n q = res
      where
        -- Want the q that minimizes r. Assume the signs are the same
        r = n - pInt * q
        res = case (abs r > abs (r + pInt), abs r > abs (r - pInt)) of
                (True, _) -> q - 1
                (_, True) -> q + 1
                _ -> q

-- Used to invoke faster square function
fastSqr :: (ValidFastPrime p) => FastPrime p -> FastPrime p
fastSqr (FP# x# :: FastPrime p) = let px = ProxyNat @p in FP# (sqrField# (prime# px) (offset# px) x#)

-- NOTE should only be used if the prime p = 4 n + 3
type Sqrt p = (TN.Mod p 4 ~ 3)

fastSqrt :: (ValidFastPrime p, Sqrt p) => FastPrime p -> Maybe (FastPrime p)
fastSqrt (x :: FastPrime p) = if fastSqr r == x then Just r else Nothing
  where
    n = (primeInteger (ProxyNat @p) + 1) `div` 4
    r = pow x n



-------------------------------------------------------------------------------
-- Numeric instances
-------------------------------------------------------------------------------

-- Prime fields are fractional.
instance (ValidFastPrime p) => Fractional (FastPrime p) where
  recip z | z == fp0  = divZeroError
  recip (FP# x#)      = let px = ProxyNat @p in FP# (invField# (primeBigNat px) x#)
  {-# INLINE recip #-}

  FP# x# / FP# y# = let px = ProxyNat @p in FP# (divField# (prime# px) (offset# px) (primeBigNat px) x# y#)
  {-# INLINE (/) #-}

  fromRational (x:%y) = fromInteger x / fromInteger y
  {-# INLINE fromRational #-}

-- Prime fields are numeric.
instance (ValidFastPrime p) => Num (FastPrime p) where
  FP# x# + FP# y# = let px = ProxyNat @p in FP# (addField# (prime# px) (offset# px) x# y#)
  {-# INLINE (+) #-}
  
  FP# x# * FP# y# = let px = ProxyNat @p in FP# (mulField# (prime# px) (offset# px) x# y#)
  {-# INLINE (*) #-}
  
  --FP# x# - FP# y# = let px = ProxyNat @p in FP# (subField# (prime# px) (offset# px) (primeInc# px) x# y#)
  x - y = x + Protolude.negate y
  {-# INLINE (-) #-}
  
  negate (FP# x#) = let px = ProxyNat @p in FP# (negField# (prime# px) (offset# px) (primeInc# px) x#)
  {-# INLINE negate #-}
  
  fromInteger n = let px = ProxyNat @p in FP# (integerToField# (prime# px) (offset# px) (primeInc# px) (primeBigNat px) n) 
  {-# INLINE fromInteger #-}
  
  abs           = panic "Prime.abs: not implemented."
  signum        = panic "Prime.signum: not implemented."

-------------------------------------------------------------------------------
-- Semiring instances
-------------------------------------------------------------------------------

-- Prime fields are Euclidean domains.
instance (ValidFastPrime p) => Euclidean (FastPrime p) where
  degree  = panic "Prime.degree: not implemented."
  quotRem x y = (x/y, 0) -- (flip (,) 0 .) . (/)
  {-# INLINE quotRem #-}

-- Prime fields are fields.
instance (ValidFastPrime p) => Field (FastPrime p)

-- Prime fields are GCD domains.
instance (ValidFastPrime p) => GcdDomain (FastPrime p)

-- Prime fields are rings.
instance (ValidFastPrime p) => Ring (FastPrime p) where
  negate = Protolude.negate
  {-# INLINE negate #-}

-- Prime fields are semirings.
instance (ValidFastPrime p) => Semiring (FastPrime p) where
  fromNatural = fromIntegral
  {-# INLINABLE fromNatural #-}
  one         = fromIntegral 1
  {-# INLINE one #-}
  plus        = (+)
  {-# INLINE plus #-}
  times       = (*)
  {-# INLINE times #-}
  zero        = fp0
  {-# INLINE zero #-}

-------------------------------------------------------------------------------
-- Other instances
-------------------------------------------------------------------------------

-- Prime fields are arbitrary.
instance (ValidFastPrime p) => Arbitrary (FastPrime p) where
  arbitrary = fromInteger <$> choose (0, fromIntegral (-1))
  {-# INLINABLE arbitrary #-}

-- Prime fields are bounded.
instance (ValidFastPrime p) => Bounded (FastPrime p) where
  maxBound = fromIntegral (-1)
  {-# INLINE maxBound #-}
  minBound = fromIntegral 0
  {-# INLINE minBound #-}

-- Prime fields are enumerable.
instance (ValidFastPrime p) => Enum (FastPrime p) where
  fromEnum = fromIntegral
  {-# INLINABLE fromEnum #-}
  toEnum   = fromIntegral
  {-# INLINABLE toEnum #-}

-- Prime fields are integral.
instance (ValidFastPrime p) => Integral (FastPrime p) where
  quotRem   = S.quotRem     -- TODO what does this actually do??
  {-# INLINE quotRem #-}
  toInteger = fromP
  {-# INLINE toInteger #-}

-- Prime fields are pretty.
instance (ValidFastPrime p) => Pretty (FastPrime p) where
  pretty (FP# x) = pretty $ fieldToInteger# x

-- Prime fields are random.
instance (ValidFastPrime p) => Random (FastPrime p) where
  random         = randomR (fromIntegral 0, fromIntegral (-1))
  {-# INLINABLE random #-}
  randomR (a, b) = first fromInteger . randomR (toInteger a, toInteger b)
  {-# INLINABLE randomR #-}

-- Prime fields are real.
instance (ValidFastPrime p) => Real (FastPrime p) where
  toRational = fromIntegral
  {-# INLINABLE toRational #-}

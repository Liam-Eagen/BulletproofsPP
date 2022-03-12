{-# LANGUAGE UndecidableInstances, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Uses Fast(er) field arithmetic

module Data.Curve.Weierstrass.FastSECP256K1
  ( module Data.Curve.Weierstrass
  , Point(..)
  , module Data.Curve.Weierstrass.FastSECP256K1
  ) where

import Data.Bits
import Data.List (minimumBy)
import Data.Field.Galois
import qualified Data.Field.Galois as G (char)
import Data.Field.Galois.FastPrime
import GHC.Natural (Natural)

import Data.Field.Eis
import Data.Curve.CM
import Data.Curve.Weierstrass
import qualified Data.Curve.Weierstrass.SECP256K1 as SECP256K1

-- TODO want to compute automatically without this
import GHC.Exts

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data FastSECP256K1

--type Q = 115792089237316195423570985008687907853269984665640564039457584007908834671663
type Q = SECP256K1.Q
type Fq = FastPrime Q

instance HasEis Fq where
  -- TODO compile time simplify?
  unity3 = fromInteger (55594575648329892869085402983802832744385952214688224221778511981742606582254)

  charEis _ = Eis (303414439467246543595250775667605759171) (-64502973549206556628585045361533709078)

  -- We can simplify the division by noting that p ~ 2^256 and the halves are <
  -- 128 bits. This means u and v are 2^(384) bits
  decomposeEis = decomposeFastPrimeEis

--type R = 115792089237316195423570985008687907852837564279074904382605163141518161494337
type R = SECP256K1.R
type Fr = FastPrime R

instance HasEis Fr where
  -- TODO compile time simplify?
  unity3 = fromInteger (37718080363155996902926221483475020450927657555482586988616620542887997980018)

  -- NOTE this differs by a unit from Fq (i.e. last digit is 7 not 8)
  charEis _ = Eis (303414439467246543595250775667605759171) (-64502973549206556628585045361533709077)

  -- We can simplify the division by noting that p ~ 2^256 and the halves are <
  -- 128 bits. This means u and v are 2^(384) bits
  decomposeEis = decomposeFastPrimeEis

-- Has the same curve equation
instance Curve 'Weierstrass c FastSECP256K1 Fq Fr => WCurve c FastSECP256K1 Fq Fr where
  a_ = const _a
  {-# INLINABLE a_ #-}
  b_ = const _b
  {-# INLINABLE b_ #-}
  h_ = const _h
  {-# INLINABLE h_ #-}
  q_ = const _q
  {-# INLINABLE q_ #-}
  r_ = const _r
  {-# INLINABLE r_ #-}

-- | Affine FastSECP256K1 curve point.
type PA = WAPoint FastSECP256K1 Fq Fr

instance WACurve FastSECP256K1 Fq Fr where
  gA_ = gA
  {-# INLINABLE gA_ #-}

-- | Jacobian FastSECP256K1 point.
type PJ = WJPoint FastSECP256K1 Fq Fr

instance WJCurve FastSECP256K1 Fq Fr where
  gJ_ = gJ
  {-# INLINABLE gJ_ #-}

-- | Projective FastSECP256K1 point.
type PP = WPPoint FastSECP256K1 Fq Fr

instance WPCurve FastSECP256K1 Fq Fr where
  gP_ = gP
  {-# INLINABLE gP_ #-}

instance WCurve c FastSECP256K1 Fq Fr => CMWCurve c FastSECP256K1 Fq Fr

-------------------------------------------------------------------------------
-- Parameters
-------------------------------------------------------------------------------

-- | Coefficient @A@ of SECP256K1 curve.
_a :: Fq
_a = 0x0
{-# INLINABLE _a #-}

-- | Coefficient @B@ of SECP256K1 curve.
_b :: Fq
_b = 0x7
{-# INLINABLE _b #-}

-- | Cofactor of SECP256K1 curve.
_h :: Natural
_h = 0x1
{-# INLINABLE _h #-}

-- | Characteristic of FastSECP256K1 curve.
_q :: Natural
-- _q = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
_q = SECP256K1._q
{-# INLINABLE _q #-}

-- | Order of FastSECP256K1 curve.
_r :: Natural
-- _r = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
_r = SECP256K1._r
{-# INLINABLE _r #-}

-- There is no canonical basepoint for this curve, so I picked the smallest value of
-- x that generated a valid curve point, x = 1, and the y value with the smaller minimal
-- positive integer representative.

-- | Coordinate @X@ of FastSECP256K1 curve.
_x :: Fq
_x = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
{-# INLINABLE _x #-}

-- | Coordinate @Y@ of FastSECP256K1 curve.
_y :: Fq
_y = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
{-# INLINABLE _y #-}

-- | Generator of affine FastSECP256K1 curve.
gA :: PA
gA = A _x _y
{-# INLINABLE gA #-}

-- | Generator of Jacobian FastSECP256K1 curve.
gJ :: PJ
gJ = J _x _y 1
{-# INLINABLE gJ #-}

-- | Generator of projective FastSECP256K1 curve.
gP :: PP
gP = P _x _y 1
{-# INLINABLE gP #-}

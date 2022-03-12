{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module Encoding where

import GHC.TypeNats
import Data.Proxy
import Data.Bits (testBit, unsafeShiftL, unsafeShiftR)
import Data.VectorSpace
import Data.Foldable (foldl')
import Control.Monad (replicateM)

import Data.Bits
import Data.Binary
import Data.Binary.Get (runGet)
import Data.Binary.Put (runPut)
import qualified Data.ByteString.Lazy as BS

import Data.Field.Galois hiding ((*^), (/), recip, Binary(..))
import Data.Curve
import Data.Curve.Weierstrass
import qualified Data.Curve as Curve

import qualified Data.Vector as V
import Data.Field.BatchInverse

import Data.Field.Eis
import Data.Curve.CM

import Utils

-- Binary enode lists of curve points and scalars
--class (Curve f c e q r, Binary q, Binary r) => BinaryEncodeCurve (Point f c e q r) where
class BinaryEncodeCurve v where
  type BECScalar v
  
  -- Write monadic functions
  putScalarsCurvePoints :: [BECScalar v] -> [v] -> Put
  getScalarsCurvePoints :: Int -> Int -> Get (Maybe ([BECScalar v], [v]))
  
-- Should be inverse via:
-- scLen = length scs, ptLen = length pts
--
-- bs = encodeScalarsCurvePoints scs pts
-- Just (scs, pts) = decodeScalarsCurvePoints scLen ptLen bs
encodeScalarsCurvePoints :: BinaryEncodeCurve v => [BECScalar v] -> [v] -> BS.ByteString
encodeScalarsCurvePoints scs pts = runPut $ putScalarsCurvePoints scs pts

decodeScalarsCurvePoints :: BinaryEncodeCurve v => Int -> Int -> BS.ByteString -> Maybe ([BECScalar v], [v])
decodeScalarsCurvePoints sN pN bs = runGet (getScalarsCurvePoints sN pN) bs

-- Convenience constaint
type CanEncode' c e q s = ( WCurve c e q s, WACurve e q s
                          , BECScalar (WPoint c e q s) ~ s
                          , Binary q, Binary s, Integral q )

type CanEncode c e q v s = ( WCurve c e q s, WACurve e q s, WPoint c e q s ~ v
                           , BinaryEncodeCurve v, BECScalar v ~ s
                           , Binary q, Binary s, Integral q )


-- Encode weierstrass points with sign bit seperately
instance (CanEncode' c e q r) => BinaryEncodeCurve (WPoint c e q r) where
  type BECScalar (WPoint c e q r) = r

  getScalarsCurvePoints sN cN = do
    ss <- replicateM sN get
    cs <- decodeCommitments cN
    return $ (ss, ) <$> cs
  
  putScalarsCurvePoints ss cs = do
    mapM_ put ss
    encodeCommitments cs

-- This just assumes that the prime is 256 bits.
instance KnownNat p => Binary (Prime p) where
  get = do
    quad <- get :: Get (Word, Word, Word, Word)
    let (a0, a1, a2, a3) = mapQuad toInteger quad
    return $ toP $ a0 + unsafeShiftL a1 64 + unsafeShiftL a2 128 + unsafeShiftL a3 192
  put x = do
    let n = toInteger x
    let (q0, a0) = n  `divMod` (2^64)
    let (q1, a1) = q0 `divMod` (2^64)
    let (a3, a2) = q1 `divMod` (2^64)
    let quad = mapQuad fromInteger (a0, a1, a2, a3) :: (Word, Word, Word, Word)
    put quad

-----------------
-- Implementation

-- Extract packed bits
bitUnpack :: [Word8] -> [Bool]
bitUnpack ws = ws >>= btEx
  where btEx w = [ testBit w n | n <- [0..7] ]

-- If b is true, use larger y coordinate
fromXWithSign :: CanEncode c e q v s => q -> Bool -> Maybe v
fromXWithSign x b = do
  p <- pointX x
  let A _ y = toA p
  let yInt = toInteger y
  let negYInt = toInteger $ -y
  return $ if (yInt > negYInt) `xor` b then inv p else p -- p else inv p

-- pack bits
bitPack :: [Bool] -> [Word8]
bitPack bs = btEm 0 0 <$> chunks 8 bs
  where
    btEm n w [] = w
    btEm n w (False:bs) = btEm (n+1) w bs
    btEm n w (True:bs)  = btEm (n+1) (setBit w n) bs

getXAndSign :: CanEncode c e q v s => v -> (q, Bool)
getXAndSign p = (x, yInt > negYInt)
  where
    A x y = toA p
    yInt = toInteger y
    negYInt = toInteger $ -y

decodeCommitments :: CanEncode c e q v s => Int -> Get (Maybe [v])
decodeCommitments n = do
  -- Figure out how many bytes of sign information
  let nSignBytes = let (q, r) = n `divMod` 8 in if r /= 0 then q + 1 else q
  signs <- replicateM nSignBytes get :: Get [Word8]

  -- Get x coordinates and convert to points
  xs <- replicateM n get
  return $ sequence $ zipWith fromXWithSign xs $ bitUnpack signs

encodeCommitments :: CanEncode c e q v s => [v] -> Put
encodeCommitments vs = do
  let (xs, ss) = unzip $ getXAndSign <$> vs
  mapM_ put $ bitPack ss
  mapM_ put xs

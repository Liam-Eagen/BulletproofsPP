{-# LANGUAGE BangPatterns, MagicHash, UnboxedTuples #-}

module Data.Field.Galois.FastPrime.Internal where

--import GHC.Word
-- import GHC.Prim
import GHC.Exts hiding (Word64#, F#)
import GHC.Natural
import GHC.Integer
import GHC.Integer.GMP.Internals

import Debug.Trace

--
-- This file implements 256 bit arithmetic modulo a prime p representable as 
-- p = 2^256 - r such that r^2 < 2 p. This is true of both primes associated to
-- the SECP256k1 curves. Represents the primes as 4 limbs of 64 bytes and
-- performs addition, subtraction and multiplication without explicitly calling
-- modulo. Division is not currently optimized. This does not take full
-- advantage of the optimization potential, but it should be faster than using a
-- ByteArray# backend like Integer/Natural.

-- NOTE assumes Word is 64 bytes.
-- Field x0 x1 x2 x3 -> x0 + 2^64 x1 + 2^128 x2 + 2^192 x3
-- data Field = F# { unF# :: Word256# }

-- 0xffffffffffffffff
-- 0xfffffffffffffffe
-- 0xbaaedce6af48a03b
-- 0xbfd25e8cd0364141

--  -- Modulus
--  p =    F# (# int2Word# 0xbfd25e8cd0364141#
--            ,  int2Word# 0xbaaedce6af48a03b#
--            ,  int2Word# 0xfffffffffffffffe#
--            ,  int2Word# 0xffffffffffffffff# #)
--  
--  -- Modulus plus one, for subtraction/negation
--  pPlus1 = F# (# int2Word# 0xbfd25e8cd0364142#
--              ,  int2Word# 0xbaaedce6af48a03b#
--              ,  int2Word# 0xfffffffffffffffe#
--              ,  int2Word# 0xffffffffffffffff# #)
--  
--  -- modulus as a big nat for modular inversion/reduction
--  pBigNat = fieldToBigNat# (unF# p)
--  
--  -- 2^256 - p = r
--  r =    F# (# int2Word# 0x402da1732fc9bebf#
--            ,  int2Word# 0x4551231950b75fc4#
--            ,  int2Word# 0x1#
--            ,  int2Word# 0x0# #)
--  
--  -- 2 r
--  rDbl = F# (# int2Word# 0x805b42e65f937d7e#
--            ,  int2Word# 0x8aa24632a16ebf88#
--            ,  int2Word# 0x2#
--            ,  int2Word# 0x0# #)
--  
--  -- Lower primitive third root of unity, other one is w^2 = -w - 1
--  -- 5363ad4cc05c30e0
--  -- a5261c028812645a
--  -- 122e22ea20816678
--  -- df02967c1b23bd72
--  unity3 :: Field
--  unity3 = F# (# int2Word# 0xdf02967c1b23bd72#
--              ,  int2Word# 0x122e22ea20816678#
--              ,  int2Word# 0xa5261c028812645a#
--              ,  int2Word# 0x5363ad4cc05c30e0# #)
--  
--  -- Both 00 and 11 are the same
--  -- 3086d221a7d46bcd
--  -- e86c90e49284eb15
--  unity3Matdd :: Field
--  unity3Matdd = F# (# int2Word# 0xe86c90e49284eb15#
--                   ,  int2Word# 0x3086d221a7d46bcd#
--                   ,  int2Word# 0x0#
--                   ,  int2Word# 0x0# #)
--  
--  -- Negation of value
--  -- 1
--  -- 14ca50f7a8e2f3f6
--  -- 57c1108d9d44cfd8
--  --
--  -- ffffffffffffffff
--  -- fffffffffffffffd
--  -- a5e48bef0665ac45
--  -- 68114dff32f17169
--  unity3Mat01 :: Field
--  unity3Mat01 = F# (# int2Word# 0x57c1108d9d44cfd8#
--                   ,  int2Word# 0x14ca50f7a8e2f3f6#
--                   ,  int2Word# 0x1#
--                   ,  int2Word# 0x0# #)
--  
--  -- e4437ed6010e8828
--  -- 6f547fa90abfe4c3
--  unity3Mat10 :: Field
--  unity3Mat10 = F# (# int2Word# 0x6f547fa90abfe4c3#
--                   ,  int2Word# 0xe4437ed6010e8828#
--                   ,  int2Word# 0x0#
--                   ,  int2Word# 0x0# #)
--  
--  
--  -----------------
--  -- Test Values --
--  
--  -- TODO move to test file
--  
--  -- 3^160
--  -- 0x304d37f120d696c8
--  -- 0x34550e63d9bb9c14
--  -- 0xb4f9165c9ede434e
--  -- 0x4644e3998d6db881
--  test = F# (# int2Word# 0x4644e3998d6db881#
--            ,  int2Word# 0xb4f9165c9ede434e#
--            ,  int2Word# 0x34550e63d9bb9c14#
--            ,  int2Word# 0x304d37f120d696c8# #)
--  
--  -- (q + 1238349833)/2
--  -- 7fffffffffffffff
--  -- ffffffffffffffff
--  -- 5d576e7357a4501d
--  -- dfe92f468d02fca5
--  test2 = F# (# int2Word# 0xdfe92f468d02fca5#
--             ,  int2Word# 0x5d576e7357a4501d#
--             ,  int2Word# 0xffffffffffffffff#
--             ,  int2Word# 0x7fffffffffffffff# #)

-- TODO move to newtypes to prevent type errors
type Word1#   = Word64#
type Word2#   = Word64#
type Word64#  = Word#
type Word128# = (# Word64#, Word64# #)
type Word129# = (# Word1#, Word64#, Word64# #)
type Word256# = (# Word64#, Word64#, Word64#, Word64# #)

-- Useful for distinguishing return values
type Carry2#   = Word2#
type Carry64#  = Word64#
type Carry128# = Word128#
type Carry129# = Word129#
type Carry256# = Word256#

-- Just takes the first three words, does not clear the higher bits
uncheckedTruncate256to129# :: Word256# -> Word129#
uncheckedTruncate256to129# (# x0#, x1#, x2#, _ #) = (# x0#, x1#, x2# #)
{-# INLINE uncheckedTruncate256to129# #-}

----------------------------
-- Modulo 2^64 operations --

-- Regular addition with carry word
add64Carry# :: Word64# -> Word64# -> (# Carry64#, Word64# #)
add64Carry# = plusWord2#
{-# INLINE add64Carry# #-}

-- Takes a carry input, useful for multiple additions
add64CarryChain# :: (# Carry64#, Word64# #) -> Word64# -> (# Carry64#, Word64# #)
add64CarryChain# (# c0#, x0# #) y0# = (# plusWord# c0# c1#, z0# #)
  where
    -- NOTE docs say plusWord2 is the reverse of addWordC
    (# c1#, z0# #) = plusWord2# x0# y0#
{-# INLINE add64CarryChain# #-}

-- Takes a 64 bit input and a carry and another 64 bit input returns the sum of
-- all three and the total carry.
add64Three# :: Word64# -> Word64# -> Word64# -> (# Carry64#, Word64# #)
add64Three# c0# x0# y0# = (# plusWord# c1# c2#, z1# #)
  where
    (# c1#, z0# #) = plusWord2# x0# y0#
    (# c2#, z1# #) = plusWord2# z0# c0#
{-# INLINE add64Three# #-}

-- This function does the 64 bit multiplication carry for us
mul64WithCarry# :: Word64# -> Word64# -> (# Carry64#, Word64# #)
mul64WithCarry# = timesWord2#
{-# INLINE mul64WithCarry# #-}

-- Given two 64 bit words a and b returns { a', b' } = {a, b} with a' > b' and a
-- flag which is 0x1 if a == a' and 0x0 if a == b'
swap64# :: Word64# -> Word64# -> (# Word1#, Word64#, Word64# #)
swap64# a# b# = (# int2Word# f#, a2#, b2# #)
  where
    f# = geWord# a# b#
    mask0# = int2Word# (notI# f# +# 1#)          -- If a > b all ones
    mask1# = not# mask0#                        
    a2# = and# mask0# a# `xor#` and# mask1# b#
    b2# = and# mask1# a# `xor#` and# mask0# b#
{-# INLINE swap64# #-}

--------------------------
-- Modulo 2^128 operations

-- Given two 128 bit words a and b returns { a', b' } = {a, b} with a' > b' and a
-- flag which is 0x1 if a == a' and 0x0 if a == b'
swap128# :: Word128# -> Word128# -> (# Word1#, Word128#, Word128# #)
swap128# a# b# = (# f#, a2#, b2# #)
  where
    f# = ge128# a# b#
    mask0# = mask128# f#          -- If a > b all ones
    mask1# = not128# mask0#                        
    a2# = and128# mask0# a# `xor128#` and128# mask1# b#
    b2# = and128# mask1# a# `xor128#` and128# mask0# b#
{-# INLINE swap128# #-}

-- Comparisons
-- Returns 1 if greater than or equal, zero if not
ge128# :: Word128# -> Word128# -> Word1#
ge128# (# x0#, x1# #) (# y0#, y1# #) = c0#
  where
    eq1# = int2Word# (eqWord# x1# y1#)
    gt1# = int2Word# (gtWord# x1# y1#)
    
    ge0# = int2Word# (geWord# x0# y0#)

    c0# = (gt1# `or#` (eq1# `and#` ge0#))
{-# INLINE ge128# #-}

-- Returns 1 if equal
eq128# :: Word128# -> Word128# -> Word1#
eq128# (# x0#, x1# #) (# y0#, y1# #) = c0#
  where
    eq0# = int2Word# (eqWord# x0# y0#)
    eq1# = int2Word# (eqWord# x1# y1#)

    c0# = eq0# `and#` eq1#
{-# INLINE eq128# #-}

-- Bitwise operations
not128# :: Word128# -> Word128#
not128# (# a0#, a1# #) = (# not# a0#, not# a1# #)
{-# INLINE not128# #-}

xor128# :: Word128# -> Word128# -> Word128#
xor128# (# a0#, a1# #) (# b0#, b1# #) = (# xor# a0# b0#, xor# a1# b1# #)
{-# INLINE xor128# #-}

and128# :: Word128# -> Word128# -> Word128#
and128# (# a0#, a1# #) (# b0#, b1# #) = (# and# a0# b0#, and# a1# b1# #)
{-# INLINE and128# #-}

mask128# :: Word1# -> Word128#
mask128# f# = (# m#, m# #)
  where m# = plusWord# (not# f#) (int2Word# 1#)
{-# INLINE mask128# #-}

-- Arithmetic operations
add128Carry# :: Word128# -> Word128# -> (# Word1#, Word128# #)
add128Carry# (# x0#, x1# #) (# y0#, y1# #) = (# c1#, (# z0#, z1# #) #)
  where
    (# c0#, z0# #) = plusWord2# x0# y0#
    (# c1#, z1# #) = add64Three# c0# x1# y1#
{-# INLINE add128Carry# #-}

add128# :: Word128# -> Word128# -> Word128#
add128# x# y# = z#
  where
    (# _, z# #) = add128Carry# x# y#
{-# INLINE add128# #-}

-- No carry
sub128# :: Word128# -> Word128# -> Word128#
sub128# x# y# = add128# x# yNeg#
  where yNeg# = not128# y# `add128#` (extend64To128# (int2Word# 1#))
{-# INLINE sub128# #-}

-- Takes a carry input, useful for multiple additions
add128CarryChain# :: (# Word64#, Word128# #) -> Word128# -> (# Word64#, Word128# #)
add128CarryChain# (# c0#, x0# #) y0# = (# plusWord# c0# c1#, z0# #)
  where
    -- NOTE docs say plusWord2 is the reverse of addWordC
    (# c1#, z0# #) = add128Carry# x0# y0#
{-# INLINE add128CarryChain# #-}

-- Given bit flag, perform conditional negation of 128 bit value. To do this,
-- extend the bit to all 128 bits and then do m ^ x + b where b is the bit in
-- the lowest order position.
condNeg128# :: Word1# -> Word128# -> Word128#
condNeg128# f# x# = xor128# m# x# `add128#` b#
  where
    b# = (# f#, int2Word# 0# #)
    m# = mask128# f#
{-# INLINE condNeg128# #-}

--data Body = Body
--  { x0 :: Word
--  , x1 :: Word
--  , y0 :: Word
--  , y1 :: Word
--  , p0 :: Word
--  , c0 :: Word
--  , p1 :: Word
--  , c1 :: Word
--  , xD :: Word
--  , yD :: Word
--  , c01 :: Word
--  , p01 :: Word
--  , w0 :: Word
--  , w1 :: Word
--  } deriving Show

-- Uses Karatsuba multiplication with 2 64 bit components
-- Appears to be working
mulKara128With128# :: Word128# -> Word128# -> (# Carry128#, Word128# #)
--mul128With128# (# x0#, x1# #) (# y0#, y1# #) = error $ show $ Body x0 x1 y0 y1 p0 c0 p1 c1 xD yD c01 p01 w0 w1
mulKara128With128# (# x0#, x1# #) (# y0#, y1# #) = (# (# z2#, z3# #) , (# z0#, z1# #) #)
  where
    --x0 = W# x0#
    --x1 = W# x1#
    --y0 = W# y0#
    --y1 = W# y1#
    --p0 = W# p0#
    --c0 = W# c0#
    --p1 = W# p1#
    --c1 = W# c1#
    --xD = W# xD#
    --yD = W# yD#
    --c01 = W# c01#
    --p01 = W# p01#
    --w0 = W# w0#
    --w1 = W# w1#

    (# c0#, p0# #) = mul64WithCarry# x0# y0#
    (# c1#, p1# #) = mul64WithCarry# x1# y1#

    -- Swapping avoids carrying and returns sign bit
    (# sx#, xGt#, xLt# #) = swap64# x0# x1#
    (# sy#, yGt#, yLt# #) = swap64# y0# y1#
    p01IsNeg# = sx# `xor#` sy# `xor#` int2Word# 1#

    -- Product of positive differences, followed by mod 2^128 negation
    xD# = minusWord# xGt# xLt#
    yD# = minusWord# yGt# yLt#
    (# c01#, p01# #) = mul64WithCarry# xD# yD#
    p01Signed# = condNeg128# p01IsNeg# (# p01#, c01# #)

    -- Depending on how the additions carry determines the final sign
    (# carry0#, sum0# #) = add128Carry# (# p0#, c0# #) (# p1#, c1# #)
    (# carry1#, (# w0#, w1# #) #) = add128Carry# sum0# p01Signed#

    -- If p01IsNeg# == 0x1 then sign carry bit if carry0# xor carry1#
    -- If p01IsNeg# == 0x0 then sign carry bit if carry0# and carry1#
    mask0# = p01IsNeg#                              -- Works only on first bit
    mask1# = (int2Word# 1#) `minusWord#` mask0#     -- 1 - b
    carry# = ( mask1# `and#` (carry0# `xor#` carry1#) )
             `xor#` ( mask0# `and#` (carry0# `and#` carry1#) )

    -- Perform all the additions. The result is always 256 bits, so the final
    -- carry can be safely discarded
    z0# = p0#
    (# z1C#, z1# #) = c0# `add64Carry#` w0#
    (# z2C#, z2# #) = p1# `add64Carry#` w1#
                          `add64CarryChain#` z1C# 
    (# _, z3# #) = c1# `add64Carry#` z2C#
                       `add64CarryChain#` carry#
{-# INLINE mulKara128With128# #-}

-- Conversions
extend128To256# :: Word128# -> Word256#
extend128To256# (# w0#, w1# #) = (# w0#, w1#, z#, z# #)
  where z# = int2Word# 0#
{-# INLINE extend128To256# #-}

trunc256To128# :: Word256# -> Word128#
trunc256To128# (# w0#, w1#, _, _ #) = (# w0#, w1# #)
{-# INLINE trunc256To128# #-}

extend64To128# :: Word64# -> Word128#
extend64To128# x0# = (# x0#, int2Word# 0# #)
{-# INLINE extend64To128# #-}

--------------------------
-- Modulo 2^256 operations

pack128To256# :: Word128# -> Word128# -> Word256#
pack128To256# (# x0#, x1# #) (# x2#, x3# #) = (# x0#, x1#, x2#, x3# #)
{-# INLINE pack128To256# #-}

unpack256To128# :: Word256# -> (# Word128#, Word128# #)
unpack256To128# (# x0#, x1#, x2#, x3# #) = (# (# x0#, x1# #), (# x2#, x3# #) #)
{-# INLINE unpack256To128# #-}

mask256# :: Word1# -> Word256#
mask256# f# = (# m#, m#, m#, m# #)
  where m# = plusWord# (not# f#) (int2Word# 1#)
{-# INLINE mask256# #-}

condNeg256# :: Word1# -> Word256# -> Word256#
condNeg256# f# x# = xor256# m# x# `add256#` b#
  where
    z# = int2Word# 0#
    b# = (# f#, z#, z#, z# #)
    m# = mask256# f#
{-# INLINE condNeg256# #-}

-- Adds two 256 bit integers and returns carry
add256Carry# :: Word256# -> Word256# -> (# Word1#, Word256# #)
add256Carry# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2#, y3# #) = (# c3#, (# z0#, z1#, z2#, z3# #) #)
  where
    (# c0#, z0# #) = plusWord2# x0# y0#
    (# c1#, z1# #) = add64Three# c0# x1# y1#
    (# c2#, z2# #) = add64Three# c1# x2# y2#
    (# c3#, z3# #) = add64Three# c2# x3# y3#
{-# INLINE add256Carry# #-}

add256# :: Word256# -> Word256# -> Word256#
add256# x# y# = z#
  where (# _, z# #) = add256Carry# x# y#
{-# INLINE add256# #-}

-- Subtracts two 256 bit integer and returns carry
--sub256AndCarry# :: Field -> Field -> (# Word#, Field #)

-- 256 bit karatsuba multiplication
-- NOTE slower than standard multiplication, could try with standard 128 bit
-- mults instead
mulKara256With256# :: Word256# -> Word256# -> (# Carry256#, Word256# #)
mulKara256With256# (# a0#, a1#, a2#, a3# #) (# b0#, b1#, b2#, b3# #) = (# car# , res# #)
  where
    --x0 = W# x0#
    --x1 = W# x1#
    --y0 = W# y0#
    --y1 = W# y1#
    --p0 = W# p0#
    --c0 = W# c0#
    --p1 = W# p1#
    --c1 = W# c1#
    --xD = W# xD#
    --yD = W# yD#
    --c01 = W# c01#
    --p01 = W# p01#
    --w0 = W# w0#
    --w1 = W# w1#

    x0# = (# a0#, a1# #)
    x1# = (# a2#, a3# #)
    y0# = (# b0#, b1# #)
    y1# = (# b2#, b3# #)

    (# c0#, p0# #) = mulKara128With128# x0# y0#
    (# c1#, p1# #) = mulKara128With128# x1# y1#

    -- Swapping avoids carrying and returns sign bit
    (# sx#, xGt#, xLt# #) = swap128# x0# x1#
    (# sy#, yGt#, yLt# #) = swap128# y0# y1#
    p01IsNeg# = sx# `xor#` sy# `xor#` int2Word# 1#

    -- Product of positive differences, followed by mod 2^128 negation
    -- TODO need to implement minus128#
    xD# = sub128# xGt# xLt#
    yD# = sub128# yGt# yLt#
    (# c01#, p01# #) = mulKara128With128# xD# yD#
    p01Signed# = condNeg256# p01IsNeg# (pack128To256# p01# c01#)

    -- Depending on how the additions carry determines the final sign
    (# carry0#, sum0# #) = add256Carry# (pack128To256# p0# c0#) (pack128To256# p1# c1#)
    (# carry1#, w# #) = add256Carry# sum0# p01Signed#
    (# w0#, w1# #) = unpack256To128# w#

    -- If p01IsNeg# == 0x1 then sign carry bit if carry0# xor carry1#
    -- If p01IsNeg# == 0x0 then sign carry bit if carry0# and carry1#
    mask0# = p01IsNeg#                              -- Works only on first bit
    mask1# = (int2Word# 1#) `minusWord#` mask0#     -- 1 - b
    carry# = ( mask1# `and#` (carry0# `xor#` carry1#) )
             `xor#` ( mask0# `and#` (carry0# `and#` carry1#) )

    -- Perform all the additions. The result is always 256 bits, so the final
    -- carry can be safely discarded
    z0# = p0#
    (# z1C#, z1# #) = c0# `add128Carry#` w0#
    (# z2C#, z2# #) = p1# `add128Carry#` w1#
                          `add128CarryChain#` (extend64To128# z1C#) 
    (# _, z3# #) = c1# `add128Carry#` (extend64To128# z2C#)
                       `add128CarryChain#` (extend64To128# carry#)

    -- TODO should reorganize so that 256 is nested pairs rather than a
    -- quadruple so function more ergonomical
    res# = pack128To256# z0# z1#
    car# = pack128To256# z2# z3#
{-# INLINE mulKara256With256# #-}

-- Multiplies two 256 bit integers and returns both the result and carry
-- NOTE this is this faster than karatsuba multiplication
mul256With256# :: Word256# -> Word256# -> (# Carry256#, Word256# #)
mul256With256# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2#, y3# #) = (# (# z4#, z5#, z6#, z7# #), (# z0#, z1#, z2#, z3# #) #)
  where
    ------------- 
    -- First Word
    (# z0C#, z0# #) = mul64WithCarry# x0# y0#
    a0# = z0C#

    --------------
    -- Second Word
    (# w01C#, w01# #) = mul64WithCarry# x0# y1#
    (# w10C#, w10# #) = mul64WithCarry# x1# y0#
   
    (# z1C#, z1# #) = a0# `add64Carry#` w01#
                          `add64CarryChain#` w10#
    
    (# b1#, a1# #) = z1C# `add64Carry#` w01C#
                          `add64CarryChain#` w10C#
                          -- b0# is always zero

    -------------
    -- Third Word
    (# w02C#, w02# #) = mul64WithCarry# x0# y2#
    (# w11C#, w11# #) = mul64WithCarry# x1# y1#
    (# w20C#, w20# #) = mul64WithCarry# x2# y0#

    (# z2C#, z2# #) = a1# `add64Carry#` w02#
                          `add64CarryChain#` w11#
                          `add64CarryChain#` w20#
    
    (# b2#, a2# #) = z2C# `add64Carry#` w02C#
                          `add64CarryChain#` w11C#
                          `add64CarryChain#` w20C#
                          `add64CarryChain#` b1#

    --------------
    -- Fourth word
    (# w03C#, w03# #) = mul64WithCarry# x0# y3#
    (# w12C#, w12# #) = mul64WithCarry# x1# y2#
    (# w21C#, w21# #) = mul64WithCarry# x2# y1#
    (# w30C#, w30# #) = mul64WithCarry# x3# y0#

    (# z3C#, z3# #) = a2# `add64Carry#` w03#
                          `add64CarryChain#` w12#
                          `add64CarryChain#` w21#
                          `add64CarryChain#` w30#

    (# b3#, a3# #) = z3C# `add64Carry#` w03C#
                          `add64CarryChain#` w12C#
                          `add64CarryChain#` w21C#
                          `add64CarryChain#` w30C#
                          `add64CarryChain#` b2#

    -------------
    -- Fifth word
    (# w13C#, w13# #) = mul64WithCarry# x1# y3#
    (# w22C#, w22# #) = mul64WithCarry# x2# y2#
    (# w31C#, w31# #) = mul64WithCarry# x3# y1#

    (# z4C#, z4# #) = a3# `add64Carry#` w13#
                          `add64CarryChain#` w22#
                          `add64CarryChain#` w31#
    
    (# b4#, a4# #) = z4C# `add64Carry#` w13C#
                          `add64CarryChain#` w22C#
                          `add64CarryChain#` w31C#
                          `add64CarryChain#` b3#

    -------------
    -- Sixth Word
    (# w23C#, w23# #) = mul64WithCarry# x2# y3#
    (# w32C#, w32# #) = mul64WithCarry# x3# y2#

    (# z5C#, z5# #) = a4# `add64Carry#` w23#
                          `add64CarryChain#` w32#
    
    (# b5#, a5# #) = z5C# `add64Carry#` w23C#
                          `add64CarryChain#` w32C#
                          `add64CarryChain#` b4#

    ---------------
    -- Seventh Word
    (# w33C#, w33# #) = mul64WithCarry# x3# y3#

    (# z6C#, z6# #) = a5# `add64Carry#` w33#
    
    (# b6#, a6# #) = z6C# `add64Carry#` w33C#
                          `add64CarryChain#` b5#

    --------------
    -- Eighth Word (just carry)
    z7# = a6#
{-# INLINE mul256With256# #-}

-- Takes two 256 bit values and returns their square
-- Avoids extra multiplications. TODO use faster multiplication by 2, currently
-- just does additions
sqr256With256# :: Word256# -> (# Carry256#, Word256# #)
sqr256With256# (# x0#, x1#, x2#, x3# #) = (# (# z4#, z5#, z6#, z7# #), (# z0#, z1#, z2#, z3# #) #)
  where
    -- Hopefully compiler expands
    (# y0#, y1#, y2#, y3# #) = (# x0#, x1#, x2#, x3# #)
    
    ------------- 
    -- First Word
    (# z0C#, z0# #) = mul64WithCarry# x0# y0#
    a0# = z0C#

    --------------
    -- Second Word
    (# w01C#, w01# #) = mul64WithCarry# x0# y1#
    --(# w10C#, w10# #) = mul64WithCarry# x1# y0#
    (# w10C#, w10# #) = (# w01C#, w01# #)
   
    (# z1C#, z1# #) = a0# `add64Carry#` w01#
                          `add64CarryChain#` w10#
    
    (# b1#, a1# #) = z1C# `add64Carry#` w01C#
                          `add64CarryChain#` w10C#
                          -- b0# is always zero

    -------------
    -- Third Word
    (# w02C#, w02# #) = mul64WithCarry# x0# y2#
    (# w11C#, w11# #) = mul64WithCarry# x1# y1#
    --(# w20C#, w20# #) = mul64WithCarry# x2# y0#
    (# w20C#, w20# #) = (# w02C#, w02# #)

    (# z2C#, z2# #) = a1# `add64Carry#` w02#
                          `add64CarryChain#` w11#
                          `add64CarryChain#` w20#
    
    (# b2#, a2# #) = z2C# `add64Carry#` w02C#
                          `add64CarryChain#` w11C#
                          `add64CarryChain#` w20C#
                          `add64CarryChain#` b1#

    --------------
    -- Fourth word
    (# w03C#, w03# #) = mul64WithCarry# x0# y3#
    (# w12C#, w12# #) = mul64WithCarry# x1# y2#
    --(# w21C#, w21# #) = mul64WithCarry# x2# y1#
    (# w21C#, w21# #) = (# w12C#, w12# #)
    --(# w30C#, w30# #) = mul64WithCarry# x3# y0#
    (# w30C#, w30# #) = (# w03C#, w03# #)

    (# z3C#, z3# #) = a2# `add64Carry#` w03#
                          `add64CarryChain#` w12#
                          `add64CarryChain#` w21#
                          `add64CarryChain#` w30#

    (# b3#, a3# #) = z3C# `add64Carry#` w03C#
                          `add64CarryChain#` w12C#
                          `add64CarryChain#` w21C#
                          `add64CarryChain#` w30C#
                          `add64CarryChain#` b2#

    -------------
    -- Fifth word
    (# w13C#, w13# #) = mul64WithCarry# x1# y3#
    (# w22C#, w22# #) = mul64WithCarry# x2# y2#
    --(# w31C#, w31# #) = mul64WithCarry# x3# y1#
    (# w31C#, w31# #) = (# w13C#, w13# #)

    (# z4C#, z4# #) = a3# `add64Carry#` w13#
                          `add64CarryChain#` w22#
                          `add64CarryChain#` w31#
    
    (# b4#, a4# #) = z4C# `add64Carry#` w13C#
                          `add64CarryChain#` w22C#
                          `add64CarryChain#` w31C#
                          `add64CarryChain#` b3#

    -------------
    -- Sixth Word
    (# w23C#, w23# #) = mul64WithCarry# x2# y3#
    --(# w32C#, w32# #) = mul64WithCarry# x3# y2#
    (# w32C#, w32# #) = (# w23C#, w23# #)

    (# z5C#, z5# #) = a4# `add64Carry#` w23#
                          `add64CarryChain#` w32#
    
    (# b5#, a5# #) = z5C# `add64Carry#` w23C#
                          `add64CarryChain#` w32C#
                          `add64CarryChain#` b4#

    ---------------
    -- Seventh Word
    (# w33C#, w33# #) = mul64WithCarry# x3# y3#

    (# z6C#, z6# #) = a5# `add64Carry#` w33#
    
    (# b6#, a6# #) = z6C# `add64Carry#` w33C#
                          `add64CarryChain#` b5#

    --------------
    -- Eighth Word (just carry)
    z7# = a6#
{-# INLINE sqr256With256# #-}

-- Takes a 256 bit input and a 129 bit input and multiplies to produce a 256 bit
-- result and 129 bits of carry. Useful for multiplying r = 2^256 - p.
--
-- NOTE ignores the upper bits of y2#
mul256With129# :: Word256# -> Word129# -> (# Carry129#, Word256# #)
mul256With129# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2# #) = (# (# z4#, z5#, z6# #), (# z0#, z1#, z2#, z3# #) #)
  where
    -- One bit multiply
    y2Mask# = int2Word# 1# `plusWord#` not# (int2Word# 1# `and#` y2#)
    
    ------------- 
    -- First Word
    (# z0C#, z0# #) = mul64WithCarry# x0# y0#
    a0# = z0C#

    --------------
    -- Second Word
    (# w01C#, w01# #) = mul64WithCarry# x0# y1#
    (# w10C#, w10# #) = mul64WithCarry# x1# y0#
   
    (# z1C#, z1# #) = a0# `add64Carry#` w01#
                          `add64CarryChain#` w10#
    
    (# b1#, a1# #) = z1C# `add64Carry#` w01C#
                          `add64CarryChain#` w10C#

    -------------
    -- Third Word
    w02# = x0# `and#` y2Mask#
    (# w11C#, w11# #) = mul64WithCarry# x1# y1#
    (# w20C#, w20# #) = mul64WithCarry# x2# y0#

    (# z2C#, z2# #) = a1# `add64Carry#` w02#
                          `add64CarryChain#` w11#
                          `add64CarryChain#` w20#
    
    (# b2#, a2# #) = z2C# `add64Carry#` w11C#
                          `add64CarryChain#` w20C#
                          `add64CarryChain#` b1#

    --------------
    -- Fourth word
    w12# = x1# `and#` y2Mask#
    (# w21C#, w21# #) = mul64WithCarry# x2# y1#
    (# w30C#, w30# #) = mul64WithCarry# x3# y0#

    (# z3C#, z3# #) = a2# `add64Carry#` w12#
                          `add64CarryChain#` w21#
                          `add64CarryChain#` w30#

    (# b3#, a3# #) = z3C# `add64Carry#` w21C#
                          `add64CarryChain#` w30C#
                          `add64CarryChain#` b2#

    -------------
    -- Fifth word
    w22# = x2# `and#` y2Mask#
    (# w31C#, w31# #) = mul64WithCarry# x3# y1#

    (# z4C#, z4# #) = a3# `add64Carry#` w22#
                          `add64CarryChain#` w31#
    
    (# b4#, a4# #) = z4C# `add64Carry#` w31C#
                          `add64CarryChain#` b3#

    -------------
    -- Sixth Word
    w32# = x3# `and#` y2Mask#

    (# z5C#, z5# #) = a4# `add64Carry#` w32#
    
    (# b5#, a5# #) = z5C# `add64Carry#` b4#

    ---------------
    -- Seventh Word
    z6# = a5#
{-# INLINE mul256With129# #-}

-- Takes two 129 bit values and multiplies to produce one 256 bit value and two
-- bits of carry. Used on the output of the previous function.
--
-- NOTE ignores the upper bits of both inputs
mul129With129# :: Word129# -> Word129# -> (# Carry2#, Word256# #)
mul129With129# (# x0#, x1#, x2# #) (# y0#, y1#, y2# #) = (# z4#, (# z0#, z1#, z2#, z3# #) #)
  where
    zeroWord# = int2Word# 0#
    x2Mask# = int2Word# 1# `plusWord#` not# (int2Word# 1# `and#` x2#)
    y2Mask# = int2Word# 1# `plusWord#` not# (int2Word# 1# `and#` y2#)

    ------------- 
    -- First Word
    (# z0C#, z0# #) = mul64WithCarry# x0# y0#
    a0# = z0C#

    --------------
    -- Second Word
    (# w01C#, w01# #) = mul64WithCarry# x0# y1#
    (# w10C#, w10# #) = mul64WithCarry# x1# y0#
   
    (# z1C#, z1# #) = a0# `add64Carry#` w01#
                          `add64CarryChain#` w10#
    
    (# b1#, a1# #) = z1C# `add64Carry#` w01C#
                          `add64CarryChain#` w10C#
                          -- b0# is always zero

    -------------
    -- Third Word
    w02# = x0# `and#` y2Mask#
    (# w11C#, w11# #) = mul64WithCarry# x1# y1#
    w20# = x2Mask# `and#` y0#

    (# z2C#, z2# #) = a1# `add64Carry#` w02#
                          `add64CarryChain#` w11#
                          `add64CarryChain#` w20#
    
    (# b2#, a2# #) = z2C# `add64Carry#` w11C#
                          `add64CarryChain#` b1#

    --------------
    -- Fourth word
    w12# = x1# `and#` y2Mask#
    w21# = x2Mask# `and#` y1#

    (# z3C#, z3# #) = a2# `add64Carry#` w12#
                          `add64CarryChain#` w21#

    (# b3#, a3# #) = z3C# `add64Carry#` b2#

    -------------
    -- Fifth word
    -- One bit multiplication
    w22# = x2# `and#` y2#
    
    -- NOTE, cannot carry by assumption
    (# _, z4# #) = a3# `add64Carry#` w22#
{-# INLINE mul129With129# #-}

-- Multiplies a two bit value with a 129 bit value
--
-- TODO, is this actually preferable to using a multiply function?
mul2With129# :: Word2# -> Word129# -> Word256#
mul2With129# b# (# x0#, x1#, x2# #) = w
  where
    bit0Mask# = int2Word# 1# `plusWord#` not# (int2Word# 1# `and#` b#)
    bit1Mask# = int2Word# 1# `plusWord#` not# (int2Word# 1# `and#` (b# `uncheckedShiftRL#` 1#))

    -- Double x by shifting up
    xDbl0# = x0# `uncheckedShiftL#` 1#
    xDbl1# = (x1# `uncheckedShiftL#` 1#) `xor#` (x0# `uncheckedShiftRL#` 63#)
    xDbl2# = (x2# `uncheckedShiftL#` 1#) `xor#` (x1# `uncheckedShiftRL#` 63#)

    y0# = bit0Mask# `and#` x0#
    y1# = bit0Mask# `and#` x1#
    y2# = bit0Mask# `and#` x2#
    y3# = int2Word# 0#

    z0# = bit1Mask# `and#` xDbl0#
    z1# = bit1Mask# `and#` xDbl1#
    z2# = bit1Mask# `and#` xDbl2#
    z3# = int2Word# 0#

    (# _, w #) = add256Carry# (# y0#, y1#, y2#, y3# #) (# z0#, z1#, z2#, z3# #)
{-# INLINE mul2With129# #-}

-- Returns 1 if greater than or equal, zero if not
ge256# :: Word256# -> Word256# -> Word1#
ge256# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2#, y3# #) = c0#
  where
    eq3# = int2Word# (eqWord# x3# y3#)
    eq2# = int2Word# (eqWord# x2# y2#)
    eq1# = int2Word# (eqWord# x1# y1#)
    
    gt3# = int2Word# (gtWord# x3# y3#)
    gt2# = int2Word# (gtWord# x2# y2#)
    gt1# = int2Word# (gtWord# x1# y1#)
    
    ge0# = int2Word# (geWord# x0# y0#)

    c0# = gt3# `or#` (eq3# `and#` (gt2# `or#` (eq2# `and#` (gt1# `or#` (eq1# `and#` ge0#)))))
{-# INLINE ge256# #-}

-- Returns 1 if equal
eq256# :: Word256# -> Word256# -> Word1#
eq256# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2#, y3# #) = c0#
  where
    eq0# = int2Word# (eqWord# x0# y0#)
    eq1# = int2Word# (eqWord# x1# y1#)
    eq2# = int2Word# (eqWord# x2# y2#)
    eq3# = int2Word# (eqWord# x3# y3#)

    c0# = eq0# `and#` eq1# `and#` eq2# `and#` eq3#
{-# INLINE eq256# #-}

-- bitwise negation of 256 bit word
not256# :: Word256# -> Word256#
not256# (# x0#, x1#, x2#, x3# #) = (# not# x0#, not# x1#, not# x2#, not# x3# #)
{-# INLINE not256# #-}

xor256# :: Word256# -> Word256# -> Word256#
xor256# (# x0#, x1#, x2#, x3# #) (# y0#, y1#, y2#, y3# #) = (# z0#, z1#, z2#, z3# #)
  where
    z0# = x0# `xor#` y0#
    z1# = x1# `xor#` y1#
    z2# = x2# `xor#` y2#
    z3# = x3# `xor#` y3#

------------------------
-- Modular Operations --

-- These operations also word on unboxed vectors with the p, 2^256 - p, p+1 etc.
-- passed as arguments to the function. Meant to be instantiated to a particular
-- prime inside a wrapper

type Prime# = Word256#
type PrimeOffset# = Word129#
type PrimeInc# = Word256#

type Field# = Word256#

-- After performing an addition of two reduced residues, there are three
-- possibilities, that a + b < p, p <= a + b < 2^256, 2^256 <= a+b < 2p. In the
-- first case, c = a + b is a reduced residue. Using the fact that p = 2^256 -
-- r, in the second case we can drop carry and add r, which is the same as
-- subtracting p. In the second case, we can first add r and then drop the
-- carry.
addField# :: Prime# -> PrimeOffset# -> Field# -> Field# -> Field#
addField# p (# r0#, r1#, r2# #) x y = b
  where
    --(# r0#, r1#, r2# #) = r ()
    (# c0#, z@(# z0#, z1#, z2#, z3# #) #) = add256Carry# x y
    c1# = ge256# z p
    mask# = int2Word# 1# `plusWord#` not# (c0# `or#` c1#)

    w0# = mask# `and#` r0#
    w1# = mask# `and#` r1#
    w2# = mask# `and#` r2#
    w3# = int2Word# 0#
    -- w3# = mask# `and#` r3#

    (# _, b #) = add256Carry# (# w0#, w1#, w2#, w3# #) z
{-# INLINE addField# #-}

-- Since the contents are less than p, cannot underflow
negField# :: Prime# -> PrimeOffset# -> PrimeInc# -> Field# -> Field#
negField# p# r# pInc# a = (# b0# `and#` eqMask#, b1# `and#` eqMask#, b2# `and#` eqMask#, b3# `and#` eqMask# #)
  where
    (# _, b#@(# b0#, b1#, b2#, b3# #) #) = add256Carry# pInc# (not256# a)
    eqMask# = (eq256# b# p#) `minusWord#` int2Word# 0x1#
{-# INLINE negField# #-}

-- Subtraction works by taking a - b = a + (p - b).
subField# :: Prime# -> PrimeOffset# -> PrimeInc# -> Field# -> Field# -> Field#
subField# p# r# pInc# a# b# = addField# p# r# a# (negField# p# r# pInc# b#)
{-# INLINE subField# #-}

-- Instead of reducing mod p explicitly, we perform several multiplication by r.
-- This has the effect of reducing the carry by 127 bits for each r
-- multiplication, which allows transforming a finite field multiplication into
-- three 256 bit multiplications. TODO can use shorter multiplications.
mulField# :: Prime# -> PrimeOffset# -> Field# -> Field# -> Field#
mulField# p# r# x# y# = w# -- trace (show $ map pfti out) w
  where
    --pfti (x, y) = (fieldToInteger x, fieldToInteger y)
    --out = [(F# c0#, F# z0#) ]-- (c1, F# z1), (c2, F# z2)]
    -- r# = uncheckedTruncate256to129# (unF# r)
    (# c0#, z0# #) = mul256With256# x# y#
    (# c1#, z1# #) = mul256With129# c0# r#
    (# c2#, z2# #) = mul129With129# c1# r#
    z3# = mul2With129# c2# r#
    
    add' = addField# p# r#
    w# = z0# `add'` z1# `add'` z2# `add'` z3#
{-# INLINE mulField# #-}

-- Works using the same technique as mulField, but performs a square for the
-- initial multiplication. 
sqrField# :: Prime# -> PrimeOffset# -> Field# -> Field#
sqrField# p# r# x# = w# -- trace (show $ map pfti out) w
  where
    --pfti (x, y) = (fieldToInteger x, fieldToInteger y)
    --out = [(F# c0#, F# z0#) ]-- (c1, F# z1), (c2, F# z2)]
    -- r# = uncheckedTruncate256to129# (unF# r)
    (# c0#, z0# #) = sqr256With256# x#
    (# c1#, z1# #) = mul256With129# c0# r#
    (# c2#, z2# #) = mul129With129# c1# r#
    z3# = mul2With129# c2# r#
    
    add' = addField# p# r#
    w# = z0# `add'` z1# `add'` z2# `add'` z3#
{-# INLINE sqrField# #-}

-- This functions is (relatively speaking) very rarely ever called, and when it
-- is modular inversion can be batched, so the performance of this function
-- matters less than addition and multiplication generally. As such, just revert
-- to the BigNum modular inverse algorithm. Returns 0 on 0
--
-- TODO not clear that the big nat is always sufficiently large
invField# :: BigNat -> Field# -> Field#
invField# pBigNat x = truncateBigNatToField# (flip recipModBigNat pBigNat (fieldToBigNat# x))
{-# INLINE invField# #-}

-- Compute inverse and multiply
divField# :: Prime# -> PrimeOffset# -> BigNat -> Field# -> Field# -> Field#
divField# p# r# pBigNat a# b# = mulField# p# r# a# (invField# pBigNat b#)
{-# INLINE divField# #-}

-- TODO should use mod p-1
powFieldInteger# :: Prime# -> PrimeOffset# -> BigNat -> Field# -> Integer -> Field#
powFieldInteger# p# r# pBigNat b# (Jp# n#) = powFieldBigNat# p# r# b# n#
powFieldInteger# p# r# pBigNat b# (Jn# n#) = powFieldBigNat# p# r# (invField# pBigNat b#) n#
powFieldInteger# p# r# pBigNat b# (S# n#) = a#
  where
    -- TODO not clear that inversion is efficient
    (# b'#, n'# #) = if isTrue# (n# <# 0#) then (# invField# pBigNat b#, negateInt# n# #) else (# b#, n# #)
    (# _, a# #) = powFieldWord# p# r# (# b'#, wordToField# (int2Word# 1#) #) (int2Word# n'#)
{-# INLINE powFieldInteger# #-}

-- Compute power using double-and-add on a BigNat
-- TODO could use mod (p-1)
powFieldBigNat# :: Prime# -> PrimeOffset# -> Field# -> BigNat -> Field#
powFieldBigNat# p# r# b# n = rec 0# (# b#, wordToField# (int2Word# 1#) #)
  where
    sz# = sizeofBigNat# n
    rec i# (# _, a# #) | isTrue# (i# ==# sz#) = a#
    rec i# x# = rec (i# +# 1#) (powFieldWord# p# r# x# (indexBigNat# n i#))
{-# INLINE powFieldBigNat# #-}

-- Given the (base, accumulated) and the n, compute base^n * accumulated
-- recursively. Need to perform at least 64 doublings independent of the value
-- of the exponent to saturate the length of the word
powFieldWord# :: Prime# -> PrimeOffset# -> (# Field#, Field# #) -> Word64# -> (# Field#, Field# #)
powFieldWord# p# r# x w# = rec x w# 64#
  where
    rec x# n# k# | isTrue# (k# ==# 0#) = x#
    rec (# c#, a#@(# a0#, a1#, a2#, a3# #) #) n# k# = rec (# d#, (# f0#, f1#, f2#, f3# #) #) (uncheckedShiftRL# n# 1#) (k# -# 1#)
      where
        -- One's if bit is set zero's if not set
        nMask# = int2Word# (negateInt# (1# `andI#` word2Int# n#))

        -- Compute doubling (TODO could save instructions)
        d# = mulField# p# r# c# c#

        -- Compute the multiplication
        (# e0#, e1#, e2#, e3# #) = mulField# p# r# c# a#

        -- Select either the multiplied value or the original value based on the
        -- bit of exponent
        f0# = (nMask# `and#` e0#) `xor#` (not# nMask# `and#` a0#)
        f1# = (nMask# `and#` e1#) `xor#` (not# nMask# `and#` a1#)
        f2# = (nMask# `and#` e2#) `xor#` (not# nMask# `and#` a2#)
        f3# = (nMask# `and#` e3#) `xor#` (not# nMask# `and#` a3#)
{-# INLINE powFieldWord# #-}

-- Takes a field element as input and returns two field elements as output of
-- approximately half the size (up to sign) such that x = y + z W where W is the
-- smaller primitive third root of unity. Costs approximately 6 129 bit
-- multiplications and can reduce EC scalar multiplication time by over fifty
-- percent.
--
-- This works by finding a vector [y, z] near [x,0] in the lattice L = { (x,y) :
-- x + y W = 0 mod p }. A short basis for this lattice is independent of x and
-- is computed ahead of time. If M is the matrix with columns encoding such a
-- short basis, to compute [a,b] = M floor(M^-1 [k,0]).
--
-- det(M) = p, so multiplying M^-1 [x,0] = 1/p [y', z']. Note that the exact
-- minimal solution is not necessary to acheive the vast majority of the length
-- reduction, so 1/p = 1/2^256 + 1/2^384 + O(1/2^386) can be approximated by
-- 1/2^256. Then [y'', z''] = M [y', z'] can be computed exactly using four 129
-- bit multiplies. The final vector is [y, z] = [x,0] - [y'', z''].
-- splitField :: Field# -> (Field#, Field#)
-- splitField x = {- trace (show $ map fieldToInteger [a0C, b0C, m00', m01', m10', m11']) -} (a1, b1)
--   where 
--     r# = uncheckedTruncate256to129# (unF# r)
--     matdd# = uncheckedTruncate256to129# (unF# unity3Matdd)
--     mat01# = uncheckedTruncate256to129# (unF# unity3Mat01)
--     mat10# = uncheckedTruncate256to129# (unF# unity3Mat10)
-- 
--     -- Approximate 1/p by 1/2^256
--     (# a0C#, _ #) = mul256With129# (unF# x) matdd#
--     (# b0C#, _ #) = mul256With129# (unF# x) mat10#     -- NOTE this is the negation of the actual component
-- 
--     -- Matrix multiply the vector
--     -- positive
--     (# m00C#, m00# #) = mul129With129# a0C# matdd#
--     m00' = (F# m00#) `addField` (F# (mul2With129# m00C# r#))
-- 
--     -- positive
--     (# m01C#, m01# #) = mul129With129# b0C# mat01#
--     m01' = (F# m01#) `addField` (F# (mul2With129# m01C# r#))
--     
--     -- negative
--     (# m10C#, m10# #) = mul129With129# a0C# mat10#
--     m10' = (F# m10#) `addField` (F# (mul2With129# m10C# r#))
--     
--     -- positive
--     (# m11C#, m11# #) = mul129With129# b0C# matdd#
--     m11' = (F# m11#) `addField` (F# (mul2With129# m11C# r#))
-- 
--     a1 = x `subField` (m01' `addField` m00')
--     b1 = m10' `subField` m11'

-- Convert 64bit integer to field
intToField# :: Prime# -> Int# -> Field#
intToField# (# p0#, p1#, p2#, p3# #) i# = (# x0#, x1#, x2#, x3# #)
  where
    -- Since the integer only has 127 bits plus one sign bit, the negative case
    -- cannot underflow as the 127th bit of both SECP256k1 primes is set. In the
    -- negative case, we can add as a word and ignore the carry.
    -- 
    -- NOTE this is not necessarily true of all prime of the form 2^256 - r for
    -- r^2 < 2 p.
    --(# p0#, p1#, p2#, p3# #) = unF# p
    isNegMask# = int2Word# (negateInt# (i# <# 0#))
    w0# = int2Word# i#
    w1# = p0# `plusWord#` w0#

    x0# = (w1# `and#` isNegMask#) `xor#` (w0# `and#` not# isNegMask#)
    x1# = (p1# `and#` isNegMask#)
    x2# = (p2# `and#` isNegMask#)
    x3# = (p3# `and#` isNegMask#)
{-# INLINE intToField# #-}

wordToField# :: Word# -> Field#
wordToField# w# = (# w#, z#, z#, z# #)
  where z# = int2Word# 0#
{-# INLINE wordToField# #-}

fieldToBigNat# :: Field# -> BigNat
fieldToBigNat# (# x0#, x1#, x2#, x3# #) = b0 `xorBigNat` (shiftLBigNat b1 128#)
  where
    b0  = wordToBigNat2 x1# x0#
    b1  = wordToBigNat2 x3# x2#
{-# INLINE fieldToBigNat# #-}

-- Given a big nat of length four, reads the first four bytes into a tuple
--
-- NOTE lots of weird bugs if called on insufficiently big BigNats. Be careful.
uncheckedBigNatToField# :: BigNat -> Field#
uncheckedBigNatToField# x = (# y0#, y1#, y2#, y3# #)
  where
    y0# = indexBigNat# x 0#
    y1# = indexBigNat# x 1#
    y2# = indexBigNat# x 2#
    y3# = indexBigNat# x 3#
{-# INLINE uncheckedBigNatToField# #-}

-- For computing the offset
uncheckedBigNatToTrunc# :: BigNat -> PrimeOffset#
uncheckedBigNatToTrunc# x = (# y0#, y1#, y2# #)
  where
    y0# = indexBigNat# x 0#
    y1# = indexBigNat# x 1#
    y2# = indexBigNat# x 2#
{-# INLINE uncheckedBigNatToTrunc# #-}

-- Checks that the length is sufficient and pads with zeros. Does not perform a
-- modulo operations
truncateBigNatToField# :: BigNat -> Field#
truncateBigNatToField# bn = uncheckedBigNatToField# (plusBigNat bn (bitBigNat 256#))
{-# INLINE truncateBigNatToField# #-}

fieldToInteger# :: Field# -> Integer
fieldToInteger# x = bigNatToInteger (fieldToBigNat# x)
{-# INLINE fieldToInteger# #-}

truncToInteger# :: Word129# -> Integer
truncToInteger# (# x0#, x1#, x2# #) = bigNatToInteger (fieldToBigNat# (# x0#, x1#, x2#, int2Word# 0# #))
{-# INLINE truncToInteger# #-}

fieldToNatural# :: Field# -> Natural
fieldToNatural# x = NatJ# (fieldToBigNat# x)
{-# INLINE fieldToNatural# #-}

-- TODO typically called on values already reduced, so avoid BigNat calls?
integerToField# :: Prime# -> PrimeOffset# -> PrimeInc# -> BigNat -> Integer -> Field#
integerToField# p# r# pInc# pBigNat (S#  nInt#) = intToField# p# nInt#
integerToField# p# r# pInc# pBigNat (Jn# nBig) = negField# p# r# pInc# (integerToField# p# r# pInc# pBigNat (Jp# nBig))
integerToField# p# r# pInc# pBigNat (Jp# nBig) = truncateBigNatToField# $ remBigNat nBig pBigNat
{-# INLINE integerToField# #-}


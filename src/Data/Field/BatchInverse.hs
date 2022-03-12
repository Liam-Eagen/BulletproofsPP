{-# LANGUAGE BangPatterns #-}
 
module Data.Field.BatchInverse where

import qualified Data.Vector as V

--import Control.Monad
--import Control.Monad.ST
--import Data.STRef

-- Uses montgomery batch inversion to invert a list of number using three
-- multiplications per number and one reciprocal for the whole list. Maps the
-- inverse of zero to zero.
batchInverse :: (Fractional a, Eq a) => [a] -> [a]
batchInverse vs = rec0 1 vs []
  where
    rec0 !n [] ss = rec1 (1/n) ss []
    rec0 !n (0:xs) ss = rec0 n xs $ (0, n) : ss
    rec0 !n (x:xs) ss = rec0 (x*n) xs $ (x,n) : ss

    -- TODO remove m 
    rec1 _ [] ys = ys
    rec1 (!y) ((0, n):ss) ys = rec1 (y) ss $ 0 : ys
    rec1 (!y) ((x, n):ss) ys = rec1 (x * y) ss $ y * n : ys

-- Implemented over vectors rather than lists
batchInverseV :: (Fractional a, Eq a) => V.Vector a -> V.Vector a
batchInverseV vs = vs''
  where
    l = V.length vs

    -- Not sure if there is a faster way, use an unfold for now
    --vs' = V.unfoldrExactN l go1 (0, 1)
    vs' = V.unfoldr go1 (0, 1)
    --go1 (ind, n) = ((x, n), (ind + 1, n'))
    go1 (ind, n) = if ind < l then Just ((x, n), (ind + 1, n')) else Nothing
      where
        x = vs V.! ind
        n' = if x == 0 then n else n * x

    -- This uses Monad.ST to modify the input in place

    -- Second pass goes in reverse order
    -- TODO why is
    nInv = recip $ snd $ vs' V.! (l-1)
    --vs'' = V.unfoldrExactN l go2 (0, nInv)
    vs'' = V.unfoldr go2 (0, nInv)
    go2 (ind, y) = if ind < l then Just (x', (ind+1, y')) else Nothing
      where
        (x, n) = vs' V.! (l - ind - 1)
        (x', y') = if x == 0 then (0, y) else (y * n, x * y)

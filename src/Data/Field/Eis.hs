module Data.Field.Eis where

import Data.List (minimumBy)
import Data.Field.Galois
import qualified Data.Field.Galois as G -- .Prime

import Data.Curve
import Data.Curve.Weierstrass

-- TODO import?
data Pxy a = Pxy

pxy :: a -> Pxy a
pxy _ = Pxy

-- Eisurrently only implemented for w^3 = 1
data Eis a = Eis a a
  deriving (Eq, Show, Ord, Functor)

conjEis :: Num a => Eis a -> Eis a
conjEis (Eis x y) = Eis (x - y) (negate y)

normEis :: Num a => Eis a -> a
normEis (Eis x y) = x^2 - x * y + y^2

instance Num a => Num (Eis a) where
  (Eis a0 b0) + (Eis a1 b1) = Eis (a0 + a1) (b0 + b1)
  (Eis a0 b0) - (Eis a1 b1) = Eis (a0 - a1) (b0 - b1)
  --(Eis a0 b0) * (Eis a1 b1) = Eis (a0 * a1 - b0 * b1) (a0 * b1 + a1 * b0 - b0 * b1) 
  (Eis a0 b0) * (Eis a1 b1) = Eis (a' - b') (a' - c')
    where
      a' = a0 * a1
      b' = b0 * b1
      c' = (a0 - b0) * (a1 - b1)

  negate (Eis a0 b0) = Eis (negate a0) (negate b0)
  fromInteger n = Eis (fromInteger n) 0

  abs = error "Can't abs Eis"
  signum = error "Can't signum Eis"

-- Primes p = 3 n + 1 have a third root of unity. The class canonicalizes one
-- primitive root of unity. This is used to perform GLV style decomposition as
-- well as more complex rational reconstruction
class PrimeField a => HasEis a where
  -- Canonical root of unity, unity3^3 = 1
  unity3 :: a

  -- Factorization of characteristic given the canonical root of unity
  charEis :: a -> Eis Integer

  -- Decompose a = u + v*unity3 where
  -- |toInteger u|^2, |toInteger v|^2 < 2 p
  --
  -- TODO this doesn't handle sign, must detect independently
  --decomposeEis :: a -> Eis a
  decomposeEis :: a -> Eis Integer

  recomposeEis :: Eis a -> a
  recomposeEis (Eis x y) = x + unity3 * y

instance (Integral a) => Real (Eis a) where
  --toRational = toRational . recomposeEis
  toRational = error "Can't convert Eis to rational"

instance (Enum a) => Enum (Eis a) where
  --toEnum n = Eis (toEnum n) 0
  toEnum = error "Can't enumerate Eis"
  --fromEnum = fromEnum . recomposeEis
  fromEnum = error "Can't enumerate Eis"

instance (Integral a) => Integral (Eis a) where
  -- This needs to choose the "smallest" remainder which means we need to round
  -- our divisions to the nearest integer
  quotRem x m = (q, x - m * q)
    where
      Eis a b = toInteger <$> x
      mN = toInteger $ normEis m
      Eis u v = toInteger <$> x * conjEis m
      q = fromInteger <$> Eis (u `round` mN) (v `round` mN)
      round n m = if m - abs r < abs r then q + signum r else q
        where (q, r) = n `divMod` m

  toInteger = error "Can't convert Eis to integer, use recomposeEis instead"

-- TODO implement halfGCD directly
egcd :: (Integral a, Show a) => (Eis a, Eis a) -> (Eis a, Eis a) -> [(Eis a, Eis a)]
egcd (r, s) (r', s') = (r, s) : egcd (r', s') (r'', s'')
  where
    q = r `quot` r'
    r'' = r - q * r'
    s'' = s - q * s'

-- Eis Rational Reconstruction finds a = (a0 + unity3 * a1) / (a2 + unity3 * a4) mod p
-- such that |ai| ~ p^(1/4)
reconstructEisRatio :: (HasEis a, Integral a) => a -> (Eis Integer, Eis Integer)
reconstructEisRatio x = head $ dropWhile cond $ egcd (pEis, 0) (y, 1)
  where 
    p = toInteger $ G.char x
    cond (r,s) = (normEis r)^2 > 2 * p
    y = decomposeEis x
    pEis = conjEis $ charEis x


{-# LANGUAGE BangPatterns, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, ConstrainedClassMethods #-}
{-# LANGUAGE RankNTypes, DeriveFunctor, DeriveFoldable #-}

-- Generic Code for (Pedersen) Commitments. Could probably be more generic, but
-- this is adequate for now. Convenient for Bulletproofs since it allows us to
-- manipulate witnesses in a somewhat more abstract manner. Also should handle
-- e.g. vector commitments efficiently using Shamir's trick

module Commitment where

import Data.Functor
import Data.Functor.Identity
import Data.Foldable
import Data.Bifunctor               -- TODO Commitment should be Bifunctor

import Control.Monad.Trans
import Control.Monad.RWS.Strict

import Data.Field.Galois hiding ((*^))
import Data.Curve
import qualified Data.Curve as Curve

import Data.VectorSpace

import Utils

--------------------------------------------------------
-- Commitments defined over any suitable vector space --

type CanCommit v s = (Eq v, Integral s, Fractional s, FastDouble v, VectorSpace v, s ~ Scalar v)

-- Represents an opened commitment, from which we can derive the actual
-- commitment. TODO rename to something else: Opening, Shamir, Commitable, etc.?
class Bifunctor c => Commitment c where
  -- Commit using shamir's trick
  commit :: CanCommit v s => c v s -> v
  commit c = shamirWith (commitWith c) zeroV

  -- Used to implement horizontal commitments
  -- Accepts a parametric multiplication, addition, and zero. This is so that we
  -- can call e.g. as commitWith (,) (:) [] to obtain the list of scalars and
  -- group elements
  commitWith :: CanCommit v s => c v s -> (s -> v -> a) -> (a -> b -> b) -> b -> b

type Committer v s = forall a b. (s -> v -> a) -> (a -> b -> b) -> b -> b

sumWith :: Foldable f => (a -> b -> b) -> f a -> b -> b
sumWith = flip . foldr

dotWith :: (Foldable f, Zip f) => (s -> v -> a) -> (a -> b -> b) -> f s -> f v -> b -> b
dotWith (*:) (+:) xs ys = sumWith (+:) $ zipWith' (*:) xs ys

-- Basic commitment is a pair of scalar and vector
data CommitPoint v s = CP { scalarCP :: s, basisCP :: v }
  deriving (Eq, Show, Functor, Foldable)

instance Bifunctor CommitPoint where
  bimap f g (CP s b) = CP (g s) (f b)

mapScalarCP :: CommitPoint v s -> (s -> t) -> CommitPoint v t
mapScalarCP = flip second 

instance Commitment CommitPoint where
  commit (CP s g) = s *^ g
  commitWith (CP s g) (*:) (+:) !z = (s *: g) +: z

--instance Monoid m => Zip (CommitPoint m) where
--  liftZip x = CP x mempty
--  zipWith' f (CP x a) (CP y b) = CP (f x y) (a <> b)
--  zipWithDef' f _ = zipWith' f

-- Pedersen scalar commitments have blinding
data PedersenScalar v s = PS { blindingPS :: CommitPoint v s, scalarPS :: CommitPoint v s }
  deriving (Eq, Show, Functor)

makePS :: CanCommit v s => s -> v -> s -> v -> PedersenScalar v s
makePS bl blG sc scG = PS (CP bl blG) (CP sc scG)

instance Bifunctor PedersenScalar where
  bimap f g (PS bl sc) = PS (bimap f g bl) (bimap f g sc)

instance Commitment PedersenScalar where
  commit (PS (CP bs bg) (CP ss sg)) = shamir bg bs sg ss
  commitWith (PS b s) (*:) (+:) !z = let cw x z = commitWith x (*:) (+:) z in cw s $ cw b z

data PedersenScalarPair v s = PSP { blindingPSP :: CommitPoint v s, pairPSP :: (CommitPoint v s, CommitPoint v s) }
  deriving (Eq, Show, Functor)

makePSP :: CanCommit v s => s -> v -> s -> v -> s -> v -> PedersenScalarPair v s
makePSP bl blG sc0 scG0 sc1 scG1 = PSP (CP bl blG) (CP sc0 scG0, CP sc1 scG1)

instance Bifunctor PedersenScalarPair where
  bimap f g (PSP bl sc) = PSP (bimap f g bl) (dup (bimap f g) sc)

instance Commitment PedersenScalarPair where
  --commit (PS (CP bs bg) (CP ss sg)) = shamir bg bs sg ss
  commitWith (PSP b (s0, s1)) (*:) (+:) !z = let cw x z = commitWith x (*:) (+:) z in cw s1 $ cw s0 $ cw b z

--instance Monoid m => Zip (PedersenScalar m) where
--  liftZip x = PS (liftZip x) (liftZip x)
--  zipWith' f (PS bl0 sc0) (PS bl1 sc1) = PS (zipWith' f bl0 bl1) (zipWith' f sc0 sc1)
--  zipWithDef' f _ = zipWith' f

-- Pedersen Vector Commitments work over any kind of zippable functor
data PedersenScalarVector f v s = PSV { blindingPSV :: CommitPoint v s, scalarPSV :: CommitPoint v s, vectorPSV :: f v s }
  deriving (Eq, Show, Functor)

makePSV :: CanCommit v s => s -> v -> s -> v -> f v s -> PedersenScalarVector f v s
makePSV bl blG sc scG = PSV (CP bl blG) (CP sc scG)

updatePSV :: PedersenScalarVector f v s -> t -> t -> f v t -> PedersenScalarVector f v t
updatePSV (PSV b s _) b' s' c' = PSV (mapScalarCP b $ const b') (mapScalarCP s $ const s') c'

instance Bifunctor f => Bifunctor (PedersenScalarVector f) where
  bimap f g (PSV bl sc xs) = PSV (bimap f g bl) (bimap f g sc) (bimap f g xs)

instance Commitment f => Commitment (PedersenScalarVector f) where
  commitWith (PSV b s v) (*:) (+:) !z = commitWith v (*:) (+:) $ cw s $ cw b z
    where cw x = commitWith x (*:) (+:)
  
--instance (Monoid m, Zip (f m)) => Zip (PedersenScalarVector f m) where
--  liftZip x = PSV (liftZip x) (liftZip x) (liftZip x)
--  zipWith' f (PSV bl0 sc0 xs0) (PSV bl1 sc1 xs1) = PSV (zipWith' f bl0 bl1) (zipWith' f sc0 sc1) (zipWith' f xs0 xs1)
--  zipWithDef' f z (PSV bl0 sc0 xs0) (PSV bl1 sc1 xs1) = PSV (zipWith' f bl0 bl1) (zipWith' f sc0 sc1) (zipWithDef' f z xs0 xs1)

---------------------------
-- Zero Knoweldge Proofs --

class ZKP c where
  -- NOTE Setup may not be used in the same way as is typical in papers. I have
  -- defacto used Setup to store any common public information necessary for
  -- both proving and verifying.

  type Setup c v s       -- Stores public information independent of particular proof
  type Witness c v s     -- Stores data to construct proof
  -- type Proof c v        -- Stores public data sufficient to verify

  -- Allows one to compose zero knowledge proofs and ensures oracle calls are
  -- evaluated over the entire transcript.
  proveM :: CanCommitM v s m => Setup c v s -> Witness c v s -> m (c v s)
  
  -- NOTE: this is not meant to be chained with the proveM. Monad just keeps
  -- track of challenges.
  verifyM :: CanCommitM v s m => Setup c v s -> c v s -> m Bool

type CanCommitM v s m = (CanCommit v s, MonadZKP m, s ~ ScalarZKP m, v ~ CommitZKP m)

class Monad m => MonadZKP m where
  -- The type of commitments
  type CommitZKP m

  -- The type of scalars
  type ScalarZKP m
  
  -- Samples a random value (TODO accept distribution parameter)
  random :: m (ScalarZKP m)

  -- Given a list of commitments, query oracle for scalars
  oracle :: [CommitZKP m] -> m [ScalarZKP m]

-- Convenient for pattern matching
random' :: (Traversable t, Applicative t, MonadZKP m) => m (t (ScalarZKP m))
random' = sequence $ pure random

-- Initialized with a random oracle, a sufficiently long (i.e. infinite) list of
-- random values and stores a list of all commitments.
-- TODO monadic oracle
newtype ZKPT v s m a = ZKPT (RWST ([v] -> m [s]) () ([v], [s]) m a)
  deriving (Functor, Applicative, Monad)

type ZKP' v s a = ZKPT v s Identity a

runZKPT :: (Monad m, CanCommit v s) => ([v] -> m [s]) -> [s] -> ZKPT v s m a -> m a
runZKPT f rs (ZKPT x) = fst <$> evalRWST x f ([], rs)

runZKP' :: CanCommit v s => ([v] -> [s]) -> [s] -> ZKP' v s a -> a
runZKP' f rs (ZKPT x) = fst $ evalRWS x (Identity . f) ([], rs)

instance MonadTrans (ZKPT v s) where
  lift = ZKPT . lift

-- TODO CanCommit not necessary
instance (CanCommit v s, Monad m) => MonadZKP (ZKPT v s m) where
  type CommitZKP (ZKPT v s m) = v
  type ScalarZKP (ZKPT v s m) = s

  -- Pops a value from list of random values
  random = ZKPT $ state $ \(cs, rs) -> (head rs, (cs, tail rs))

  -- Appends to the list of commitments and then hashes using oracle
  oracle xs = ZKPT $ do
    func <- ask
    (cs, rs) <- get
    let cs' = xs ++ cs
    put (cs', rs)
    lift $ func cs'

----------------------
-- Shamir functions --

-- TODO 256 -> bitLength @p either via Bounded or Bits

-- Given a two points and two scalars compute a G + b H consolidating doubling
-- operations.
shamir :: CanCommit v s => v -> s -> v -> s -> v 
shamir g a h b = applyN' 256 step zeroV
  where step n p = addIfV (testBit' a $ n-1) g $ addIfV (testBit' b $ n-1) h $ dbl' p

-- Designed to accept commitWith as an argument. Commits with the function for
-- each bit index in all the scalars, then doubles after this.
--shamirWith :: CanCommit v s => ((s -> v -> v) -> v -> c v -> v) -> v -> c v -> v
shamirWith :: CanCommit v s => ((s -> v -> v) -> (v -> v -> v) -> v -> v) -> v -> v
shamirWith row z = applyN' 256 step z
  where step n !x = row (\ s v -> if testBit' s (n-1) then v else zeroV) (^+^) (dbl' x)

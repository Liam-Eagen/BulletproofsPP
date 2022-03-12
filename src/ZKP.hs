{-# LANGUAGE UndecidableInstances #-}

-- Zero Knowledge proof class and MonadZKP for proving and verifying zero
-- knowledge proofs.

module ZKP where

import Data.Traversable (mapAccumL)
import Data.Functor
import Data.Functor.Identity
import Data.Foldable
import Data.Bifunctor

import Control.Monad.Trans
import Control.Monad.RWS.Strict

import Data.VectorSpace

import Utils

import Commitment (CanCommit)

---------------------------
-- Zero Knoweldge Proofs --

class ZKP c where
  -- NOTE Setup may be used in a confusing way for nested proofs. It stores the
  -- information necessary to setup the inner proof

  type Setup c v s       -- Stores public information independent of particular proof
  type Witness c v s     -- Stores data to construct proof

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

oracle' :: (Traversable t, Applicative t, MonadZKP m) => [CommitZKP m] -> m (t (ScalarZKP m))
oracle' cs = do
  es <- oracle cs
  return $ snd $ mapAccumL (\(e:es) _ -> (es, e)) es $ pure ()

-- Initialized with a random oracle, a sufficiently long (i.e. infinite) list of
-- random values and stores a list of all commitments.
--newtype ZKPT v s m a = ZKPT (RWST ([v] -> m [s]) () ([v], [s]) m a)
newtype ZKPT v s m a = ZKPT (RWST ([v] -> m [s], Int -> s) () ([v], Int) m a)
  deriving (Functor, Applicative, Monad)

type ZKP' v s a = ZKPT v s Identity a

runZKPT :: (Monad m, CanCommit v s) => ([v] -> m [s]) -> (Int -> s) -> ZKPT v s m a -> m a
runZKPT f h (ZKPT x) = fst <$> evalRWST x (f, h) ([], 0)

runZKP' :: CanCommit v s => ([v] -> [s]) -> (Int -> s) -> ZKP' v s a -> a
runZKP' f h (ZKPT x) = fst $ evalRWS x (Identity . f, h) ([], 0)

instance MonadTrans (ZKPT v s) where
  lift = ZKPT . lift

-- TODO CanCommit not necessary
instance (CanCommit v s, Monad m) => MonadZKP (ZKPT v s m) where
  type CommitZKP (ZKPT v s m) = v
  type ScalarZKP (ZKPT v s m) = s

  -- Pops a value from list of random values
  -- TODO call hash with incremented counter instead
  --random = ZKPT $ state $ \(cs, rs) -> (head rs, (cs, tail rs))
  random = ZKPT $ do
    (_, h) <- ask
    -- TODO monadic random action
    state $ \(cs, n) -> (h n, (cs, n+1))

  -- Appends to the list of commitments and then hashes using oracle
  oracle xs = ZKPT $ do
    (func, _) <- ask
    (cs, rs) <- get
    let cs' = xs ++ cs
    put (cs', rs)
    lift $ func cs'

-- TODO it is almost possible to "just" use these functions with the ordinary
-- range proofs. Need the range proofs to support zeroing the input commitment
-- scalars even in conserved/typed mode but retaining the spacing in the
-- commitments. Then we just zero the inputs from other provers in proving mode.
-- The Range Data's are necessary for all the inputs to properly allocate shared
-- bases.
--
-- Also need to supply the write/read operations for whatever communication
-- medium is to be used (Chan, Socket, etc.)

-- Parametric in the communication function
multiPartyClientOracle :: (Monad m, CanCommitM v s m)
                 => (a -> m [s])           -- Type a is hash seed
                 -> ([v] -> m a)           -- Blocking communication
                 -> [v] -> m [s]
multiPartyClientOracle func send cs = send cs >>= func

-- Given client comminication, the dealer sends hash result and awaits a
-- responds. If protocol is over, returns the openings. Otherwise repeats the
-- dealer protocol. This should be general enough to work in either a
-- client/server or p2p situation.
multiPartyDealer :: (Monad m, CanCommitM v s m)
                 => ([v] -> m a)                   -- Type a is hash seed
                 -> (a -> m (Either [b] [[v]]))    -- Get either
                 -> [[v]] -> m [b]
multiPartyDealer func send ps = do
  sd <- func $ foldr (zipWith (^+^)) (repeat zeroV) ps
  res <- send sd
  either return (multiPartyDealer func send) res

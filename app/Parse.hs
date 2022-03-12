{-# LANGUAGE DeriveGeneric, ConstraintKinds, RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints, TypeFamilies, DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings, DeriveFunctor #-}

module Parse where

import GHC.Generics
import Data.Aeson
import Data.Aeson.Types
import qualified Data.Text as T

import Data.Curve hiding (id)
import qualified Data.Curve as C
import Data.Curve.Weierstrass hiding (id)
import qualified Data.Curve.Weierstrass.FastSECP256K1 as SECP256K1

import Data.Bits
import qualified Data.ByteString.Lazy as BSL (ByteString)
import Data.Binary
import Control.Monad

import Utils

import qualified RangeProof.Binary as BRP
import qualified RangeProof.TypedReciprocal as TRRP

--data ProofSpec a = PrfSpec
--  { curve ::      Maybe T.Text          -- Currently only SECP256K1
--  , basisSeed ::  Maybe T.Text          -- Use to generate basis points via hash
--  , basisFile ::  Maybe T.Text          -- File to read basis points from
--  , randomSeed :: Maybe T.Text          -- Generate challenges from hashing this value
--  , binary ::     Maybe Bool            -- If true, use binary range proof. No types or other bases
--  , conserved ::  Maybe Bool            -- If true adds inputs, subtracts outputs defaults False
--  , typed ::      Maybe Bool            -- If true, implies conserved for each type
--  , public ::     Maybe [PublicSpec]    -- Public inputs
--  , ranges ::     [RangeSpec a]         -- If empty, then no proof
--  } deriving (Eq, Show, Generic)
--
--instance FromJSON a => FromJSON (ProofSpec a)
--instance ToJSON a =>   ToJSON   (ProofSpec a)

-- TODO add other curves, need to refactor the shamir code
data CurveType = SECP256K1 | Curve25519
  deriving (Eq, Show, Generic, ToJSON)

instance FromJSON CurveType where
  parseJSON = withText "CurveType" $ \str -> do
    case T.toLower str of
      "secp256k1" -> return SECP256K1
      "curve25519" -> return Curve25519
      _ -> prependFailure "Unsupported Curve: " $ unexpected $ String str

charCurveType :: CurveType -> Integer
charCurveType SECP256K1 = toInteger $ char (C.id :: SECP256K1.PA)
--charCurveType Curve25519 = toInteger $ char (C.id :: Curve25519.PA)

data Argument = IP | NL
  deriving (Eq, Show, Generic, ToJSON)

instance FromJSON Argument where
  parseJSON = withText "CurveType" $ \str -> do
    case T.toLower str of
      s | s `elem` ["ip", "innerproduct"] -> return IP
      s | s `elem` ["nl", "normlinear"] -> return NL
      _ -> prependFailure "Unsupported Argument: " $ unexpected $ String str

-- Stores the information to generate/read basis/randomness
data External = Ext
  { basis :: Either T.Text FilePath          -- Use to generate basis points via hash of from file
  , randomSeed :: T.Text                   -- Generate challenges from hashing this value
  } deriving (Eq, Show, Generic, ToJSON)

instance FromJSON External where
  parseJSON = withObject "External" $ \obj -> do
    bSeed <- obj .:? "basisSeed"
    bFile <- obj .:? "basisFile"
    rs <- maybe' "default random seed" <$> obj .:? "randomSeed"
    flip Ext rs <$> case (bSeed, bFile) of
      (Nothing, Nothing) -> return $ Right "points.bin"
      (Just s,  Nothing) -> return $ Left s
      (Nothing, Just s)  -> return $ Right s
      (Just _, Just _)   -> prependFailure "Cannot specify both point file and seed" $ unexpected $ Object obj

-- Should probably store the setup object directly
-- We allow specifying blinds in the public specs here, don't support in the
-- proof. It might be useful to allow this (Mimblewimble?) currently just check
-- that it is zero
data ProofSpec'
  = RecPrf CurveType Argument External Bool [TRRP.RangeData] [PublicSpec Integer]
  | BinPrf CurveType Argument External Bool [BRP.RangeData] [PublicSpec Integer]
  deriving (Eq, Show, Generic)

external :: ProofSpec' -> External
external (RecPrf _ _ e _ _ _) = e
external (BinPrf _ _ e _ _ _) = e

instance FromJSON ProofSpec' where
  parseJSON = withObject "ProofSpec" $ \obj -> do
    crv <- maybe' SECP256K1 <$> obj .:? "curve"
    arg <- maybe' IP <$> obj .:? "argument"
    ext <- parseJSON $ Object obj                   -- Stored at the same level
    typed <- maybe' False <$> obj .:? "typed"
    con <- maybe' False <$> obj .:? "conserved"
    bin <- maybe' False <$> obj .:? "binary"
    pubs <- (maybe' [] <$> obj .:? "public" >>=) $ mapM $ \pub -> do
      prs@(PubSpec am ty bl io) <- parseJSON pub
      if bl /= Nothing
        then prependFailure "Cannot have blinding on public value" $ unexpected pub
        else return ()

      if bin && ty /=0
        then prependFailure "Cannot have type of public value in binary proof" $ unexpected pub
        else return ()

      return prs
    
    rngs <- obj .: "ranges"

    if typed && bin
      then prependFailure "Can't make typed binary proof" $ unexpected Null
      else return ()

    -- Handle Binary and Reciprocal range proofs seperately
    -- Duplicate ranges based on count
    if bin
      --then prependFailure "Binary proofs unsupported" $ unexpected Null
      then do
        rngs' <- fmap (>>= uncurry replicate) $ forM rngs $ \r -> do
          count <- maybe' 1 <$> r .:? "count"
          min   <- maybe' 0 <$> r .:? "min"
          max   <- maybe' (2^64) <$> r .:? "max"
          isO   <- maybe' False <$> r .:? "isOutput"
          isA   <- maybe' False <$> r .:? "isAssumed" 

          -- Can't support these in binary range proof
          base  <- r .:? "base"
          isS   <- r .:? "isShared"
          case (base, isS) of
            (Just n, _) | n /= 2 -> prependFailure "Invalid base for binary range proof " $ unexpected $ toJSON (n :: Integer)
            (_, Just True) -> prependFailure "Cannot share digits in binary range proof" $ unexpected $ Null
            _ -> return ()

          if any (/= 0) $ kind <$> pubs
            then prependFailure "Cannot specify types for public values in binary range proof" $ unexpected Null
            else return ()

          -- maybe construct range proof object
          case BRP.makeRangeData (charCurveType crv) (R min max) isO isA of
            Nothing -> prependFailure "Invalid range: " $ unexpected $ Object r
            Just r' -> return (count, r')

        -- Binary range proof
        return $ BinPrf crv arg ext con rngs' pubs
      else do
        -- Duplicate ranges based on count
        rngs' <- fmap (>>= uncurry replicate) $ forM rngs $ \r -> do
          count <- maybe' 1 <$> r .:? "count"
          min   <- maybe' 0 <$> r .:? "min"
          max   <- maybe' (2^64) <$> r .:? "max"
          base  <- maybe' (approxLogW $ max - min) <$> r .:? "base"
          isS   <- maybe' False <$> r .:? "isShared"
          isO   <- maybe' False <$> r .:? "isOutput"
          isA   <- maybe' False <$> r .:? "isAssumed" 

          -- maybe construct range proof object
          case TRRP.makeRangeData (charCurveType crv) base (R min max) isS isO isA of
            Nothing -> prependFailure "Invalid range: " $ unexpected $ Object r
            Just r' -> return (count, r')

        -- Technically different but currently don't differentiate between typed
        -- and conserved proofs
        return $ RecPrf crv arg ext (typed || con) rngs' pubs

data RangeSpec a = RngSpec
  { count ::    Maybe Integer          -- Defaults 1, how many of this range to prove
  , base ::     Maybe Integer           -- Base for the range proof, defaults to optimal for range
  , min ::      Maybe Integer            -- Defaults to zero
  , max ::      Maybe Integer            -- Defaults to 2^64
  , isShared ::   Maybe Bool            -- Defaults to False, cannot be true in binary
  , isOutput :: Maybe Bool          -- Defaults to True, if false
  , isAssumed ::   Maybe Bool            -- If true, do not construct range proof only type check
  } deriving (Eq, Show, Generic)

instance FromJSON a => FromJSON (RangeSpec a)
instance ToJSON a =>   ToJSON   (RangeSpec a)


maybe' :: a -> Maybe a -> a
maybe' x m = maybe x id m
-- 
-- -- y^y = x => y = exp(W(log(x))
-- -- exp(W(log(x)) ~ log(x)/log(log(x))
-- --
-- -- Probably should have a more inteligent procedure
approxLogW :: Integer -> Integer
approxLogW n = l `div` ll
  where
    l = integerLog 2 n
    ll = integerLog 2 l

-- -- Transforms the JSON range spec parse to a valid object
-- parseRangeSpec :: MonadError ParseError m => Bool -> RangeSpec a -> m RangeParse
-- parseRangeSpec isBool rs = do
--   let pCount = maybe'  1      $ count rs
--   let pAssume = maybe' False  $ assume rs
--   let pMin = maybe'    0      $ min rs
--   let pMax = maybe'    (2^64) $ max rs
--   let pShared = maybe' False  $ shared rs
-- 
--   -- Find x^x ~ max - min
--   let optInline = approxLogW (pMax - pMin)
--   
--   let pBase = maybe' approxLogW $ base rs
-- 
--   return 

-- Functor instance for convenience
data PublicSpec a = PubSpec
  { amount :: a -- Integer
  , kind :: a -- Integer
  , blind :: Maybe a -- Integer
  , isOutputPub :: Bool
  } deriving (Eq, Show, Functor, Generic, ToJSON)

--instance FromJSON PublicSpec
instance (FromJSON a, Integral a) => FromJSON (PublicSpec a) where
  parseJSON = withObject "PublicSpec" $ \obj -> do
    amount <- obj .: "amount"
    kind <- maybe' 0 <$> obj .:? "type"
    --kind <- obj .:? "type"
    blind <- obj .:? "blind"
    --blind <- obj .:? "blind"
    isO <- maybe' False <$> obj .:? "isOutput"

    return $ PubSpec amount kind blind isO

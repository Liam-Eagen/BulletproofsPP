{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses#-}

module Data.Curve.CM where

import Data.List (minimumBy)
import Data.Field.Galois
import qualified Data.Field.Galois as G -- .Prime
import Data.Field.Eis

import Data.Curve
import Data.Curve.Weierstrass

-- Curve with j invariant have Eis CM. Currently only works over prime fields
class (Curve f c e q r, HasEis q, HasEis r) => CMCurve f c e q r where
  -- cmConj p = unity3 `mul` p but typically much faster
  cmConj :: Point f c e q r -> Point f c e q r

class (WCurve c e q r, HasEis q, HasEis r) => CMWCurve c e q r where
  -- Weierstrass curves multiply x coordinate by third root of unity
  -- TODO need to check that this agrees in general as canonical roots may
  -- not agree
  unity3_ :: WPoint c e q r -> q
  unity3_ _ = unity3

instance (WACurve e q r, CMWCurve 'Affine e q r) => CMCurve 'Weierstrass 'Affine e q r where
  cmConj O = O
  cmConj p@(A x y) = A (unity3_ p * x) y

instance (WPCurve e q r, CMWCurve 'Projective e q r) => CMCurve 'Weierstrass 'Projective e q r where
  cmConj p@(P x y z) = P (unity3_ p * x) y z

instance (WJCurve e q r, CMWCurve 'Jacobian e q r) => CMCurve 'Weierstrass 'Jacobian e q r where
  cmConj p@(J x y z) = J (unity3_ p * x) y z
  

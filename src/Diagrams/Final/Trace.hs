{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Diagrams.Final.Trace where

import Control.Applicative
import Control.Lens
import Data.Set (Set)

import Diagrams.Final.Base
import Diagrams.Final.Space

newtype Trace = Trace { unTrace :: Point Scalar -> Vector Scalar -> Set Scalar }

instance Wrapped Trace where
  type Unwrapped Trace = Point Scalar -> Vector Scalar -> Set Scalar
  _Wrapped' = iso unTrace Trace

instance Rewrapped Trace Trace

deriving instance Semigroup Trace
deriving instance Monoid Trace

class Spatial repr => Traces repr where
  toTrace :: repr (Point Scalar -> Vector Scalar -> Set Scalar) -> repr Trace
  fromTrace :: repr Trace -> repr (Point Scalar) -> repr (Vector Scalar) -> repr (Set Scalar)

instance Applicative repr => Traces (ViaApplicative repr) where
  toTrace = fmap Trace
  fromTrace = liftA3 unTrace

deriving via (ViaApplicative Identity) instance Traces Identity
deriving via (repr :: * -> *) instance Traces repr => Traces (ViaSpatial repr)

instance (Lambda repr, Traces repr) => AffineAction' Trace repr where
  actA' a t =
    let_ (linearOf a) $ \l ->
      toTrace $ lam $ \p -> lam $ \v ->
        fromTrace t (actA' (inverseAffine a) p) (actL' (inverseLinear l) v)

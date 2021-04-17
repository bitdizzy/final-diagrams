{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Trace where

import Control.Lens

import Diagrams.Final.Base
import Diagrams.Final.Space

newtype Trace repr = Trace { unTrace :: Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar)) }

instance Wrapped (Trace repr) where
  type Unwrapped (Trace repr) = Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))
  _Wrapped' = iso unTrace Trace

instance Rewrapped (Trace repr) (Trace repr)

class (Spatial repr, Semigroup' (Set' repr Scalar) repr) => Traces repr where
  toTrace :: repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))) -> repr (Trace repr)
  fromTrace :: repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set' repr Scalar)
  default toTrace :: Functor repr => repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))) -> repr (Trace repr)
  toTrace = fmap Trace
  default fromTrace :: Functor repr => repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set' repr Scalar)
  fromTrace f p v = fmap unTrace f %$ p %$ v

instance Traces Identity

instance (Lambda repr, Traces repr) => AffineAction' Scalar (Trace repr) repr where
  actA' a t = withSpatial @repr @Scalar $
    let_ (linearOf a) $ \l ->
      toTrace $ lam $ \p -> lam $ \v ->
        fromTrace t (actA' (inverseAffine a) p) (actL' (inverseLinear l) v)

instance Traces repr => Semigroup' (Trace repr) repr where
  t1 %<> t2 = toTrace $ lam $ \p -> lam $ \v -> fromTrace t1 p v %<> fromTrace t2 p v

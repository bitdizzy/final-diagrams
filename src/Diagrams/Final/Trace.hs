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
{-# OPTIONS_GHC -Wno-orphans #-}
module Diagrams.Final.Trace where

import Control.Lens
import Data.Set

import Diagrams.Final.Base
import Diagrams.Final.Space

newtype DefaultTrace repr = DefaultTrace { unDefaultTrace :: Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar)) }

instance Wrapped (DefaultTrace repr) where
  type Unwrapped (DefaultTrace repr) = Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))
  _Wrapped' = iso unDefaultTrace DefaultTrace

instance Rewrapped (DefaultTrace repr) (DefaultTrace repr)

class (Spatial repr, Monoid' (Set' repr Scalar) repr, AffineAction' Scalar (Trace repr) repr, Semigroup' (Trace repr) repr) => Traces repr where
  type Trace repr :: *
  type Trace repr = DefaultTrace repr
  emptyTrace :: repr (Trace repr)
  toTrace :: repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))) -> repr (Trace repr)
  fromTrace :: repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set' repr Scalar)
  default emptyTrace :: (Applicative repr, Trace repr ~ DefaultTrace repr) => repr (Trace repr)
  emptyTrace = toTrace $ lam $ \_ -> lam $ \_ -> mempty' -- pure mempty
  default toTrace :: (Functor repr, Trace repr ~ DefaultTrace repr) => repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set' repr Scalar))) -> repr (Trace repr)
  toTrace = fmap DefaultTrace
  default fromTrace :: (Functor repr, Trace repr ~ DefaultTrace repr) => repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set' repr Scalar)
  fromTrace f p v = fmap unDefaultTrace f %$ p %$ v

instance Semigroup' (Set Scalar) Identity
instance Monoid' (Set Scalar) Identity
instance Traces Identity

instance (Lambda repr, Traces repr, Trace repr ~ DefaultTrace repr) => AffineAction' Scalar (DefaultTrace repr) repr where
  actA' a t = withSpatial @repr @Scalar $
    let_ (linearOf a) $ \l ->
      toTrace $ lam $ \p -> lam $ \v ->
        fromTrace t (actA' (inverseAffine a) p) (actL' (inverseLinear l) v)

instance (Traces repr, Trace repr ~ DefaultTrace repr) => Semigroup' (DefaultTrace repr) repr where
  t1 %<> t2 = toTrace $ lam $ \p -> lam $ \v -> fromTrace t1 p v %<> fromTrace t2 p v

instance (Traces repr, Trace repr ~ DefaultTrace repr) => Monoid' (DefaultTrace repr) repr where
  mempty' = emptyTrace

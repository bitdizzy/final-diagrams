{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Diagrams.Final.Core.Trace where

import Control.Lens
import Data.Set

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space

newtype Trace repr = Trace { unTrace :: Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar)) }

instance Wrapped (Trace repr) where
  type Unwrapped (Trace repr) = Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))
  _Wrapped' = iso unTrace Trace

instance Rewrapped (Trace repr) (Trace repr)

class (Spatial repr, Monoid' (Set Scalar) repr, AffineAction' Scalar (Trace repr) repr, Semigroup' (Trace repr) repr, Monoid' (Trace repr) repr) => Traces repr where
  emptyTrace :: repr (Trace repr)
  toTrace :: repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))) -> repr (Trace repr)
  fromTrace :: repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set Scalar)
  default emptyTrace :: (Applicative repr, Lambda repr) => repr (Trace repr)
  emptyTrace = toTrace $ lam $ \_ -> lam $ \_ -> mempty' -- pure mempty
  default toTrace :: (Functor repr) => repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))) -> repr (Trace repr)
  toTrace = fmap Trace
  default fromTrace :: (Functor repr, Lambda repr) => repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set Scalar)
  fromTrace f p v = fmap unTrace f %$ p %$ v

instance Semigroup' (Set Scalar) Identity
instance Monoid' (Set Scalar) Identity
instance Traces Identity

instance (Lambda repr, Traces repr) => AffineAction' Scalar (Trace repr) repr where
  actA' a t =
    let_ (linearOf a) $ \l ->
      toTrace $ lam $ \p -> lam $ \v ->
        fromTrace t (actA' (inverseAffine a) p) (actL' (inverseLinear l) v)

instance (Lambda repr, Traces repr) => Semigroup' (Trace repr) repr where
  t1 %<> t2 = toTrace $ lam $ \p -> lam $ \v -> fromTrace t1 p v %<> fromTrace t2 p v

instance (Lambda repr, Traces repr) => Monoid' (Trace repr) repr where
  mempty' = emptyTrace

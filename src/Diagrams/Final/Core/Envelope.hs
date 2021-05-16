{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Core.Envelope where

import Control.Lens hiding (re)

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space

newtype DefaultEnvelope repr = DefaultEnvelope { unDefaultEnvelope :: Maybe' repr (Arr repr (Vector repr Scalar) Scalar) }

instance Wrapped (DefaultEnvelope repr) where
  type Unwrapped (DefaultEnvelope repr) = Maybe' repr (Arr repr (Vector repr Scalar) Scalar)
  _Wrapped' = iso (\(DefaultEnvelope e) -> e) DefaultEnvelope

instance Rewrapped (DefaultEnvelope repr) (DefaultEnvelope repr)

class (Spatial repr, AffineAction' Scalar (Envelope repr) repr, Semigroup' (Envelope repr) repr, Monoid' (Envelope repr) repr) => Envelopes repr where
  type Envelope repr :: *
  type Envelope repr = DefaultEnvelope repr
  emptyEnvelope :: repr (Envelope repr)
  envelope
    :: repr (Arr repr (Vector repr Scalar) Scalar)
    -> repr (Envelope repr)
  withEnvelope
    :: repr (Envelope repr)
    -> repr a
    -> repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) a)
    -> repr a
  onEnvelope
    :: repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) (Arr repr (Vector repr Scalar) Scalar))
    -> repr (Envelope repr)
    -> repr (Envelope repr)
  default emptyEnvelope
    :: (Applicative repr, Maybe' repr ~ Lift1 repr Maybe, Envelope repr ~ DefaultEnvelope repr)
    => repr (Envelope repr)
  emptyEnvelope = pure $ DefaultEnvelope $ Lift1 Nothing
  default envelope
    :: (Functor repr, LiftMaybe repr, Envelope repr ~ DefaultEnvelope repr)
    => repr (Arr repr (Vector repr Scalar) Scalar)
    -> repr (Envelope repr)
  envelope = fmap DefaultEnvelope . just'
  default withEnvelope
    :: (Functor repr, LiftMaybe repr, Envelope repr ~ DefaultEnvelope repr)
    => repr (Envelope repr)
    -> repr a
    -> repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) a)
    -> repr a
  withEnvelope e k0 k1 = maybe' k0 k1 (fmap unDefaultEnvelope e)
  default onEnvelope
    :: (Functor repr, LiftMaybe repr, Lambda arr repr, Envelope repr ~ DefaultEnvelope repr)
    => repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) (Arr repr (Vector repr Scalar) Scalar))
    -> repr (Envelope repr)
    -> repr (Envelope repr)
  onEnvelope f = maybe' emptyEnvelope (lam (envelope . app f)) . fmap unDefaultEnvelope

instance Envelopes Identity

instance (Lambda arr repr, Envelopes repr, Envelope repr ~ DefaultEnvelope repr) => AffineAction' Scalar (DefaultEnvelope repr) repr where
  actA' a = onEnvelope $ lam $ \f -> lam $ \v ->
    let_ (linearOf a) $ \l ->
      let_ (translationOf a) $ \t ->
        let_ (actL' (adjoint l) v) $ \v' ->
           (quadrance' v' %* (f %$ v') %+ v `dot'` t) %/ quadrance' v

instance (Lambda arr repr, Envelopes repr, Envelope repr ~ DefaultEnvelope repr) => Semigroup' (DefaultEnvelope repr) repr where
  e1 %<> e2 = withEnvelope e1 e2 $ lam $ \f1 -> withEnvelope e2 emptyEnvelope $ lam $ \f2 ->
   envelope $ lam $ \v -> max' (f1 %$ v) (f2 %$ v)

instance (Envelopes repr, Envelope repr ~ DefaultEnvelope repr) => Monoid' (DefaultEnvelope repr) repr where
  mempty' = emptyEnvelope

class Envelopes repr => Enveloped a repr where
  envelopeOf :: repr a -> repr (Envelope repr)

extent
  :: (Envelopes repr, LiftMaybe repr, Lambda arr repr, Tuple2 repr)
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr (Maybe' repr (Scalar, Scalar))
extent v e = withEnvelope e nothing' $ lam $ \f ->
  just' $ tup2' (negate' (f $% negated' v)) (f $% v)

diameter
  :: (Envelopes repr, LiftMaybe repr, Lambda arr repr, Tuple2 repr)
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr Scalar
diameter v e = maybe' 0
  (lam $ \tup ->
     let_ (pi1' tup) $ \lo -> let_ (pi2' tup) $ \hi ->
       hi %- lo %* norm' v
  )
  (extent v e)

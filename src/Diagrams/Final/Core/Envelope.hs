{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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
import Data.Set (Set)

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space

newtype Envelope repr = Envelope { unEnvelope :: Maybe' repr (Arr repr (Vector repr Scalar) Scalar) }

instance Wrapped (Envelope repr) where
  type Unwrapped (Envelope repr) = Maybe' repr (Arr repr (Vector repr Scalar) Scalar)
  _Wrapped' = iso (\(Envelope e) -> e) Envelope

instance Rewrapped (Envelope repr) (Envelope repr)

class (Spatial repr, AffineAction' Scalar (Envelope repr) repr, Semigroup' (Envelope repr) repr, Monoid' (Envelope repr) repr) => Envelopes repr where
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
    :: Applicative repr => repr (Envelope repr)
  emptyEnvelope = pure $ Envelope $ T1 Nothing
  default envelope
    :: (Functor repr, LiftMaybe repr)
    => repr (Arr repr (Vector repr Scalar) Scalar)
    -> repr (Envelope repr)
  envelope = fmap Envelope . just'
  default withEnvelope
    :: (Functor repr, LiftMaybe repr)
    => repr (Envelope repr)
    -> repr a
    -> repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) a)
    -> repr a
  withEnvelope e k0 k1 = maybe' k0 k1 (fmap unEnvelope e)
  default onEnvelope
    :: (Functor repr, LiftMaybe repr, Lambda repr)
    => repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) (Arr repr (Vector repr Scalar) Scalar))
    -> repr (Envelope repr)
    -> repr (Envelope repr)
  onEnvelope f = maybe' emptyEnvelope (lam (envelope . app f)) . fmap unEnvelope

instance Envelopes Identity

instance (Lambda repr, Envelopes repr) => AffineAction' Scalar (Envelope repr) repr where
  actA' a = onEnvelope $ lam $ \f -> lam $ \v ->
    let_ (linearOf a) $ \l ->
      let_ (translationOf a) $ \t ->
        let_ (actL' (adjoint l) v) $ \v' ->
           (quadrance' v' %* (f %$ v') %+ v `dot'` t) %/ quadrance' v

instance (Lambda repr, Envelopes repr) => Semigroup' (Envelope repr) repr where
  e1 %<> e2 = withEnvelope e1 e2 $ lam $ \f1 -> withEnvelope e2 emptyEnvelope $ lam $ \f2 ->
   envelope $ lam $ \v -> max' (f1 %$ v) (f2 %$ v)

instance (Lambda repr, Envelopes repr) => Monoid' (Envelope repr) repr where
  mempty' = emptyEnvelope

class Envelopes repr => Enveloped a repr where
  envelopeOf :: repr a -> repr (Envelope repr)

instance Envelopes repr => Enveloped (Envelope repr) repr where
  envelopeOf = id

instance (Envelopes repr, Enveloped a repr, Enveloped b repr) => Enveloped (a, b) repr where
  envelopeOf ab = envelopeOf (pi1' ab) %<> envelopeOf (pi2' ab)

instance (Lambda repr, Envelopes repr, Enveloped a repr, LiftList repr) => Enveloped (List' repr a) repr where
  envelopeOf = foldMap' (lam envelopeOf)

instance (Ord' a repr, Lambda repr, Envelopes repr, Enveloped a repr, LiftSet repr) => Enveloped (Set a) repr where
  envelopeOf = envelopeOf . toAscList

extent
  :: (Envelopes repr, LiftMaybe repr, Lambda repr, Tuple2 repr)
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr (Maybe' repr (Scalar, Scalar))
extent v e = withEnvelope e nothing' $ lam $ \f ->
  just' $ tup2' (negate' (f $% negated' v)) (f $% v)

diameter
  :: (Envelopes repr, LiftMaybe repr, Lambda repr, Tuple2 repr)
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr Scalar
diameter v e = maybe' 0
  (lam $ \tup ->
     let_ (pi1' tup) $ \lo -> let_ (pi2' tup) $ \hi ->
       hi %- lo %* norm' v
  )
  (extent v e)

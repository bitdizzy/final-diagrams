{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Diagrams.Final.Envelope where

import Control.Applicative
import Control.Lens
import Data.Semigroup

import Diagrams.Final.Base
import Diagrams.Final.Space

newtype Envelope = Envelope (Maybe (Vector Scalar -> Scalar))

deriving via (Maybe (Vector Scalar -> Max Scalar)) instance Semigroup Envelope
deriving via (Maybe (Vector Scalar -> Max Scalar)) instance Monoid Envelope

instance Wrapped Envelope where
  type Unwrapped Envelope = Maybe (Vector Scalar -> Scalar)
  _Wrapped' = iso (\(Envelope e) -> e) Envelope

instance Rewrapped Envelope Envelope

class Spatial repr => Envelopes repr where
  emptyEnvelope :: repr Envelope
  envelope :: repr Envelope -> repr a -> repr ((Vector Scalar -> Scalar) -> a) -> repr a
  onEnvelope :: repr ((Vector Scalar -> Scalar) -> (Vector Scalar -> Scalar)) -> repr Envelope -> repr Envelope

instance (Applicative repr, AffineAction' Envelope repr) => Envelopes (ViaApplicative repr) where
  emptyEnvelope = pure $ Envelope Nothing
  onEnvelope f x = over (_Wrapping' Envelope . mapped) <$> f <*> x
  envelope = liftA3 $ \(Envelope e) k0 k1 -> case e of
    Nothing -> k0
    Just f -> k1 f

deriving via (ViaApplicative Identity) instance Envelopes Identity
deriving via (repr :: * -> *) instance Envelopes repr => Envelopes (ViaSpatial repr)

instance (Lambda repr, Envelopes repr) => AffineAction' Envelope (ViaSpatial repr) where
  actA' a = onEnvelope $ lam $ \f -> lam $ \v ->
    let_ (linearOf a) $ \l ->
      let_ (translationOf a) $ \t ->
        let_ (actL' (adjoint l) v) $ \v' ->
           (quadrance' v' %* (f %$ v') %+ v `dot'` t) %/ quadrance' v

instance AffineAction Envelope where
  actA l x = runIdentity $ actA' (Identity l) (Identity x)

extent
  :: (Envelopes repr, Maybe' repr, Lambda repr, Tuple2 repr)
  => repr (Vector Scalar)
  -> repr Envelope
  -> repr (Maybe (Scalar, Scalar))
extent v e = envelope e nothing' $ lam $ \f ->
  just' $ tup2' (negate' (f $% negated' v)) (f $% v)

diameter
  :: (Envelopes repr, Maybe' repr, Lambda repr, Tuple2 repr)
  => repr (Vector Scalar)
  -> repr Envelope
  -> repr Scalar
diameter v e = maybe' 0
  (lam $ \tup ->
     let_ (fst' tup) $ \lo -> let_ (snd' tup) $ \hi ->
       hi %- lo %* norm' v
  )
  (extent v e)

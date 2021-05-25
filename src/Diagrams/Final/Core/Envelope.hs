{-# LANGUAGE BlockArguments #-}
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
import Linear (zero, E(..))

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space

newtype Envelope repr = Envelope { unEnvelope :: Maybe' repr (Arr repr (Vector repr Scalar) Scalar) }

instance Wrapped (Envelope repr) where
  type Unwrapped (Envelope repr) = Maybe' repr (Arr repr (Vector repr Scalar) Scalar)
  _Wrapped' = iso (\(Envelope e) -> e) Envelope

instance Rewrapped (Envelope repr) (Envelope repr)

class (Spatial repr, AffineAction' repr Scalar (Envelope repr), Semigroup' repr (Envelope repr), Monoid' repr (Envelope repr)) => Envelopes repr where
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
  withEnvelope e k0 k1 = maybe' (fmap unEnvelope e) k0 k1
  default onEnvelope
    :: (Functor repr, LiftMaybe repr, Lambda repr)
    => repr (Arr repr (Arr repr (Vector repr Scalar) Scalar) (Arr repr (Vector repr Scalar) Scalar))
    -> repr (Envelope repr)
    -> repr (Envelope repr)
  onEnvelope f m = maybe' (fmap unEnvelope m) emptyEnvelope (lam (envelope . app f))

instance Envelopes Identity

instance (Lambda repr, Envelopes repr) => AffineAction' repr Scalar (Envelope repr) where
  actA' a = onEnvelope $ lam $ \f -> lam $ \v ->
    let_ (linearOf a) $ \l ->
      let_ (translationOf a) $ \t ->
        let_ (actL' (adjoint l) v) $ \v' ->
           (quadrance' v' %* (f %$ v') %+ v `dot'` t) %/ quadrance' v

instance (Lambda repr, Envelopes repr) => Semigroup' repr (Envelope repr) where
  e1 %<> e2 = withEnvelope e1 e2 $ lam $ \f1 -> withEnvelope e2 emptyEnvelope $ lam $ \f2 ->
   envelope $ lam $ \v -> max' (f1 %$ v) (f2 %$ v)

instance (Lambda repr, Envelopes repr) => Monoid' repr (Envelope repr) where
  mempty' = emptyEnvelope

class Enveloped repr a where
  envelopeOf :: repr a -> repr (Envelope repr)

instance Enveloped repr (Envelope repr) where
  envelopeOf = id

instance (Lambda repr, Envelopes repr, Enveloped repr a, Enveloped repr b) => Enveloped repr (a, b) where
  envelopeOf ab = envelopeOf (pi1' ab) %<> envelopeOf (pi2' ab)

instance (Lambda repr, Envelopes repr, Enveloped repr a, LiftList repr) => Enveloped repr (List' repr a) where
  envelopeOf = foldMap' (lam envelopeOf)

instance (Ord' repr a, Lambda repr, Envelopes repr, Enveloped repr a, LiftSet repr) => Enveloped repr (Set a) where
  envelopeOf = envelopeOf . toAscList'

--TODO: Map instance

envelopeVMay :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Vector repr Scalar))
envelopeVMay v e = withEnvelope (envelopeOf e) nothing' $ lam $ \f -> just' $ (f %$ v) %*^ v

envelopeV :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr (Vector repr Scalar)
envelopeV v = (\m -> maybe' m zero' id') . envelopeVMay v

envelopePMay :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Point repr Scalar))
envelopePMay v = fmap' (lam $ (origin %.+^)) . envelopeVMay v

envelopeP :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr (Point repr Scalar)
envelopeP v = (origin %.+^) . envelopeV v

envelopeSMay :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr Scalar)
envelopeSMay v e = withEnvelope (envelopeOf e) nothing' $ lam $ \f -> just' $ (f %$ v) %* norm' v

envelopeS :: (Envelopes repr, Enveloped repr a) => repr (Vector repr Scalar) -> repr a -> repr Scalar
envelopeS v = (\m -> maybe' m 0 id') . envelopeSMay v

pointEnvelope :: Envelopes repr => repr (Point repr Scalar) -> repr (Envelope repr)
pointEnvelope p = moveTo p $ envelope $ lam \_ -> 0

diameter
  :: Envelopes repr
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr Scalar
diameter v e = maybe' (extent v e) 0
  (lam $ \tup ->
     let_ (pi1' tup) $ \lo -> let_ (pi2' tup) $ \hi ->
       hi %- lo %* norm' v
  )

radius
  :: Envelopes repr
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr Scalar
radius v = (0.5 %*) . diameter v

extent
  :: (Envelopes repr, LiftMaybe repr, Lambda repr, Tuple2 repr)
  => repr (Vector repr Scalar)
  -> repr (Envelope repr)
  -> repr (Maybe' repr (Scalar, Scalar))
extent v e = withEnvelope e nothing' $ lam $ \f ->
  just' $ tup2' (negate' (f $% negated' v)) (f $% v)

size :: Envelopes repr => repr (Envelope repr) -> repr (Vector repr Scalar)
size d = tabulate' $ \(E l) -> diameter (val1 (zero & l .~ 1)) d

-- Juxtaposition

class Juxtapose repr a where
  juxtapose :: repr (Vector repr Scalar) -> repr a -> repr a -> repr a
  default juxtapose :: (Envelopes repr, Enveloped repr a, AffineAction' repr Scalar a) => repr (Vector repr Scalar) -> repr a -> repr a -> repr a
  juxtapose v a1 a2 =
    let mv1 = lam negated' <%$> envelopeVMay v a1
        mv2 = envelopeVMay (negated' v) a2
     in maybe' mv1 a2 $ lam $ \v1 -> maybe' mv2 a2 $ lam $ \v2 -> actA' (translateBy (negated' (v1 %^+^ v2))) a2

instance Envelopes repr => Juxtapose repr (Envelope repr)

instance (Envelopes repr, Enveloped repr a, Enveloped repr b, AffineAction' repr Scalar a, AffineAction' repr Scalar b) => Juxtapose repr (a,b)

instance (Envelopes repr, Enveloped repr a, AffineAction' repr Scalar a) => Juxtapose repr (List' repr a)

instance (Envelopes repr, Enveloped repr a, Ord' repr a, AffineAction' repr Scalar a) => Juxtapose repr (Set a)

instance (Envelopes repr, Juxtapose repr b) => Juxtapose repr (Arr repr a b) where
  juxtapose v f1 f2 = lam $ \a -> juxtapose v (f1 %$ a) (f2 %$ a)

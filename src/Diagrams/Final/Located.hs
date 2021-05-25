{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
module Diagrams.Final.Located where

import Control.Monad

import Diagrams.Final.Core
import Diagrams.Final.Align

data Located repr a = Located
  { _located_value :: repr a
  , _located_location :: repr (Point repr Scalar)
  }

class (forall a. Val repr (Located repr a)) => LiftLocated repr where
  locatedAt' :: repr a -> repr (Point repr Scalar) -> repr (Located repr a)
  located' :: repr (Located repr a) -> (repr a -> repr (Point repr Scalar) -> repr r) -> repr r
  default locatedAt' :: Applicative repr => repr a -> repr (Point repr Scalar) -> repr (Located repr a)
  locatedAt' = (pure .) . Located
  default located' :: Monad repr => repr (Located repr a) -> (repr a -> repr (Point repr Scalar) -> repr r) -> repr r
  located' lv k = join $ flip fmap lv $ \(Located v l) -> k v l

unLocated :: LiftLocated repr => repr (Located repr v) -> repr v
unLocated vl = located' vl $ \v _ -> v

instance (Spatial repr, LiftLocated repr) => HasOrigin repr (Located repr a) where
  moveOriginBy t vl = located' vl $ \v l -> locatedAt' v (moveOriginBy t l)

instance (Spatial repr, LiftLocated repr, LinearAction' repr Scalar a) => AffineAction' repr Scalar (Located repr a) where
  actA' t vl = located' vl $ \v l -> locatedAt' (actL' (linearOf t) v) (moveOriginBy (translationOf t) l)

instance (Envelopes repr, LiftLocated repr, Enveloped repr a) => Enveloped repr (Located repr a) where
  envelopeOf vl = located' vl $ \v l -> moveTo l (envelopeOf v)

instance (Traces repr, LiftLocated repr, Traced repr a) => Traced repr (Located repr a) where
  traceOf vl = located' vl $ \v l -> moveTo l (traceOf v)

instance (Envelopes repr, LiftLocated repr, Enveloped repr a) => Juxtapose repr (Located repr a)

instance (LiftLocated repr, Alignable repr a) => Alignable repr (Located repr a) where
  defaultBoundary = lam2 $ \v -> app2 defaultBoundary v . unLocated

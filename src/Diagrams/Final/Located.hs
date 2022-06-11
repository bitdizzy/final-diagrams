{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Diagrams.Final.Located where

import Control.Monad

import Diagrams.Final.Core
import Diagrams.Final.Align
import Diagrams.Final.Parametric

data Located repr a = Located
  { _located_value :: repr a
  , _located_location :: repr (Point repr Scalar)
  }

class LiftLocated repr where
  locatedAt' :: repr a -> repr (Point repr Scalar) -> repr (Located repr a)
  located' :: repr (Located repr a) -> (repr a -> repr (Point repr Scalar) -> repr r) -> repr r
  default locatedAt' :: Applicative repr => repr a -> repr (Point repr Scalar) -> repr (Located repr a)
  locatedAt' = (pure .) . Located
  default located' :: Monad repr => repr (Located repr a) -> (repr a -> repr (Point repr Scalar) -> repr r) -> repr r
  located' lv k = join $ flip fmap lv $ \(Located v l) -> k v l

unLocated :: LiftLocated repr => repr (Located repr v) -> repr v
unLocated vl = located' vl $ \v _ -> v

lVec :: (Spatial repr, LiftLocated repr) => repr (Located repr (Vector repr Scalar)) -> repr (Point repr Scalar)
lVec vl = located' vl $ \v p -> p %.+^ v

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

instance
  ( LiftLocated repr
  , Spatial repr
  , Parametric repr a (PDom a) (PCod a)
  , x ~ PDom a
  , Vector repr Scalar ~ PCod a
  ) => Parametric repr (Located repr a) x (Point repr Scalar) where
  type PDom (Located repr a) = PDom a
  type PCod (Located repr a) = Point repr Scalar
  pl `atParam` t = located' pl $ \p l -> l %.+^ (p `atParam` t)

instance
  ( LiftLocated repr
  , DomainBounds repr a
  ) => DomainBounds repr (Located repr a) where
  domainLower pl = located' pl $ \p _ -> domainLower p
  domainUpper pl = located' pl $ \p _ -> domainUpper p

instance
  ( LiftLocated repr
  , Spatial repr
  , Fractional' repr (PDom a)
  , Parametric repr a (PDom a) (Vector repr Scalar)
  , Sectionable repr a
  ) => Sectionable repr (Located repr a) where
  splitAtParam pl t = located' pl $ \p l ->
    let ab = splitAtParam p t
     in tup2' (pi1' ab `locatedAt'` l) (pi2' ab `locatedAt'` (l %.+^ (p `atParam` t)))

  section pl t1 t2 = located' pl $ \p l -> section p t1 t2 `locatedAt'` (l %.+^ (p `atParam` t1))

  reverseDomain pl = located' pl $ \p l -> reverseDomain p `locatedAt'` (l %.+^ (p `atParam` domainUpper p))

instance
  ( LiftLocated repr
  , Spatial repr
  , PCod a ~ Vector repr Scalar
  , HasArcLength repr a
  ) => HasArcLength repr (Located repr a) where
  arcLengthBounded eps pl = located' pl $ \p _ -> arcLengthBounded eps p
  arcLengthToParam eps pl t = located' pl $ \p _ -> arcLengthToParam eps p t

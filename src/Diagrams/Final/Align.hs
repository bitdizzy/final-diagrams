{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Align where

import Data.Set (Set)

import Diagrams.Final.Core

class (AffineAction' repr Scalar a, Spatial repr) => Alignable repr a where
  alignBy'
    :: repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar)))
    -> repr (Vector repr Scalar)
    -> repr Scalar
    -> repr a
    -> repr a
  defaultBoundary :: repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar)))
  alignBy
    :: repr (Vector repr Scalar)
    -> repr Scalar
    -> repr a
    -> repr a
  alignBy = alignBy' defaultBoundary
  default alignBy'
    :: (AffineAction' repr Scalar a)
    => repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar)))
    -> repr (Vector repr Scalar)
    -> repr Scalar
    -> repr a
    -> repr a
  alignBy' boundary v d a = flip moveOriginTo a $ lerp'
    ((d %+ 1) %/ 2)
    (boundary %$ v %$ a)
    (boundary %$ negated' v %$ a)
  default defaultBoundary :: (Envelopes repr, Enveloped repr a) => repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar)))
  defaultBoundary = lam2 envelopeP

traceBoundary :: (Traces repr, Traced repr a) => repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar)))
traceBoundary = lam2 \v a -> maybe' (maxTraceP origin v a) origin id'

combineBoundaries :: (Spatial repr, Foldable' repr f) => repr (Arr repr (Vector repr Scalar) (Arr repr a (Point repr Scalar))) -> repr (Vector repr Scalar) -> repr (f a) -> repr (Point repr Scalar)
combineBoundaries b v fa =
  maybe' (maximumBy' (lam2 (comparing' $ lam (dot' v . (%.-. origin) . (app2 b v)))) fa) origin (b %$ v)

instance Envelopes repr => Alignable repr (Envelope repr) where

instance Traces repr => Alignable repr (Trace repr) where
  defaultBoundary = traceBoundary

instance (Spatial repr, Alignable repr a, LiftList repr) => Alignable repr (List' repr a) where
  defaultBoundary = lam2 $ combineBoundaries defaultBoundary

instance (Spatial repr, Alignable repr a, Ord' repr a, LiftSet repr) => Alignable repr (Set a) where
  defaultBoundary = lam2 $ \v xs -> combineBoundaries defaultBoundary v (toAscList' xs)

instance (Diagrams repr style ann prim) => Alignable repr (Diagram repr style ann prim) where

alignByF :: Alignable repr b => repr (Vector repr Scalar) -> repr Scalar -> repr (Arr repr a b) -> repr (Arr repr a b)
alignByF v d f = lam $ \b -> alignBy v d (f %$ b)

alignByF'
  :: Alignable repr b
  => repr (Arr repr (Vector repr Scalar) (Arr repr b (Point repr Scalar)))
  -> repr (Vector repr Scalar)
  -> repr Scalar
  -> repr (Arr repr a b)
  -> repr (Arr repr a b)
alignByF' boundary v d f = lam $ \b -> alignBy' boundary v d (f %$ b)

snugBy
  :: (Alignable repr a, Traces repr, Traced repr a)
  => repr (Vector repr Scalar)
  -> repr Scalar
  -> repr a
  -> repr a
snugBy = alignBy' traceBoundary

snug
  :: (Alignable repr a, Traces repr, Traced repr a)
  => repr (Vector repr Scalar)
  -> repr a
  -> repr a
snug v = snugBy v 1

centerV
  :: Alignable repr a
  => repr (Vector repr Scalar)
  -> repr a
  -> repr a
centerV v = alignBy v 0

center
  :: Alignable repr a
  => repr a
  -> repr a
center = applyAll $ fmap' (lam2 centerV) basis

snugCenterV
  :: (Traces repr, Traced repr a, Alignable repr a)
  => repr (Vector repr Scalar)
  -> repr a
  -> repr a
snugCenterV v = alignBy' traceBoundary v 0

snugCenter
  :: (Traces repr, Traced repr a, Alignable repr a)
  => repr a
  -> repr a
snugCenter = applyAll $ fmap' (lam2 snugCenterV) basis

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Diagrams.Final.Space
  ( module Diagrams.Final.Space
  , module X
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Constraint
import Data.Functor.Product
import Linear hiding (basis)
import Linear.Affine (Affine(..))

import qualified Diagrams.Final.Sig.Space as T
import Diagrams.Final.Sig.Space as X (Scalar)

import Diagrams.Final.Base

class Functor' f repr => Additive' f repr where
  zero' :: Num' a repr => repr (f a)
  vadd' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  vmin' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  lerp' :: Num' a repr => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  default zero' :: (Num' a repr, f ~ Lift1 repr g, Additive g, Applicative repr) => repr (f a)
  zero' = pure (Lift1 (fmap unL zero))
  default vadd' :: (Num' a repr, f ~ Lift1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vadd' = liftA2 $ \(Lift1 x) (Lift1 y) -> Lift1 $ fmap unL $ fmap L x ^+^ fmap L y
  default vmin' :: (Num' a repr, f ~ Lift1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vmin' = liftA2 $ \(Lift1 x) (Lift1 y) -> Lift1 $ fmap unL $ fmap L x ^-^ fmap L y
  default lerp' :: (Num' a repr, f ~ Lift1 repr g, Additive g, Applicative repr) => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  lerp' rx = liftA2 $ \(Lift1 y) (Lift1 z) -> Lift1 $ fmap unL $ lerp (L rx) (fmap L y) (fmap L z)

instance Additive f => Additive' (Lift1 Identity f) Identity

class Additive' f repr => Metric' f repr where
  dot' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  quadrance' :: Num' a repr => repr (f a) -> repr a
  qd' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  distance' :: Floating' a repr => repr (f a) -> repr (f a) -> repr a
  norm' :: Floating' a repr => repr (f a) -> repr a
  signorm' :: Floating' a repr => repr (f a) -> repr (f a)
  default dot' :: (Num' a repr, f ~ Lift1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  dot' rx ry = join $ liftA2 (\(Lift1 x) (Lift1 y) -> unL $ dot (fmap L x) (fmap L y)) rx ry
  default quadrance' :: (Num' a repr, f ~ Lift1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  quadrance' = join . fmap (\(Lift1 x) -> unL $ quadrance (fmap L x))
  default qd' :: (Num' a repr, f ~ Lift1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  qd' rx ry = join $ liftA2 (\(Lift1 x) (Lift1 y) -> unL $ qd (fmap L x) (fmap L y)) rx ry
  default distance' :: (Floating' a repr, f ~ Lift1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  distance' rx ry = join $ liftA2 (\(Lift1 x) (Lift1 y) -> unL $ distance (fmap L x) (fmap L y)) rx ry
  default norm' :: (Floating' a repr, f ~ Lift1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  norm' = join . fmap (\(Lift1 x) -> unL $ norm $ fmap L x)
  default signorm' :: (Floating' a repr, f ~ Lift1 repr g, Metric g, Applicative repr) => repr (f a) -> repr (f a)
  signorm' = fmap (\(Lift1 x) -> Lift1 $ fmap unL $ signorm (fmap L x))

instance Metric f => Metric' (Lift1 Identity f) Identity

class Additive' (Diff' p repr) repr => Affine' p repr where
  type Diff' p repr :: * -> *
  pdiff' :: Num' a repr => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  padd' :: Num' a repr => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' :: Num' a repr => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  default pdiff' :: (Num' a repr, p ~ Lift1 repr g, Affine g, Functor g, Diff' p repr ~ Lift1 repr (Diff g), Applicative repr) => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  pdiff' = liftA2 $ \(Lift1 x) (Lift1 y) -> Lift1 $ fmap unL $ fmap L x .-. fmap L y
  default padd' :: (Num' a repr, p ~ Lift1 repr g, Affine g, Functor g, Diff' p repr ~ Lift1 repr (Diff g), Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  padd' = liftA2 $ \(Lift1 x) (Lift1 y) -> Lift1 $ fmap unL $ fmap L x .+^ fmap L y
  default pmin' :: (Num' a repr, p ~ Lift1 repr g, Affine g, Functor g, Diff' p repr ~ Lift1 repr (Diff g), Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' = liftA2 $ \(Lift1 x) (Lift1 y) -> Lift1 $ fmap unL $ fmap L x .-^ fmap L y

instance (Functor p, Affine p, Additive' (Diff' (Lift1 Identity p) Identity) Identity) => Affine' (Lift1 Identity p) Identity where
  type Diff' (Lift1 Identity p) Identity = Lift1 Identity (Diff p)

class NoConstraint x
instance NoConstraint x

class (LinearAction' n (Vector repr n) repr, AffineAction' n (Point repr n) repr) => SpatialClass repr n
instance (LinearAction' n (Vector repr n) repr, AffineAction' n (Point repr n) repr) => SpatialClass repr n

type SpatialConstraints repr =
   ( Lambda repr, Tuple2 repr, Tuple3 repr
   , Integral' Int repr
   , LiftMaybe repr, LiftList repr
   , Functor' (List' repr) repr, Foldable' (List' repr) repr
   , Num' Scalar repr, Floating' Scalar repr, Fractional' Scalar repr, Eq' Scalar repr, Ord' Scalar repr
   , Functor' (Vector repr) repr, Foldable' (Vector repr) repr, Additive' (Vector repr) repr
   , Metric' (Vector repr) repr, Affine' (Point repr) repr, Diff' (Point repr) repr ~ Vector repr
   , Semigroup' (LinearTransform repr Scalar) repr, Monoid' (LinearTransform repr Scalar) repr
   , Semigroup' (AffineTransform repr Scalar) repr, Monoid' (AffineTransform repr Scalar) repr
   )

class
  ( Representational repr
  , SpatialConstraints repr
  -- This should be a quantified constraint over n s.t. Num' n repr,
  -- but GHC doesn't like type families in quantified constraints
  , NumConstr repr Scalar
  , forall n. (NumConstr repr n, Num' n repr) => SpatialClass repr n
  ) => Spatial repr where
  type NumConstr repr :: * -> Constraint
  type NumConstr repr = NoConstraint
  type Vector repr :: * -> *
  type Vector repr = Lift1 repr T.Vector
  type Point repr :: * -> *
  type Point repr = Lift1 repr T.Point
  type LinearTransform repr :: * -> *
  type LinearTransform repr = Lift1 repr T.LinearTransform
  type AffineTransform repr :: * -> *
  type AffineTransform repr = Lift1 repr T.AffineTransform

  basis
    :: forall n. Num' n repr
    => repr (List' repr (Vector repr n))
  origin
    :: forall n. Num' n repr
    => repr (Point repr n)
  inverseLinear
    :: forall n. Num' n repr
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint
    :: forall n. Num' n repr
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  det
    :: forall n. Num' n repr
    => repr (LinearTransform repr n) -> repr n
  scalingBy
    :: forall n. Num' n repr
    => repr n -> repr (LinearTransform repr n)
  inverseAffine
    :: forall n. Num' n repr
    => repr (AffineTransform repr n) -> repr (AffineTransform repr n)
  translateBy
    :: forall n. Num' n repr
    => repr (Vector repr n) -> repr (AffineTransform repr n)
  linearOf
    :: forall n. Num' n repr
    => repr (AffineTransform repr n) -> repr (LinearTransform repr n)
  translationOf
    :: forall n. Num' n repr
    => repr (AffineTransform repr n) -> repr (Vector repr n)
  affineOf
    :: forall n. Num' n repr
    => repr (LinearTransform repr n) -> repr (Vector repr n) -> repr (AffineTransform repr n)
  default basis
    :: (Num' n repr, Applicative repr, List' repr ~ Lift1 repr [], Vector repr ~ Lift1 repr T.Vector)
    => repr (List' repr (Vector repr n))
  basis = pure $ Lift1 $ fmap (pure . Lift1 . fmap unL) $ T.basis
  default origin
    :: (Num' n repr, Applicative repr, Point repr ~ Lift1 repr T.Point)
    => repr (Point repr n)
  origin = pure $ Lift1 $ fmap unL $ T.origin
  default inverseLinear
    :: (Num' n repr, Applicative repr, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  inverseLinear = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ T.inverseLinear $ fmap L t
  default adjoint
    :: (Num' n repr, Applicative repr, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ T.adjoint $ fmap L t
  default det
    :: (Num' n repr, Monad repr, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr (LinearTransform repr n) -> repr n
  det = join . fmap (\(Lift1 t) -> unL $ T.det $ fmap L t)
  default scalingBy
    :: (Num' n repr, Applicative repr, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr n -> repr (LinearTransform repr n)
  scalingBy = pure . Lift1 . fmap unL . T.scalingBy . L
  default inverseAffine
    :: (Num' n repr, Applicative repr, AffineTransform repr ~ Lift1 repr T.AffineTransform)
    => repr (AffineTransform repr n) -> repr (AffineTransform repr n)
  inverseAffine = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ T.inverseAffine $ fmap L t
  default translateBy
    :: (Num' n repr, Applicative repr, Vector repr ~ Lift1 repr T.Vector, AffineTransform repr ~ Lift1 repr T.AffineTransform)
    => repr (Vector repr n) -> repr (AffineTransform repr n)
  translateBy = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ T.translateBy $ fmap L t
  default linearOf
    :: (Num' n repr, Applicative repr, AffineTransform repr ~ Lift1 repr T.AffineTransform, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr (AffineTransform repr n) -> repr (LinearTransform repr n)
  linearOf = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ view (T.relativeToOrigin . _1) $ fmap L t
  default translationOf
    :: (Num' n repr, Applicative repr, AffineTransform repr ~ Lift1 repr T.AffineTransform, Vector repr ~ Lift1 repr T.Vector)
    => repr (AffineTransform repr n) -> repr (Vector repr n)
  translationOf = fmap $ \(Lift1 t) -> Lift1 $ fmap unL $ view (T.relativeToOrigin . _2) $ fmap L t
  default affineOf
    :: (Num' n repr, Applicative repr, AffineTransform repr ~ Lift1 repr T.AffineTransform, Vector repr ~ Lift1 repr T.Vector, LinearTransform repr ~ Lift1 repr T.LinearTransform)
    => repr (LinearTransform repr n) -> repr (Vector repr n) -> repr (AffineTransform repr n)
  affineOf = liftA2 $ \(Lift1 l) (Lift1 v) -> Lift1 $ fmap unL $ view (from T.relativeToOrigin) $
    Pair (fmap L l) (fmap L v)

instance T.IsDiffOf T.Point T.Vector => Spatial Identity

-- Work around GHC #14860
withSpatial :: forall repr n r. (NumConstr repr n, Num' n repr, Spatial repr) => ((SpatialClass repr n) => r) -> r
withSpatial f = f

class LinearAction' n a repr | a -> n where
  actL' :: repr (LinearTransform repr n) -> repr a -> repr a
  default actL'
    :: forall g. (Num' n repr, Applicative repr, LinearTransform repr ~ Lift1 repr T.LinearTransform, a ~ Lift1 repr g n, Functor g, forall m. Num m => T.LinearAction m (g m))
    => repr (LinearTransform repr n) -> repr a -> repr a
  actL' = liftA2 $ \(Lift1 t) (Lift1 f) -> Lift1 $ fmap unL $ fmap L t `T.actL` fmap L f

instance (Num' n Identity, forall m. Num m => T.LinearAction m (f m), Functor f) => LinearAction' n (Lift1 Identity f n) Identity

class AffineAction' n a repr | a -> n where
  actA' :: repr (AffineTransform repr n) -> repr a -> repr a
  default actA'
    :: forall g. (Num' n repr, Applicative repr, AffineTransform repr ~ Lift1 repr T.AffineTransform, a ~ Lift1 repr g n, Functor g, forall m. Num m => T.AffineAction m (g m))
    => repr (AffineTransform repr n) -> repr a -> repr a
  actA' = liftA2 $ \(Lift1 t) (Lift1 f) -> Lift1 $ fmap unL $ fmap L t `T.actA` fmap L f

instance (Num' n Identity, forall m. Num m => T.AffineAction m (f m), Functor f) => AffineAction' n (Lift1 Identity f n) Identity

dimension :: forall repr. Spatial repr => repr Int
dimension = length' @(List' repr) $ basis @repr @Scalar

averageScale :: (Lambda repr, Spatial repr) => repr (LinearTransform repr Scalar) -> repr Scalar
averageScale t = abs' (det t) %/ fromIntegral' dimension

negated' :: (Lambda repr, Functor' f repr, Num' a repr) => repr (f a) -> repr (f a)
negated' = fmap' (lam negate')

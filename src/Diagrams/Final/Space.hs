{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Diagrams.Final.Space
  ( module Diagrams.Final.Space
  , module X
  ) where

import Control.Applicative
import Control.Lens
import Data.Coerce
import Data.Kind
import Linear hiding (basis)
import Linear.Affine (Affine(..))

import qualified Diagrams.Final.Sig.Space as T
import Diagrams.Final.Sig.Space as X (Scalar, Vector, Point, LinearTransform, LinearAction(..), AffineTransform, AffineAction(..))

import Diagrams.Final.Base

class (LiftNum repr, Functor' f repr, Additive f) => Additive' f repr where
  zero' :: Num' a repr => repr (f a)
  vadd' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  vmin' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  lerp' :: Num' a repr => repr a -> repr (f a) -> repr (f a) -> repr (f a)

instance (Applicative repr, Additive f) => Additive' f (ViaApplicative repr) where
  zero' = pure zero
  vadd' = liftA2 (^+^)
  vmin' = liftA2 (^-^)
  lerp' = liftA3 lerp

deriving via (ViaApplicative Identity) instance Additive f => Additive' f Identity

class (LiftFloating repr, Additive' f repr, Metric f) => Metric' f repr where
  dot' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  quadrance' :: Num' a repr => repr (f a) -> repr a
  qd' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  distance' :: Floating' a repr => repr (f a) -> repr (f a) -> repr a
  norm' :: Floating' a repr => repr (f a) -> repr a
  signorm' :: Floating' a repr => repr (f a) -> repr (f a)

instance (Applicative repr, Metric f) => Metric' f (ViaApplicative repr) where
  dot' = liftA2 dot
  quadrance' = fmap quadrance
  qd' = liftA2 qd
  distance' = liftA2 distance
  norm' = fmap norm
  signorm' = fmap signorm

deriving via (ViaApplicative Identity) instance Metric f => Metric' f Identity

class (LiftNum repr, Additive' (Diff p) repr, Affine p) => Affine' p repr where
  pdiff' :: Num' a repr => repr (p a) -> repr (p a) -> repr (Diff p a)
  padd' :: Num' a repr => repr (p a) -> repr (Diff p a) -> repr (p a)
  pmin' :: Num' a repr => repr (p a) -> repr (Diff p a) -> repr (p a)

instance (Applicative repr, Affine p) => Affine' p (ViaApplicative repr) where
  pdiff' = liftA2 (.-.)
  padd' = liftA2 (.+^)
  pmin' = liftA2 (.-^)

deriving via (ViaApplicative Identity) instance Affine f => Affine' f Identity

class LinearAction' a repr where
  actL' :: repr (LinearTransform Scalar) -> repr a -> repr a

instance (Applicative repr, T.LinearAction a) => LinearAction' a (ViaApplicative repr) where
  actL' = liftA2 actL

deriving via (ViaApplicative Identity) instance T.LinearAction a => LinearAction' a Identity

class AffineAction' a repr where
  actA' :: repr (AffineTransform Scalar) -> repr a -> repr a

instance (Applicative repr, AffineAction a) => AffineAction' a (ViaApplicative repr) where
  actA' = liftA2 T.actA

deriving via (ViaApplicative Identity) instance AffineAction a => AffineAction' a Identity

type Representational repr = (forall a b. Coercible a b => Coercible (repr a) (repr b)) :: Constraint

type SpatialConstraints repr =
   ( Apply repr, Compose repr
   , Integral' Int repr
   , Traversable' [] repr
   --
   , LiftSemigroup repr, LiftMonoid repr, LiftNum repr, LiftApplicative repr, LiftTraversable repr
   --
   , Num' Scalar repr, Floating' Scalar repr, Fractional' Scalar repr, Eq' Scalar repr, Ord' Scalar repr
   , Integral' Scalar repr
   , Functor' Vector repr, Foldable' Vector repr, Traversable' Vector repr, Additive' Vector repr
   , Metric' Vector repr, Affine' Point repr
   , Semigroup (repr (LinearTransform Scalar)), Monoid (repr (LinearTransform Scalar))
   , Semigroup (repr (AffineTransform Scalar)), Monoid (repr (AffineTransform Scalar))
   , LinearAction' (Vector Scalar) repr
   , AffineAction' (Point Scalar) repr
   )

class SpatialConstraints repr => Spatial repr where
  basis :: Traversable' t repr => repr (t (Vector Scalar))
  origin :: repr (Point Scalar)
  inverseLinear :: repr (LinearTransform Scalar) -> repr (LinearTransform Scalar)
  adjoint :: repr (LinearTransform Scalar) -> repr (LinearTransform Scalar)
  determinant :: repr (LinearTransform Scalar) -> repr Scalar
  scalingBy :: repr Scalar -> repr (LinearTransform Scalar)
  inverseAffine :: repr (AffineTransform Scalar) -> repr (AffineTransform Scalar)
  translateBy :: repr (Vector Scalar) -> repr (AffineTransform Scalar)
  linearOf :: repr (AffineTransform Scalar) -> repr (LinearTransform Scalar)
  translationOf :: repr (AffineTransform Scalar) -> repr (Vector Scalar)
  affineOf :: repr (LinearTransform Scalar) -> repr (Vector Scalar) -> repr (AffineTransform Scalar)

instance Applicative repr => Spatial (ViaApplicative repr) where
  basis = pure T.basis
  origin = pure T.origin
  inverseLinear = liftA T.inverseLinear
  adjoint = liftA T.adjoint
  determinant = liftA T.determinant
  scalingBy = liftA T.scalingBy
  inverseAffine = liftA T.inverseAffine
  translateBy = liftA T.translateBy
  linearOf = liftA T.linearOf
  translationOf = liftA T.translationOf
  affineOf = liftA2 T.affineOf

deriving via (ViaApplicative Identity) instance Spatial Identity

newtype ViaSpatial repr a = ViaSpatial { unViaSpatial :: repr a }

instance LinearAction' a repr => LinearAction' a (ViaSpatial repr) where
  actL' (ViaSpatial l) (ViaSpatial y) = ViaSpatial $ actL' l y

instance AffineAction' a repr => AffineAction' a (ViaSpatial repr) where
  actA' (ViaSpatial l) (ViaSpatial y) = ViaSpatial $ actA' l y

deriving via (repr m) instance Semigroup (repr m) => Semigroup (ViaSpatial repr m)
deriving via (repr :: * -> *) instance LiftSemigroup repr => LiftSemigroup (ViaSpatial repr)

deriving via (repr m) instance Monoid (repr m) => Monoid (ViaSpatial repr m)
deriving via (repr :: * -> *) instance LiftMonoid repr => LiftMonoid (ViaSpatial repr)

deriving via (repr a) instance Num (repr a) => Num (ViaSpatial repr a)
deriving via (repr :: * -> *) instance Num' a repr => Num' a (ViaSpatial repr)
deriving via (repr :: * -> *) instance LiftNum repr => LiftNum (ViaSpatial repr)

deriving via (repr :: * -> *) instance Floating' t repr => Floating' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance LiftFloating repr => LiftFloating (ViaSpatial repr)

deriving via (repr :: * -> *) instance Applicative' f repr => Applicative' f (ViaSpatial repr)
deriving via (repr :: * -> *) instance LiftApplicative repr => LiftApplicative (ViaSpatial repr)

deriving via (repr :: * -> *) instance (Traversable' t repr) => Traversable' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance (LiftTraversable repr) => LiftTraversable (ViaSpatial repr)

deriving via (repr :: * -> *) instance Apply repr => Apply (ViaSpatial repr)
deriving via (repr :: * -> *) instance Compose repr => Compose (ViaSpatial repr)
deriving via (repr :: * -> *) instance Lambda repr => Lambda (ViaSpatial repr)
deriving via (repr :: * -> *) instance Fractional' t repr => Fractional' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Enum' t repr => Enum' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Real' t repr => Real' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Integral' t repr => Integral' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Eq' t repr => Eq' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Ord' t repr => Ord' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance Functor' t repr => Functor' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance (Foldable' t repr) => Foldable' t (ViaSpatial repr)
deriving via (repr :: * -> *) instance (Additive' f repr) => Additive' f (ViaSpatial repr)
deriving via (repr :: * -> *) instance (Metric' f repr) => Metric' f (ViaSpatial repr)
deriving via (repr :: * -> *) instance (Affine' f repr) => Affine' f (ViaSpatial repr)

deriving via (repr :: * -> *) instance (Spatial repr) => Spatial (ViaSpatial repr)

dimension :: forall repr. Spatial repr => repr Int
dimension = length' @[] $ basis

averageScale :: (Lambda repr, Spatial repr) => repr (LinearTransform Scalar) -> repr Scalar
averageScale t = abs' (determinant t) %/ fromIntegral' dimension

negated' :: (Lambda repr, Functor' f repr, Num' a repr) => repr (f a) -> repr (f a)
negated' = fmap' (lam negate')

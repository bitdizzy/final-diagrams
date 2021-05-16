{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Core.Measure where

import Data.Functor.Identity

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Envelope
import Diagrams.Final.Core.Space

newtype LocalScale = LocalScale { unLocalScale :: Scalar }
newtype GlobalScale = GlobalScale { unGlobalScale :: Scalar }
newtype NormalizedScale = NormalizedScale { unNormalizedScale :: Scalar }

newtype DefaultScaled repr a = DefaultScaled
    { unDefaultScaled
        :: Arr repr (AffineTransform repr Scalar) (Arr repr GlobalScale (Arr repr NormalizedScale a))
    }

deriving instance (Functor repr, Functor (Arr repr (AffineTransform repr Scalar)), Functor (Arr repr GlobalScale), Functor (Arr repr NormalizedScale)) => Functor (DefaultScaled repr)

type Measure repr = Scaled repr Scalar

class (Scaled repr ~ scaled, Spatial' repr, forall a. AffineAction' Scalar (Scaled repr a) repr) => Scales scaled repr | repr -> scaled where
  type Scaled repr :: * -> *
  type Scaled repr = DefaultScaled repr
  toLocalScale :: repr Scalar -> repr LocalScale
  fromLocalScale :: repr LocalScale -> repr Scalar
  toGlobalScale :: repr Scalar -> repr GlobalScale
  fromGlobalScale :: repr GlobalScale -> repr Scalar
  toNormalizedScale :: repr Scalar -> repr NormalizedScale
  fromNormalizedScale :: repr NormalizedScale -> repr Scalar
  toScaled :: repr (Arr repr (AffineTransform repr Scalar) (Arr repr GlobalScale (Arr repr NormalizedScale a))) -> repr (Scaled repr a)
  fromScaled :: repr (Scaled repr a) -> repr (AffineTransform repr Scalar) -> repr GlobalScale -> repr NormalizedScale -> repr a
  default toLocalScale :: Functor repr => repr Scalar -> repr LocalScale
  toLocalScale = fmap LocalScale
  default fromLocalScale :: Functor repr => repr LocalScale -> repr Scalar
  fromLocalScale = fmap unLocalScale
  default toGlobalScale :: Functor repr => repr Scalar -> repr GlobalScale
  toGlobalScale = fmap GlobalScale
  default fromGlobalScale :: Functor repr => repr GlobalScale -> repr Scalar
  fromGlobalScale = fmap unGlobalScale
  default toNormalizedScale :: Functor repr => repr Scalar -> repr NormalizedScale
  toNormalizedScale = fmap NormalizedScale
  default fromNormalizedScale :: Functor repr => repr NormalizedScale -> repr Scalar
  fromNormalizedScale = fmap unNormalizedScale
  default toScaled :: (Functor repr, Scaled repr ~ DefaultScaled repr) => repr (Arr repr (AffineTransform repr Scalar) (Arr repr GlobalScale (Arr repr NormalizedScale a))) -> repr (Scaled repr a)
  toScaled = fmap DefaultScaled
  default fromScaled :: (Functor repr, Lambda' repr, Scaled repr ~ DefaultScaled repr) => repr (Scaled repr a) -> repr (AffineTransform repr Scalar) -> repr GlobalScale -> repr NormalizedScale -> repr a
  fromScaled rf rt rg rn = fmap unDefaultScaled rf %$ rt %$ rg %$ rn

type Scales' repr = Scales (Scaled repr) repr

instance Scales (DefaultScaled Identity) Identity

scaled'
  :: (Lambda' repr, Scales' repr)
  => repr (Arr repr (AffineTransform repr Scalar) (Arr repr (LocalScale) (Arr repr GlobalScale (Arr repr NormalizedScale a))))
  -> repr (Scaled repr a)
scaled' f = toScaled $ lam $ \t -> f %$ t $% toLocalScale (averageScale (linearOf t))

-- Go from (local, global, norm) -> a to Scaled a
scaled :: (Lambda' repr, Scales' repr) => repr (Arr repr Scalar (Arr repr Scalar (Arr repr Scalar a))) -> repr (Scaled repr a)
scaled f = toScaled $ lam $ \t -> lam $ \g -> lam $ \n -> f
  %$ (averageScale (linearOf t))
  %$ fromGlobalScale g
  %$ fromNormalizedScale n

instance (Lambda' repr, Scales' repr, Scaled repr ~ DefaultScaled repr) => AffineAction' Scalar (DefaultScaled repr a) repr where
  actA' t f = toScaled $ lam $ \t' -> lam $ \g -> lam $ \n -> fromScaled f (t' %<> t) g n

withScaleOf
  :: forall arr repr a. (Lambda' repr, Envelopes' repr, Scales' repr, LiftMaybe (Maybe' repr) repr, Tuple2 repr)
  => repr (Scaled repr a)
  -> repr (AffineTransform repr Scalar)
  -> repr (Envelope repr)
  -> repr a
withScaleOf f t e =
  let_ (averageScale (linearOf t)) $ \avgScale ->
    let_ (product' @(List' repr) (fmap' (lam $ \x -> diameter x e) basis) %** (1 %/ fromIntegral' dimension)) $ \normalScale ->
      fromScaled f t (toGlobalScale avgScale) (toNormalizedScale normalScale)

atLeast :: forall arr repr a b c d. (Lambda arr repr, Spatial' repr, Ord' d repr) => repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d)))
atLeast m1 m2 = curry3' $ liftA2' (lam $ \x -> lam $ max' x) (uncurry3' m1) (uncurry3' m2)

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Diagrams.Final.Measure
  ( LocalScale(..)
  , GlobalScale(..)
  , NormalizedScale(..)
  , Scaled(..)
  , Scales(..)
  , scaled
  , withScaleOf
  ) where

import Data.Functor.Identity

import Diagrams.Final.Base
import Diagrams.Final.Envelope
import Diagrams.Final.Space

newtype LocalScale = LocalScale { unLocalScale :: Scalar }
newtype GlobalScale = GlobalScale { unGlobalScale :: Scalar }
newtype NormalizedScale = NormalizedScale { unNormalizedScale :: Scalar }

newtype Scaled a = Scaled
    { unScaled
        :: AffineTransform Scalar
        -> GlobalScale
        -> NormalizedScale
        -> a
    }
  deriving (Functor)

class Spatial repr => Scales repr where
  toLocalScale :: repr Scalar -> repr LocalScale
  fromLocalScale :: repr LocalScale -> repr Scalar
  toGlobalScale :: repr Scalar -> repr GlobalScale
  fromGlobalScale :: repr GlobalScale -> repr Scalar
  toNormalizedScale :: repr Scalar -> repr NormalizedScale
  fromNormalizedScale :: repr NormalizedScale -> repr Scalar
  toScaled :: repr (AffineTransform Scalar -> GlobalScale -> NormalizedScale -> a) -> repr (Scaled a)
  fromScaled :: repr (Scaled a) -> repr (AffineTransform Scalar) -> repr GlobalScale -> repr NormalizedScale -> repr a

instance Applicative repr => Scales (ViaApplicative repr) where
  toLocalScale = fmap LocalScale
  fromLocalScale = fmap unLocalScale
  toGlobalScale = fmap GlobalScale
  fromGlobalScale = fmap unGlobalScale
  toNormalizedScale = fmap NormalizedScale
  fromNormalizedScale = fmap unNormalizedScale
  toScaled = fmap Scaled
  fromScaled f t g n = unScaled <$> f <*> t <*> g <*> n

deriving via (ViaApplicative Identity) instance Scales Identity
deriving via (repr :: * -> *) instance Scales repr => Scales (ViaSpatial repr)

scaled
  :: (Lambda repr, Scales repr)
  => repr (AffineTransform Scalar -> LocalScale -> GlobalScale -> NormalizedScale -> a)
  -> repr (Scaled a)
scaled f = toScaled $ lam $ \t -> f %$ t $% toLocalScale (averageScale (linearOf t))

instance (Lambda repr, Scales repr) => AffineAction' (Scaled a) repr where
  actA' t f = toScaled $ lam $ \t' -> lam $ \g -> lam $ \n -> fromScaled f (t' <> t) g n

withScaleOf
  :: (Lambda repr, Envelopes repr, Scales repr, Maybe' repr, Tuple2 repr)
  => repr (Scaled a)
  -> repr (AffineTransform Scalar)
  -> repr Envelope
  -> repr a
withScaleOf f t e =
  let_ (averageScale (linearOf t)) $ \avgScale ->
    let_ (product' @[] (fmap' (lam $ \x -> diameter x e) basis) %** (1 %/ fromIntegral' dimension)) $ \normalScale ->
      fromScaled f t (toGlobalScale avgScale) (toNormalizedScale normalScale)

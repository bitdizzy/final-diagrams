{-# LANGUAGE BlockArguments #-}
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

newtype Scaled repr a = Scaled
    { unScaled
        :: Arr repr (AffineTransform repr Scalar) (Arr repr GlobalScale (Arr repr NormalizedScale a))
    }

deriving instance (Functor repr, Functor (Arr repr (AffineTransform repr Scalar)), Functor (Arr repr GlobalScale), Functor (Arr repr NormalizedScale)) => Functor (Scaled repr)

type Measure repr = Scaled repr Scalar

class (Spatial repr, forall a. AffineAction' repr Scalar (Scaled repr a)) => Scales repr where
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
  default toScaled :: (Functor repr) => repr (Arr repr (AffineTransform repr Scalar) (Arr repr GlobalScale (Arr repr NormalizedScale a))) -> repr (Scaled repr a)
  toScaled = fmap Scaled
  default fromScaled :: (Functor repr) => repr (Scaled repr a) -> repr (AffineTransform repr Scalar) -> repr GlobalScale -> repr NormalizedScale -> repr a
  fromScaled rf rt rg rn = fmap unScaled rf %$ rt %$ rg %$ rn

instance Scales Identity

instance Scales repr => Functor' repr (Scaled repr) where
  fmap' f = toScaled . (\k -> lam3 \x y z -> f %$ k x y z) . fromScaled

instance Scales repr => Applicative' repr (Scaled repr) where
  pure' x = toScaled $ lam3 \_ _ _ -> x
  ap' sf sx = toScaled $ lam3 \x y z -> fromScaled sf x y z %$ fromScaled sx x y z

scaled'
  :: (Scales repr)
  => repr (Arr repr (AffineTransform repr Scalar) (Arr repr (LocalScale) (Arr repr GlobalScale (Arr repr NormalizedScale a))))
  -> repr (Scaled repr a)
scaled' f = toScaled $ lam $ \t -> f %$ t $% toLocalScale (averageScale (linearOf t))

-- Go from (local, global, norm) -> a to Scaled a
scaled :: (Scales repr) => repr (Arr repr Scalar (Arr repr Scalar (Arr repr Scalar a))) -> repr (Scaled repr a)
scaled f = toScaled $ lam $ \t -> lam $ \g -> lam $ \n -> f
  %$ (averageScale (linearOf t))
  %$ fromGlobalScale g
  %$ fromNormalizedScale n

instance (Scales repr) => AffineAction' repr Scalar (Scaled repr a) where
  actA' t f = toScaled $ lam $ \t' -> lam $ \g -> lam $ \n -> fromScaled f (t' %<> t) g n

instance (Scales repr, Juxtapose repr a) => Juxtapose repr (Scaled repr a) where
  juxtapose v a b = toScaled $ lam \t -> lam \g -> lam \n -> juxtapose v (fromScaled a t g n) (fromScaled b t g n)

withScaleOf
  :: forall repr a. (Envelopes repr, Scales repr)
  => repr (Scaled repr a)
  -> repr (AffineTransform repr Scalar)
  -> repr (Envelope repr)
  -> repr a
withScaleOf f t e =
  let_ (averageScale (linearOf t)) $ \avgScale ->
    let_ (product' @repr @(List' repr) (fmap' (lam $ \x -> diameter x e) basis) %** (1 %/ fromIntegral' dimension)) $ \normalScale ->
      fromScaled f t (toGlobalScale avgScale) (toNormalizedScale normalScale)

output :: Scales repr => repr a -> repr (Scaled repr a)
output x = scaled $ lam3 \_ _ _ -> x

local :: Scales repr => repr Scalar -> repr (Scaled repr Scalar)
local x = scaled $ lam3 \l _ _ -> l %* x

global :: Scales repr => repr Scalar -> repr (Scaled repr Scalar)
global x = scaled $ lam3 \_ g _ -> g %* x

normalized :: Scales repr => repr Scalar -> repr (Scaled repr Scalar)
normalized x = scaled $ lam3 \_ _ n -> n %* x

atLeast :: forall repr a b c d. (Spatial repr, Ord' repr d) => repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d)))
atLeast m1 m2 = curry3' $ liftA2' (lam $ \x -> lam $ max' x) (uncurry3' m1) (uncurry3' m2)

atMost :: forall repr a b c d. (Spatial repr, Ord' repr d) => repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr a (Arr repr b (Arr repr c d)))
atMost m1 m2 = curry3' $ liftA2' (lam $ \x -> lam $ min' x) (uncurry3' m1) (uncurry3' m2)

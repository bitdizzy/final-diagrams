{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Diagrams.Final.Core.Space.Primitive where

import Control.Lens
import Data.Constraint
import Data.Distributive
import Data.Functor.Product
import Data.Functor.Rep
import Linear
import qualified Linear as L
import Linear.Affine hiding (Point, Vector)

type Scalar = Double
type Vector = V2

basis :: forall n. Num n => [Vector n]
basis = L.basis

type Point = Homogeneous
newtype Homogeneous a = H (V2 a)
  deriving (Functor, Applicative, Foldable, Traversable, Representable, Additive)

instance Distributive Homogeneous where
  distribute f = H $ V2 (fmap (\(H (V2 x _)) -> x) f) (fmap (\(H (V2 _ y)) -> y) f)

instance Affine Homogeneous where
  type Diff Homogeneous = V2
  (H p1) .-. (H p0) = (p1 - p0) ^. _xy
  (H p0) .+^ v = H $ p0 & _xy %~ (+v)

class Diff p ~ v => IsDiffOf p v
instance IsDiffOf Point Vector

instance Wrapped (Homogeneous a) where
  type Unwrapped (Homogeneous a) = V2 a
  _Wrapped' = iso (\(H x) -> x) H

instance Rewrapped (Homogeneous a) (Homogeneous a')

origin :: forall n. Num n => Point n
origin = H $ V2 0 0

vectorIsDiffPoint :: Dict (Diff Point ~ Vector)
vectorIsDiffPoint = Dict

newtype LinearTransform a = LinearTransform { unLinearTransform :: M22 a }
  deriving (Functor, Foldable, Traversable)

instance Num n => Semigroup (LinearTransform n) where
  (<>) = over _Wrapped' . (!*!) . view _Wrapped'

instance Num n => Monoid (LinearTransform n) where
  mempty = LinearTransform identity


adjoint :: forall n. (Conjugate n, Num n) => LinearTransform n -> LinearTransform n
adjoint = over _Wrapped' L.adjoint

inverseLinear :: forall n. (Fractional n, Num n) => LinearTransform n -> LinearTransform n
inverseLinear = over _Wrapped' L.inv22

det :: forall n. Num n => LinearTransform n -> n
det = L.det22 . unLinearTransform

scalingBy :: forall n. Num n => n -> LinearTransform n
scalingBy s = Wrapped $ V2 (V2 s 0) (V2 0 s)

instance Wrapped (LinearTransform a) where
  type Unwrapped (LinearTransform a) = M22 a
  _Wrapped' = iso unLinearTransform LinearTransform

instance Rewrapped (LinearTransform a) (LinearTransform a')

newtype AffineTransform a = AffineTransform { unAffineTransform :: M33 a }
  deriving (Functor, Foldable, Traversable)

instance Num n => Semigroup (AffineTransform n) where
  (<>) = over _Wrapped' . (!*!) . view _Wrapped'

instance Num n => Monoid (AffineTransform n) where
  mempty = AffineTransform identity

instance Wrapped (AffineTransform a) where
  type Unwrapped (AffineTransform a) = M33 a
  _Wrapped' = iso unAffineTransform AffineTransform

instance Rewrapped (AffineTransform a) (AffineTransform a)

translateBy :: forall n. Num n => Vector n -> AffineTransform n
translateBy (V2 x y) = Wrapped $ V3 zero zero (V3 x y 1)

inverseAffine :: forall n. (Fractional n, Num n) => AffineTransform n -> AffineTransform n
inverseAffine m =
  let Pair l t = m ^. relativeToOrigin
      l_inv = inverseLinear l
      t_inv = actL l_inv t
   in (Pair l_inv t_inv) ^. from relativeToOrigin

class LinearAction n a | a -> n where
  actL :: LinearTransform n -> a -> a

instance Num n => LinearAction n (Vector n) where
  actL = (!*) . view _Wrapped

class AffineAction n a | a -> n where
  actA :: AffineTransform n -> a -> a

instance Num n => AffineAction n (Point n) where
  actA = over _Wrapped . (\m (V2 x y) -> view _xy $ m !* (V3 x y 1)) . view _Wrapped

class RelativeTo n a b | a -> n b where
  relativeTo :: Point n -> Iso' a b
  relativeToOrigin :: Iso' a b

instance Num n => RelativeTo n (Point n) (Vector n) where
  relativeTo p0 = iso (.-. p0) (p0 .+^)
  relativeToOrigin = _Wrapped

instance Num n => RelativeTo n (AffineTransform n) (Product LinearTransform Vector n) where
  relativeTo p = iso comprise compose
   where
    comprise m =
      let Pair l t0 = m ^. relativeToOrigin
       in Pair l (actL l (p ^. relativeToOrigin) + t0)
    compose (Pair l v) = (Pair l (v - actL l (p ^. relativeToOrigin))) ^. from relativeToOrigin
  relativeToOrigin = _Wrapped' . iso comprise compose
   where
    comprise m =
      let l = m ^. _m22
          t = m ^. _z . _xy
       in Pair (LinearTransform l) t
    compose (Pair (LinearTransform l) (V2 x y)) = zero & _m22 .~ l & _z .~ V3 x y 1


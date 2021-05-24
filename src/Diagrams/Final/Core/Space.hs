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
{-# OPTIONS_GHC -Wno-orphans #-}
module Diagrams.Final.Core.Space
  ( module Diagrams.Final.Core.Space
  , module X
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Functor.Product
import Data.Set (Set)
import Linear hiding (basis)
import Linear.Affine (Affine(..))
import Data.Kind

import qualified Diagrams.Final.Core.Space.Primitive as T
import Diagrams.Final.Core.Space.Primitive as X (Scalar)

import Diagrams.Final.Core.Base

class Num' a repr => Conjugate' a repr where
  conjugate' :: repr a -> repr a
  default conjugate' :: (Conjugate a, Functor repr) => repr a -> repr a
  conjugate' = fmap conjugate

instance Conjugate' a repr => Conjugate (L repr a) where
  conjugate (L x) = L $ conjugate' x

instance Conjugate a => Conjugate' a Identity

class Functor' f repr => Additive' f repr where
  zero' :: Num' a repr => repr (f a)
  vadd' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  vmin' :: Num' a repr => repr (f a) -> repr (f a) -> repr (f a)
  lerp' :: Num' a repr => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  default zero' :: (Num' a repr, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a)
  zero' = pure (T1 (fmap unL zero))
  default vadd' :: (Num' a repr, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vadd' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x ^+^ fmap L y
  default vmin' :: (Num' a repr, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vmin' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x ^-^ fmap L y
  default lerp' :: (Num' a repr, f ~ T1 repr g, Additive g, Applicative repr) => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  lerp' rx = liftA2 $ \(T1 y) (T1 z) -> T1 $ fmap unL $ lerp (L rx) (fmap L y) (fmap L z)

instance Additive f => Additive' (T1 Identity f) Identity

class Additive' f repr => Metric' f repr where
  dot' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  quadrance' :: Num' a repr => repr (f a) -> repr a
  qd' :: Num' a repr => repr (f a) -> repr (f a) -> repr a
  distance' :: Floating' a repr => repr (f a) -> repr (f a) -> repr a
  norm' :: Floating' a repr => repr (f a) -> repr a
  signorm' :: Floating' a repr => repr (f a) -> repr (f a)
  default dot' :: (Num' a repr, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  dot' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ dot (fmap L x) (fmap L y)) rx ry
  default quadrance' :: (Num' a repr, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  quadrance' = join . fmap (\(T1 x) -> unL $ quadrance (fmap L x))
  default qd' :: (Num' a repr, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  qd' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ qd (fmap L x) (fmap L y)) rx ry
  default distance' :: (Floating' a repr, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  distance' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ distance (fmap L x) (fmap L y)) rx ry
  default norm' :: (Floating' a repr, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  norm' = join . fmap (\(T1 x) -> unL $ norm $ fmap L x)
  default signorm' :: (Floating' a repr, f ~ T1 repr g, Metric g, Applicative repr) => repr (f a) -> repr (f a)
  signorm' = fmap (\(T1 x) -> T1 $ fmap unL $ signorm (fmap L x))

infixl 7 %*^
infixl 7 %^*
infixl 7 %^/

(%*^) :: (Num' a repr, Functor' f repr) => repr a -> repr (f a) -> repr (f a)
(%*^) a = fmap' (lam (a %*))

(%^*) :: (Num' a repr, Functor' f repr) => repr (f a) -> repr a -> repr (f a)
(%^*) f a = fmap' (lam (%* a)) f

(%^/) :: (Fractional' a repr, Functor' f repr) => repr (f a) -> repr a -> repr (f a)
(%^/) f a = fmap' (lam (%/ a)) f

infixl 6 %^+^
infixl 6 %^-^

(%^+^) :: (Num' a repr, Additive' f repr) => repr (f a) -> repr (f a) -> repr (f a)
(%^+^) = vadd'

(%^-^) :: (Num' a repr, Additive' f repr) => repr (f a) -> repr (f a) -> repr (f a)
(%^-^) = vmin'

instance Metric f => Metric' (T1 Identity f) Identity

type family Diff' p repr :: * -> * where
  Diff' (T1 repr p) repr = T1 repr (Diff p)

class (Additive' (Diff' p repr) repr) => Affine' p repr where
  pdiff' :: Num' a repr => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  padd' :: Num' a repr => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' :: Num' a repr => repr (p a) -> repr (Diff' p repr a) -> repr (p a)

  default pdiff' :: (Num' a repr, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  pdiff' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .-. fmap L y
  default padd' :: (Num' a repr, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  padd' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .+^ fmap L y
  default pmin' :: (Num' a repr, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .-^ fmap L y

infixl 6 %.-.
infixl 6 %.+^
infixl 6 %.-^

(%.-.) :: (Affine' p repr, Num' a repr) => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
(%.-.) = pdiff'

(%.+^) :: (Affine' p repr, Num' a repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
(%.+^) = padd'

(%.-^) :: (Affine' p repr, Num' a repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
(%.-^) = pmin'

instance Affine' (T1 Identity T.Point) Identity where

type SpatialConstraints repr =
   ( Tuple2 repr, Tuple3 repr
   , Integral' Int repr
   , LiftBool repr
   , LiftMaybe repr, LiftList repr, LiftSet repr, LiftMax repr, LiftEndo repr
   , Val Scalar repr
   , Val1 T.Vector repr, Val1 T.Point repr, Val1 T.LinearTransform repr, Val1 T.AffineTransform repr
   , LiftRepresentable T.Vector repr, LiftRepresentable T.Point repr
   , Functor' (List' repr) repr, Foldable' (List' repr) repr
   , Conjugate' Scalar repr, Num' Scalar repr, Floating' Scalar repr, Fractional' Scalar repr, RealFrac' Scalar repr, Eq' Scalar repr, Ord' Scalar repr
   , Functor' (Vector repr) repr, Foldable' (Vector repr) repr, Additive' (Vector repr) repr, Additive' (Point repr) repr
   , Metric' (Vector repr) repr, Affine' (Point repr) repr, Diff' (Point repr) repr ~ Vector repr
   , Semigroup' (LinearTransform repr Scalar) repr, Monoid' (LinearTransform repr Scalar) repr
   , Semigroup' (AffineTransform repr Scalar) repr, Monoid' (AffineTransform repr Scalar) repr
   )

type Vector repr = T1 repr T.Vector
type Point repr = T1 repr T.Point
type LinearTransform repr = T1 repr T.LinearTransform
type AffineTransform repr = T1 repr T.AffineTransform

class
  ( SpatialConstraints repr
  , forall n. (NumConstraint repr n, Num' n repr) => LinearAction' n (Vector repr n) repr
  , forall n. (NumConstraint repr n, Num' n repr) => AffineAction' n (Point repr n) repr
  , NumConstraint repr Scalar
  ) => Spatial repr where
  type NumConstraint repr :: * -> Constraint
  type NumConstraint repr = Num
  basis
    :: forall n. Num' n repr
    => repr (List' repr (Vector repr n))
  origin
    :: forall n. Num' n repr
    => repr (Point repr n)
  inverseLinear
    :: forall n. (Fractional' n repr, Num' n repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint
    :: forall n. (Num' n repr, Conjugate' n repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  det
    :: forall n. Num' n repr
    => repr (LinearTransform repr n) -> repr n
  scalingBy
    :: forall n. Num' n repr
    => repr n -> repr (LinearTransform repr n)
  inverseAffine
    :: forall n. (Fractional' n repr, Num' n repr)
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
    :: (Num' n repr, Applicative repr)
    => repr (List' repr (Vector repr n))
  basis = pure $ T1 $ fmap (pure . T1 . fmap unL) $ T.basis
  default origin
    :: (Num' n repr, Applicative repr)
    => repr (Point repr n)
  origin = pure $ T1 $ fmap unL $ T.origin
  default inverseLinear
    :: (Fractional' n repr, Num' n repr, Applicative repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  inverseLinear = fmap $ \(T1 t) -> T1 $ fmap unL $ T.inverseLinear $ fmap L t
  default adjoint
    :: (Conjugate' n repr, Num' n repr, Applicative repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint = fmap $ \(T1 t) -> T1 $ fmap unL $ T.adjoint $ fmap L t
  default det
    :: (Num' n repr, Monad repr)
    => repr (LinearTransform repr n) -> repr n
  det = join . fmap (\(T1 t) -> unL $ T.det $ fmap L t)
  default scalingBy
    :: (Num' n repr, Applicative repr)
    => repr n -> repr (LinearTransform repr n)
  scalingBy = pure . T1 . fmap unL . T.scalingBy . L
  default inverseAffine
    :: (Fractional' n repr, Num' n repr, Applicative repr)
    => repr (AffineTransform repr n) -> repr (AffineTransform repr n)
  inverseAffine = fmap $ \(T1 t) -> T1 $ fmap unL $ T.inverseAffine $ fmap L t
  default translateBy
    :: (Num' n repr, Applicative repr) => repr (Vector repr n) -> repr (AffineTransform repr n)
  translateBy = fmap $ \(T1 t) -> T1 $ fmap unL $ T.translateBy $ fmap L t
  default linearOf
    :: (Num' n repr, Applicative repr) => repr (AffineTransform repr n) -> repr (LinearTransform repr n)
  linearOf = fmap $ \(T1 t) -> T1 $ fmap unL $ view (T.relativeToOrigin . _1) $ fmap L t
  default translationOf
    :: (Num' n repr, Applicative repr) => repr (AffineTransform repr n) -> repr (Vector repr n)
  translationOf = fmap $ \(T1 t) -> T1 $ fmap unL $ view (T.relativeToOrigin . _2) $ fmap L t
  default affineOf
    :: (Num' n repr, Applicative repr) => repr (LinearTransform repr n) -> repr (Vector repr n) -> repr (AffineTransform repr n)
  affineOf = liftA2 $ \(T1 l) (T1 v) -> T1 $ fmap unL $ view (from T.relativeToOrigin) $
    Pair (fmap L l) (fmap L v)

relativeF :: (Spatial repr, Num' n repr) => repr (Point repr n) -> (repr (Vector repr n) -> repr (Vector repr n)) -> repr (Point repr n) -> repr (Point repr n)
relativeF p f = (p %.+^) . f . (%.-. p)

aff :: (Spatial repr, Num' n repr) => repr (LinearTransform repr n) -> repr (AffineTransform repr n)
aff l = affineOf l zero'

moveTo :: (Spatial repr, Num' n repr, AffineAction' n a repr) => repr (Point repr n) -> repr a -> repr a
moveTo p = actA' (translateBy (p %.-. origin))

moveOriginTo :: (Spatial repr, Num' n repr, AffineAction' n a repr) => repr (Point repr n) -> repr a -> repr a
moveOriginTo p = actA' (translateBy (origin %.-. p))

moveOriginBy :: (Spatial repr, Num' n repr, AffineAction' n a repr) => repr (Vector repr n) -> repr a -> repr a
moveOriginBy v = actA' (translateBy (negated' v))

instance Semigroup' (LinearTransform Identity Scalar) Identity
instance Monoid' (LinearTransform Identity Scalar) Identity
instance Semigroup' (AffineTransform Identity Scalar) Identity
instance Monoid' (AffineTransform Identity Scalar) Identity

instance T.IsDiffOf T.Point T.Vector => Spatial Identity

class LinearAction' n a repr | a -> n where
  actL' :: repr (LinearTransform repr n) -> repr a -> repr a
  default actL'
    :: forall g. (Num' n repr, Applicative repr, a ~ T1 repr g n, Functor g, forall m. Num m => T.LinearAction m (g m))
    => repr (LinearTransform repr n) -> repr a -> repr a
  actL' = liftA2 $ \(T1 t) (T1 f) -> T1 $ fmap unL $ fmap L t `T.actL` fmap L f

instance (Num' n Identity, forall m. Num m => T.LinearAction m (f m), Functor f) => LinearAction' n (T1 Identity f n) Identity

class AffineAction' n a repr | a -> n where
  actA' :: repr (AffineTransform repr n) -> repr a -> repr a
  default actA'
    :: forall g. (Num' n repr, Applicative repr, a ~ T1 repr g n, Functor g, forall m. Num m => T.AffineAction m (g m))
    => repr (AffineTransform repr n) -> repr a -> repr a
  actA' = liftA2 $ \(T1 t) (T1 f) -> T1 $ fmap unL $ fmap L t `T.actA` fmap L f

instance (Num' n Identity, forall m. Num m => T.AffineAction m (f m), Functor f) => AffineAction' n (T1 Identity f n) Identity

instance (Tuple2 repr, AffineAction' n a repr, AffineAction' n b repr) => AffineAction' n (a, b) repr where
  actA' f ab = tup2' (actA' f (pi1' ab)) (actA' f (pi2' ab))

instance (LiftList repr, AffineAction' n a repr) => AffineAction' n (List' repr a) repr where
  actA' f = fmap' $ lam $ actA' f

instance (LiftSet repr, Ord' a repr, AffineAction' n a repr) => AffineAction' n (Set a) repr where
  actA' f = fromList' . actA' f . toAscList'

dimension :: forall repr. Spatial repr => repr Int
dimension = length' @(List' repr) $ basis @repr @Scalar

averageScale :: (Lambda repr, Spatial repr) => repr (LinearTransform repr Scalar) -> repr Scalar
averageScale t = abs' (det t) %/ fromIntegral' dimension

negated' :: (Lambda repr, Functor' f repr, Num' a repr) => repr (f a) -> repr (f a)
negated' = fmap' (lam negate')

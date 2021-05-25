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

class Num' repr a => Conjugate' repr a where
  conjugate' :: repr a -> repr a
  default conjugate' :: (Conjugate a, Functor repr) => repr a -> repr a
  conjugate' = fmap conjugate

instance Conjugate' repr a => Conjugate (L repr a) where
  conjugate (L x) = L $ conjugate' x

instance Conjugate a => Conjugate' Identity a

class Functor' repr f => Additive' repr f where
  zero' :: Num' repr a => repr (f a)
  vadd' :: Num' repr a => repr (f a) -> repr (f a) -> repr (f a)
  vmin' :: Num' repr a => repr (f a) -> repr (f a) -> repr (f a)
  lerp' :: Num' repr a => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  default zero' :: (Num' repr a, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a)
  zero' = pure (T1 (fmap unL zero))
  default vadd' :: (Num' repr a, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vadd' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x ^+^ fmap L y
  default vmin' :: (Num' repr a, f ~ T1 repr g, Additive g, Applicative repr) => repr (f a) -> repr (f a) -> repr (f a)
  vmin' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x ^-^ fmap L y
  default lerp' :: (Num' repr a, f ~ T1 repr g, Additive g, Applicative repr) => repr a -> repr (f a) -> repr (f a) -> repr (f a)
  lerp' rx = liftA2 $ \(T1 y) (T1 z) -> T1 $ fmap unL $ lerp (L rx) (fmap L y) (fmap L z)

instance Additive f => Additive' Identity (T1 Identity f)

class Additive' repr f => Metric' repr f where
  dot' :: Num' repr a => repr (f a) -> repr (f a) -> repr a
  quadrance' :: Num' repr a => repr (f a) -> repr a
  qd' :: Num' repr a => repr (f a) -> repr (f a) -> repr a
  distance' :: Floating' repr a => repr (f a) -> repr (f a) -> repr a
  norm' :: Floating' repr a => repr (f a) -> repr a
  signorm' :: Floating' repr a => repr (f a) -> repr (f a)
  default dot' :: (Num' repr a, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  dot' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ dot (fmap L x) (fmap L y)) rx ry
  default quadrance' :: (Num' repr a, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  quadrance' = join . fmap (\(T1 x) -> unL $ quadrance (fmap L x))
  default qd' :: (Num' repr a, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  qd' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ qd (fmap L x) (fmap L y)) rx ry
  default distance' :: (Floating' repr a, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr (f a) -> repr a
  distance' rx ry = join $ liftA2 (\(T1 x) (T1 y) -> unL $ distance (fmap L x) (fmap L y)) rx ry
  default norm' :: (Floating' repr a, f ~ T1 repr g, Metric g, Monad repr) => repr (f a) -> repr a
  norm' = join . fmap (\(T1 x) -> unL $ norm $ fmap L x)
  default signorm' :: (Floating' repr a, f ~ T1 repr g, Metric g, Applicative repr) => repr (f a) -> repr (f a)
  signorm' = fmap (\(T1 x) -> T1 $ fmap unL $ signorm (fmap L x))

infixl 7 %*^
infixl 7 %^*
infixl 7 %^/

(%*^) :: (Num' repr a, Functor' repr f) => repr a -> repr (f a) -> repr (f a)
(%*^) a = fmap' (lam (a %*))

(%^*) :: (Num' repr a, Functor' repr f) => repr (f a) -> repr a -> repr (f a)
(%^*) f a = fmap' (lam (%* a)) f

(%^/) :: (Fractional' repr a, Functor' repr f) => repr (f a) -> repr a -> repr (f a)
(%^/) f a = fmap' (lam (%/ a)) f

infixl 6 %^+^
infixl 6 %^-^

(%^+^) :: (Num' repr a, Additive' repr f) => repr (f a) -> repr (f a) -> repr (f a)
(%^+^) = vadd'

(%^-^) :: (Num' repr a, Additive' repr f) => repr (f a) -> repr (f a) -> repr (f a)
(%^-^) = vmin'

instance Metric f => Metric' Identity (T1 Identity f)

type family Diff' p repr :: * -> * where
  Diff' (T1 repr p) repr = T1 repr (Diff p)

class (Additive' repr (Diff' p repr)) => Affine' repr p where
  pdiff' :: Num' repr a => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  padd' :: Num' repr a => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' :: Num' repr a => repr (p a) -> repr (Diff' p repr a) -> repr (p a)

  default pdiff' :: (Num' repr a, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
  pdiff' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .-. fmap L y
  default padd' :: (Num' repr a, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  padd' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .+^ fmap L y
  default pmin' :: (Num' repr a, p ~ T1 repr g, Affine g, Functor g, Applicative repr) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
  pmin' = liftA2 $ \(T1 x) (T1 y) -> T1 $ fmap unL $ fmap L x .-^ fmap L y

infixl 6 %.-.
infixl 6 %.+^
infixl 6 %.-^

(%.-.) :: (Affine' repr p, Num' repr a) => repr (p a) -> repr (p a) -> repr (Diff' p repr a)
(%.-.) = pdiff'

(%.+^) :: (Affine' repr p, Num' repr a) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
(%.+^) = padd'

(%.-^) :: (Affine' repr p, Num' repr a) => repr (p a) -> repr (Diff' p repr a) -> repr (p a)
(%.-^) = pmin'

instance Affine' Identity (T1 Identity T.Point) where

type SpatialConstraints repr =
   ( Tuple2 repr, Tuple3 repr
   , Integral' repr Int
   , LiftBool repr
   , LiftMaybe repr, LiftList repr, LiftSet repr, LiftMax repr, LiftEndo repr
   , Val repr Scalar
   , Val1 repr T.Vector, Val1 repr T.Point, Val1 repr T.LinearTransform, Val1 repr T.AffineTransform
   , LiftRepresentable repr T.Vector, LiftRepresentable repr T.Point
   , Functor' repr (List' repr), Foldable' repr (List' repr)
   , Conjugate' repr Scalar, Num' repr Scalar, Floating' repr Scalar, Fractional' repr Scalar, RealFrac' repr Scalar, Eq' repr Scalar, Ord' repr Scalar
   , Functor' repr (Vector repr), Foldable' repr (Vector repr), Additive' repr (Vector repr), Additive' repr (Point repr)
   , Metric' repr (Vector repr), Affine' repr (Point repr), Diff' (Point repr) repr ~ Vector repr
   , Semigroup' repr (LinearTransform repr Scalar), Monoid' repr (LinearTransform repr Scalar)
   , Semigroup' repr (AffineTransform repr Scalar), Monoid' repr (AffineTransform repr Scalar)
   )

type Vector repr = T1 repr T.Vector
type Point repr = T1 repr T.Point
type LinearTransform repr = T1 repr T.LinearTransform
type AffineTransform repr = T1 repr T.AffineTransform

class
  ( SpatialConstraints repr
  , forall n. (NumConstraint repr n, Num' repr n) => LinearAction' repr n (Vector repr n)
  , forall n. (NumConstraint repr n, Num' repr n) => AffineAction' repr n (Point repr n)
  , NumConstraint repr Scalar
  ) => Spatial repr where
  type NumConstraint repr :: * -> Constraint
  type NumConstraint repr = Num
  basis
    :: forall n. Num' repr n
    => repr (List' repr (Vector repr n))
  origin
    :: forall n. Num' repr n
    => repr (Point repr n)
  inverseLinear
    :: forall n. (Fractional' repr n, Num' repr n)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint
    :: forall n. (Num' repr n, Conjugate' repr n)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  det
    :: forall n. Num' repr n
    => repr (LinearTransform repr n) -> repr n
  scalingBy
    :: forall n. Num' repr n
    => repr n -> repr (LinearTransform repr n)
  inverseAffine
    :: forall n. (Fractional' repr n, Num' repr n)
    => repr (AffineTransform repr n) -> repr (AffineTransform repr n)
  translateBy
    :: forall n. Num' repr n
    => repr (Vector repr n) -> repr (AffineTransform repr n)
  linearOf
    :: forall n. Num' repr n
    => repr (AffineTransform repr n) -> repr (LinearTransform repr n)
  translationOf
    :: forall n. Num' repr n
    => repr (AffineTransform repr n) -> repr (Vector repr n)
  affineOf
    :: forall n. Num' repr n
    => repr (LinearTransform repr n) -> repr (Vector repr n) -> repr (AffineTransform repr n)
  default basis
    :: (Num' repr n, Applicative repr)
    => repr (List' repr (Vector repr n))
  basis = pure $ T1 $ fmap (pure . T1 . fmap unL) $ T.basis
  default origin
    :: (Num' repr n, Applicative repr)
    => repr (Point repr n)
  origin = pure $ T1 $ fmap unL $ T.origin
  default inverseLinear
    :: (Fractional' repr n, Num' repr n, Applicative repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  inverseLinear = fmap $ \(T1 t) -> T1 $ fmap unL $ T.inverseLinear $ fmap L t
  default adjoint
    :: (Conjugate' repr n, Num' repr n, Applicative repr)
    => repr (LinearTransform repr n) -> repr (LinearTransform repr n)
  adjoint = fmap $ \(T1 t) -> T1 $ fmap unL $ T.adjoint $ fmap L t
  default det
    :: (Num' repr n, Monad repr)
    => repr (LinearTransform repr n) -> repr n
  det = join . fmap (\(T1 t) -> unL $ T.det $ fmap L t)
  default scalingBy
    :: (Num' repr n, Applicative repr)
    => repr n -> repr (LinearTransform repr n)
  scalingBy = pure . T1 . fmap unL . T.scalingBy . L
  default inverseAffine
    :: (Fractional' repr n, Num' repr n, Applicative repr)
    => repr (AffineTransform repr n) -> repr (AffineTransform repr n)
  inverseAffine = fmap $ \(T1 t) -> T1 $ fmap unL $ T.inverseAffine $ fmap L t
  default translateBy
    :: (Num' repr n, Applicative repr) => repr (Vector repr n) -> repr (AffineTransform repr n)
  translateBy = fmap $ \(T1 t) -> T1 $ fmap unL $ T.translateBy $ fmap L t
  default linearOf
    :: (Num' repr n, Applicative repr) => repr (AffineTransform repr n) -> repr (LinearTransform repr n)
  linearOf = fmap $ \(T1 t) -> T1 $ fmap unL $ view (T.relativeToOrigin . _1) $ fmap L t
  default translationOf
    :: (Num' repr n, Applicative repr) => repr (AffineTransform repr n) -> repr (Vector repr n)
  translationOf = fmap $ \(T1 t) -> T1 $ fmap unL $ view (T.relativeToOrigin . _2) $ fmap L t
  default affineOf
    :: (Num' repr n, Applicative repr) => repr (LinearTransform repr n) -> repr (Vector repr n) -> repr (AffineTransform repr n)
  affineOf = liftA2 $ \(T1 l) (T1 v) -> T1 $ fmap unL $ view (from T.relativeToOrigin) $
    Pair (fmap L l) (fmap L v)

relativeF :: (Spatial repr, Num' repr n) => repr (Point repr n) -> (repr (Vector repr n) -> repr (Vector repr n)) -> repr (Point repr n) -> repr (Point repr n)
relativeF p f = (p %.+^) . f . (%.-. p)

aff :: (Spatial repr, Num' repr n) => repr (LinearTransform repr n) -> repr (AffineTransform repr n)
aff l = affineOf l zero'

moveTo :: (Spatial repr, Num' repr n, AffineAction' repr n a) => repr (Point repr n) -> repr a -> repr a
moveTo p = actA' (translateBy (p %.-. origin))

moveOriginTo :: (Spatial repr, Num' repr n, AffineAction' repr n a) => repr (Point repr n) -> repr a -> repr a
moveOriginTo p = actA' (translateBy (origin %.-. p))

moveOriginBy :: (Spatial repr, Num' repr n, AffineAction' repr n a) => repr (Vector repr n) -> repr a -> repr a
moveOriginBy v = actA' (translateBy (negated' v))

instance Semigroup' Identity (LinearTransform Identity Scalar)
instance Monoid' Identity (LinearTransform Identity Scalar)
instance Semigroup' Identity (AffineTransform Identity Scalar)
instance Monoid' Identity (AffineTransform Identity Scalar)

instance T.IsDiffOf T.Point T.Vector => Spatial Identity

class LinearAction' repr n a | a -> n where
  actL' :: repr (LinearTransform repr n) -> repr a -> repr a
  default actL'
    :: forall g. (Num' repr n, Applicative repr, a ~ T1 repr g n, Functor g, forall m. Num m => T.LinearAction m (g m))
    => repr (LinearTransform repr n) -> repr a -> repr a
  actL' = liftA2 $ \(T1 t) (T1 f) -> T1 $ fmap unL $ fmap L t `T.actL` fmap L f

instance (Num' Identity n, forall m. Num m => T.LinearAction m (f m), Functor f) => LinearAction' Identity n (T1 Identity f n)

class AffineAction' repr n a | a -> n where
  actA' :: repr (AffineTransform repr n) -> repr a -> repr a
  default actA'
    :: forall g. (Num' repr n, Applicative repr, a ~ T1 repr g n, Functor g, forall m. Num m => T.AffineAction m (g m))
    => repr (AffineTransform repr n) -> repr a -> repr a
  actA' = liftA2 $ \(T1 t) (T1 f) -> T1 $ fmap unL $ fmap L t `T.actA` fmap L f

instance (Num' Identity n, forall m. Num m => T.AffineAction m (f m), Functor f) => AffineAction' Identity n (T1 Identity f n)

instance (Tuple2 repr, AffineAction' repr n a, AffineAction' repr n b) => AffineAction' repr n (a, b) where
  actA' f ab = tup2' (actA' f (pi1' ab)) (actA' f (pi2' ab))

instance (LiftList repr, AffineAction' repr n a) => AffineAction' repr n (List' repr a) where
  actA' f = fmap' $ lam $ actA' f

instance (LiftSet repr, Ord' repr a, AffineAction' repr n a) => AffineAction' repr n (Set a) where
  actA' f = fromList' . actA' f . toAscList'

dimension :: forall repr. Spatial repr => repr Int
dimension = length' @repr @(List' repr) $ basis @repr @Scalar

averageScale :: (Lambda repr, Spatial repr) => repr (LinearTransform repr Scalar) -> repr Scalar
averageScale t = abs' (det t) %/ fromIntegral' dimension

negated' :: (Lambda repr, Functor' repr f, Num' repr a) => repr (f a) -> repr (f a)
negated' = fmap' (lam negate')

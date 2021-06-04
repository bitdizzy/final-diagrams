{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Diagrams.Final.Angle where

import Linear

import Diagrams.Final.Core

newtype Angle n = Angle { unAngle :: n }
  deriving (Eq, Ord, Functor)

instance Applicative Angle where
  pure = Angle
  Angle f <*> Angle x = Angle (f x)

instance Additive Angle where
  zero = pure 0

instance Num n => Semigroup (Angle n) where
  (<>) = (^+^)

instance Num n => Monoid (Angle n) where
  mappend = (<>)
  mempty = zero

--

class LiftAngle repr where
  rad' :: repr n -> repr (Angle n)
  fromRad' :: repr (Angle n) -> repr n
  default rad' :: Functor repr => repr n -> repr (Angle n)
  rad' = fmap Angle
  default fromRad' :: Functor repr => repr (Angle n) -> repr n
  fromRad' = fmap unAngle

turn :: (LiftAngle repr, Floating' repr n) => repr n -> repr (Angle n)
turn = rad' . (%* (num 2 %* pi'))

fromTurn :: (LiftAngle repr, Floating' repr n) => repr (Angle n) -> repr n
fromTurn = (%/ (num 2 %* pi')) . fromRad'

degrees :: (LiftAngle repr, Floating' repr n) => repr n -> repr (Angle n)
degrees = rad' . (%* (num 2 %* pi' %/ num 360))

fromDegrees :: (LiftAngle repr, Floating' repr n) => repr (Angle n) -> repr n
fromDegrees = (%/ (num 2 %* pi' %/ num 360)) . fromRad'

fullTurn :: (LiftAngle repr, Floating' repr n) => repr (Angle n)
fullTurn = turn (num 1)

halfTurn :: (LiftAngle repr, Floating' repr n) => repr (Angle n)
halfTurn = turn (fnum 0.5)

quarterTurn :: (LiftAngle repr, Floating' repr n) => repr (Angle n)
quarterTurn = turn (fnum 0.25)

angleBetween :: (LiftAngle repr, Metric' repr f, Floating' repr a, Ord' repr a) => repr (f a) -> repr (f a) -> repr (Angle a)
angleBetween v1 v2 = rad' . acos' . min' (num 1) . max' (num (-1)) $ signorm' v1 `dot'` signorm' v2

normalizeAngle :: (LiftAngle repr, RealFrac' repr n, Floating' repr n) => repr (Angle n) -> repr (Angle n)
normalizeAngle = rad' . (`modF'` (fnum 2 %*pi')) . fromRad'

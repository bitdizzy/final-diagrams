{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Diagrams.Final.Angle where

import Control.Lens
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

turn :: (LiftAngle repr, Floating' n repr) => repr n -> repr (Angle n)
turn = rad' . (%* (2*pi))

fromTurn :: (LiftAngle repr, Floating' n repr) => repr (Angle n) -> repr n
fromTurn = (%/ (2*pi)) . fromRad'

degrees :: (LiftAngle repr, Floating' n repr) => repr n -> repr (Angle n)
degrees = rad' . (%* (2*pi/360))

fromDegrees :: (LiftAngle repr, Floating' n repr) => repr (Angle n) -> repr n
fromDegrees = (%/ (2*pi/360)) . fromRad'

fullTurn :: (LiftAngle repr, Floating' n repr) => repr (Angle n)
fullTurn = turn 1

halfTurn :: (LiftAngle repr, Floating' n repr) => repr (Angle n)
halfTurn = turn 0.5

quarterTurn :: (LiftAngle repr, Floating' n repr) => repr (Angle n)
quarterTurn = turn 0.25

angleBetween :: (LiftAngle repr, Metric' f repr, Floating' a repr, Ord' a repr) => repr (f a) -> repr (f a) -> repr (Angle a)
angleBetween v1 v2 = rad' . acos' . min' 1 . max' (-1) $ signorm' v1 `dot'` signorm' v2

normalizeAngle :: (LiftAngle repr, RealFrac' n repr, Floating' n repr) => repr (Angle n) -> repr (Angle n)
normalizeAngle = rad' . (`modF'` (2*pi)) . fromRad'

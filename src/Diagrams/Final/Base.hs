{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Diagrams.Final.Base where

import Control.Applicative
import Data.Functor.Identity

newtype ViaApplicative repr a = ViaApplicative { unViaApplicative :: repr a }
  deriving (Functor, Applicative, Monad) via repr

class Apply repr where
  app :: repr (a -> b) -> repr a -> repr b

instance Applicative repr => Apply (ViaApplicative repr) where
  app = (<*>)

deriving via (ViaApplicative Identity) instance Apply Identity

infixl 1 %$
(%$) :: Apply repr => repr (a -> b) -> repr a -> repr b
(%$) = app

infixr 0 $%
($%) :: Apply repr => repr (a -> b) -> repr a -> repr b
($%) = app

infixr 9 %.
class Compose repr where
  (%.) :: repr (b -> c) -> repr (a -> b) -> repr (a -> c)

instance Applicative repr => Compose (ViaApplicative repr) where
  (%.) = liftA2 (.)

deriving via (ViaApplicative Identity) instance Compose Identity

class Lambda repr where
  let_ :: repr a -> (repr a -> repr b) -> repr b
  lam :: (repr a -> repr b) -> repr (a -> b)

instance Lambda Identity where
  let_ = flip ($)
  lam f = Identity $ runIdentity . f . Identity

class Fst x y repr | x -> y where
  fst' :: repr x -> repr y

instance Applicative repr => Fst (a, b) a (ViaApplicative repr) where
  fst' = fmap fst

deriving via (ViaApplicative Identity) instance Fst (a, b) a Identity

class Snd x y repr | x -> y where
  snd' :: repr x -> repr y

instance Applicative repr => Snd (a, b) b (ViaApplicative repr) where
  snd' = fmap snd

deriving via (ViaApplicative Identity) instance Snd (a, b) b Identity

class (forall a b. Fst (a, b) a repr, forall a b. Snd (a, b) b repr) => Tuple2 repr where
  tup2' :: repr a -> repr b -> repr (a, b)

instance Applicative repr => Tuple2 (ViaApplicative repr) where
  tup2' = liftA2 (,)

class Applicative' Maybe repr => Maybe' repr where
  nothing' :: repr (Maybe a)
  just' :: repr a -> repr (Maybe a)
  maybe' :: repr a -> repr (b -> a) -> repr (Maybe b) -> repr a

instance Applicative repr => Maybe' (ViaApplicative repr) where
  nothing' = pure Nothing
  just' = fmap Just
  maybe' = liftA3 maybe

deriving via (ViaApplicative Identity) instance Maybe' Identity

class Eq a => Eq' a repr where
  eq' :: repr a -> repr a -> repr Bool
  neq' :: repr a -> repr a -> repr Bool

infix 4 %==
(%==) :: Eq' a repr => repr a -> repr a -> repr Bool
(%==) = eq'

infix 4 %/=
(%/=) :: Eq' a repr => repr a -> repr a -> repr Bool
(%/=) = neq'

instance (Applicative repr, Eq a) => Eq' a (ViaApplicative repr) where
  eq' = liftA2 (==)
  neq' = liftA2 (/=)

deriving via (ViaApplicative Identity) instance Eq a => Eq' a Identity

class (Eq' a repr, Ord a) => Ord' a repr where
  compare' :: repr a -> repr a -> repr Ordering
  lt' :: repr a -> repr a -> repr Bool
  lte' :: repr a -> repr a -> repr Bool
  gt' :: repr a -> repr a -> repr Bool
  gte' :: repr a -> repr a -> repr Bool
  max' :: repr a -> repr a -> repr a
  min' :: repr a -> repr a -> repr a

infix 4 %<
(%<) :: Ord' a repr => repr a -> repr a -> repr Bool
(%<) = lt'

infix 4 %<=
(%<=) :: Ord' a repr => repr a -> repr a -> repr Bool
(%<=) = lte'

infix 4 %>
(%>) :: Ord' a repr => repr a -> repr a -> repr Bool
(%>) = gt'

infix 4 %>=
(%>=) :: Ord' a repr => repr a -> repr a -> repr Bool
(%>=) = gte'

instance (Applicative repr, Ord a) => Ord' a (ViaApplicative repr) where
  compare' = liftA2 compare
  lt' = liftA2 (<)
  lte' = liftA2 (<=)
  gt' = liftA2 (>)
  gte' = liftA2 (>=)
  max' = liftA2 max
  min' = liftA2 min

deriving via (ViaApplicative Identity) instance Ord a => Ord' a Identity

class (Num a, Num (repr a)) => Num' a repr where
  plus' :: repr a -> repr a -> repr a
  minus' :: repr a -> repr a -> repr a
  times' :: repr a -> repr a -> repr a
  negate' :: repr a -> repr a
  abs' :: repr a -> repr a
  signum' :: repr a -> repr a
  fromInteger' :: repr Integer -> repr a

infixl 6 %+
(%+) :: Num' a repr => repr a -> repr a -> repr a
(%+) = plus'

infixl 6 %-
(%-) :: Num' a repr => repr a -> repr a -> repr a
(%-) = minus'

infixl 7 %*
(%*) :: Num' a repr => repr a -> repr a -> repr a
(%*) = times'

instance (Applicative repr, Num a) => Num' a (ViaApplicative repr) where
  plus' = liftA2 (+)
  minus' = liftA2 (-)
  times' = liftA2 (*)
  negate' = fmap negate
  abs' = fmap abs
  signum' = fmap signum
  fromInteger' = fmap fromInteger

instance (Applicative repr, Num a) => Num (ViaApplicative repr a) where
  (+) = plus'
  (-) = minus'
  (*) = times'
  negate = negate'
  abs = abs'
  signum = signum'
  fromInteger = pure . fromInteger

deriving via (ViaApplicative Identity) instance Num a => Num' a Identity

class (forall a. Num a => Num' a repr) => LiftNum repr

instance Applicative repr => LiftNum (ViaApplicative repr)
deriving via (ViaApplicative Identity) instance LiftNum Identity

class (Num' a repr, Fractional a) => Fractional' a repr where
  fdiv' :: repr a -> repr a -> repr a
  recip' :: repr a -> repr a
  fromRational' :: repr Rational -> repr a

infixl 7 %/
(%/) :: Fractional' a repr => repr a -> repr a -> repr a
(%/) = fdiv'

instance (Applicative repr, Fractional a) => Fractional' a (ViaApplicative repr) where
  fdiv' = liftA2 (/)
  recip' = fmap recip
  fromRational' = fmap fromRational

deriving via (ViaApplicative Identity) instance Fractional a => Fractional' a Identity

class (Fractional' a repr, Floating a) => Floating' a repr where
  pi' :: repr a
  exp' :: repr a -> repr a
  log' :: repr a -> repr a
  sqrt' :: repr a -> repr a
  exponent' :: repr a -> repr a -> repr a
  logBase' :: repr a -> repr a -> repr a
  sin' :: repr a -> repr a
  cos' :: repr a -> repr a
  tan' :: repr a -> repr a
  asin' :: repr a -> repr a
  acos' :: repr a -> repr a
  atan' :: repr a -> repr a
  sinh' :: repr a -> repr a
  cosh' :: repr a -> repr a
  tanh' :: repr a -> repr a
  asinh' :: repr a -> repr a
  acosh' :: repr a -> repr a
  atanh' :: repr a -> repr a

instance (Applicative repr, Floating a) => Floating' a (ViaApplicative repr) where
  pi' = pure pi
  exp' = fmap exp
  log' = fmap log
  sqrt' = fmap sqrt
  exponent' = liftA2 (**)
  logBase' = liftA2 logBase
  sin' = fmap sin
  cos' = fmap cos
  tan' = fmap tan
  asin' = fmap asin
  acos' = fmap acos
  atan' = fmap atan
  sinh' = fmap sinh
  cosh' = fmap cosh
  tanh' = fmap tanh
  asinh' = fmap asinh
  acosh' = fmap acosh
  atanh' = fmap atanh

infixr 8 %**
(%**) :: Floating' a repr => repr a -> repr a -> repr a
(%**) = exponent'

deriving via (ViaApplicative Identity) instance Floating a => Floating' a Identity

class (forall a. Floating a => Floating' a repr) => LiftFloating repr

instance Applicative repr => LiftFloating (ViaApplicative repr)
deriving via (ViaApplicative Identity) instance LiftFloating Identity

class (Num' a repr, Ord' a repr, Real a) => Real' a repr where
  toRational' :: repr a -> repr Rational

instance (Applicative repr, Real a) => Real' a (ViaApplicative repr) where
  toRational' = fmap toRational

deriving via (ViaApplicative Identity) instance Real a => Real' a Identity

class Enum a => Enum' a repr where
  succ' :: repr a -> repr a
  pred' :: repr a -> repr a
  toEnum' :: repr Int -> repr a
  fromEnum' :: repr a -> repr Int
  enumFrom' :: repr a -> repr [a]
  enumFromThen' :: repr a -> repr a -> repr [a]
  enumFromTo' :: repr a -> repr a -> repr [a]
  enumFromThenTo' :: repr a -> repr a -> repr a -> repr [a]

instance (Applicative repr, Enum a) => Enum' a (ViaApplicative repr) where
  succ' = fmap succ
  pred' = fmap pred
  toEnum' = fmap toEnum
  fromEnum' = fmap fromEnum
  enumFrom' = fmap enumFrom
  enumFromThen' = liftA2 enumFromThen
  enumFromTo' = liftA2 enumFromTo
  enumFromThenTo' = liftA3 enumFromThenTo

deriving via (ViaApplicative Identity) instance Enum a => Enum' a Identity

class (Real' a repr, Enum' a repr, Integral a) => Integral' a repr where
  quot' :: repr a -> repr a -> repr a
  rem' :: repr a -> repr a -> repr a
  div' :: repr a -> repr a -> repr a
  mod' :: repr a -> repr a -> repr a
  quotRem' :: repr a -> repr a -> repr (a,a)
  divMod' :: repr a -> repr a -> repr (a,a)
  toInteger' :: repr a -> repr Integer

instance (Applicative repr, Integral a) => Integral' a (ViaApplicative repr) where
  quot' = liftA2 quot
  rem' = liftA2 rem
  div' = liftA2 div
  mod' = liftA2 mod
  quotRem' = liftA2 quotRem
  divMod' = liftA2 divMod
  toInteger' = fmap toInteger

deriving via (ViaApplicative Identity) instance Integral a => Integral' a Identity

fromIntegral' :: (Compose repr, Integral' a repr, Num' b repr) => repr a -> repr b
fromIntegral' = fromInteger' . toInteger'

class (forall m. Semigroup m => Semigroup (repr m)) => LiftSemigroup repr

instance (Applicative repr, Semigroup a) => Semigroup (ViaApplicative repr a) where
  (<>) = liftA2 (<>)

instance Applicative repr => LiftSemigroup (ViaApplicative repr)

deriving via (ViaApplicative Identity) instance LiftSemigroup Identity

class (forall m. Monoid m => Monoid (repr m)) => LiftMonoid repr

instance (Applicative repr, Monoid a) => Monoid (ViaApplicative repr a) where
  mempty = pure mempty

instance Applicative repr => LiftMonoid (ViaApplicative repr)

deriving via (ViaApplicative Identity) instance LiftMonoid Identity

class Functor f => Functor' f repr where
  fmap' :: repr (a -> b) -> repr (f a) -> repr (f b)

instance (Applicative repr, Functor f) => Functor' f (ViaApplicative repr) where
  fmap' = liftA2 fmap

deriving via (ViaApplicative Identity) instance Functor f => Functor' f Identity

class (Functor' f repr, Applicative f) => Applicative' f repr where
  pure' :: repr a -> repr (f a)
  ap' :: repr (f (a -> b)) -> repr (f a) -> repr (f b)

instance (Applicative repr, Applicative f) => Applicative' f (ViaApplicative repr) where
  pure' = fmap pure
  ap' = liftA2 (<*>)

deriving via (ViaApplicative Identity) instance Applicative f => Applicative' f Identity

class (forall f. Applicative f => Applicative' f repr) => LiftApplicative repr

instance Applicative repr => LiftApplicative (ViaApplicative repr)

deriving via (ViaApplicative Identity) instance LiftApplicative Identity

class (LiftMonoid repr, LiftNum repr, Foldable t) => Foldable' t repr where
  foldMap' :: Monoid m => repr (a -> m) -> repr (t a) -> repr m
  length' :: repr (t a) -> repr Int
  product' :: Num' a repr => repr (t a) -> repr a

instance (Applicative repr, Foldable t) => Foldable' t (ViaApplicative repr) where
  foldMap' = liftA2 foldMap
  length' = fmap length
  product' = fmap product

deriving via (ViaApplicative Identity) instance Foldable f => Foldable' f Identity

class (Foldable' t repr, Functor' t repr, LiftApplicative repr, Traversable t) => Traversable' t repr where
  traverse' :: Applicative' f repr => repr (a -> f b) -> repr (t a) -> repr (f (t b))

instance (Applicative repr, Traversable t) => Traversable' t (ViaApplicative repr) where
  traverse' = liftA2 traverse

deriving via (ViaApplicative Identity) instance Traversable f => Traversable' f Identity

class (forall t. Traversable t => Traversable' t repr) => LiftTraversable repr

instance Applicative repr => LiftTraversable (ViaApplicative repr)

deriving via (ViaApplicative Identity) instance LiftTraversable Identity

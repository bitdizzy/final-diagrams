{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Diagrams.Final.Core.Base where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

--
-- HOAS
--
type Arr repr = T2 repr (->)

class (forall a. Applicative' (Arr repr a) repr) => Lambda repr where
  app :: repr (Arr repr a b) -> repr a -> repr b
  lam :: (repr a -> repr b) -> repr (Arr repr a b)
  default app :: Monad repr => repr (Arr repr a b) -> repr a -> repr b
  app f y = f >>= ($ y) . unT2
  default lam :: Applicative repr => (repr a -> repr b) -> repr (Arr repr a b)
  lam = pure . T2

instance Lambda Identity where

id' :: Lambda repr => repr (Arr repr a a)
id' = lam id

let_ :: Lambda repr => repr a -> (repr a -> repr b) -> repr b
let_ x f = lam f `app` x

uncurry' :: (Tuple2 repr, Lambda repr) => repr (Arr repr a (Arr repr b c)) -> repr (Arr repr (a,b) c)
uncurry' f = lam $ \xy -> f %$ pi1' xy %$ pi2' xy

curry' :: (Tuple2 repr, Lambda repr) => repr (Arr repr (a,b) c) -> repr (Arr repr a (Arr repr b c))
curry' f = lam $ \x -> lam $ \y -> f %$ tup2' x y

uncurry3' :: (Tuple3 repr, Lambda repr) => repr (Arr repr a (Arr repr b (Arr repr c d))) -> repr (Arr repr (a,b,c) d)
uncurry3' f = lam $ \t -> f %$ pi1' t %$ pi2' t %$ pi3' t

curry3' :: (Tuple3 repr, Lambda repr) => repr (Arr repr (a,b,c) d) -> repr (Arr repr a (Arr repr b (Arr repr c d)))
curry3' f = lam $ \x -> lam $ \y -> lam $ \z -> f %$ tup3' x y z

infixl 1 %$
(%$) :: Lambda repr => repr (Arr repr a b) -> repr a -> repr b
(%$) = app

infixr 0 $%
($%) :: Lambda repr => repr (Arr repr a b) -> repr a -> repr b
($%) = app

infixr 9 %.
(%.) :: Lambda repr => repr (Arr repr b c) -> repr (Arr repr a b) -> repr (Arr repr a c)
f %. g = lam $ \x -> f $% g $% x

--
-- Tuples
--
class Proj1 x y repr | x -> y where
  pi1' :: repr x -> repr y
  default pi1' :: (Field1 x x y y, Functor repr) => repr x -> repr y
  pi1' = fmap (view _1)

instance Proj1 (a, b) a Identity
instance Proj1 (a, b, c) a Identity

class Proj2 x y repr | x -> y where
  pi2' :: repr x -> repr y
  default pi2' :: (Field2 x x y y, Functor repr) => repr x -> repr y
  pi2' = fmap (view _2)

instance Proj2 (a, b) b Identity
instance Proj2 (a, b, c) b Identity

class Proj3 x y repr | x -> y where
  pi3' :: repr x -> repr y
  default pi3' :: (Field3 x x y y, Functor repr) => repr x -> repr y
  pi3' = fmap (view _3)

instance Proj3 (a, b, c) c Identity

class (forall a b. Proj1 (a, b) a repr, forall a b. Proj2 (a, b) b repr) => Tuple2 repr where
  tup2' :: repr a -> repr b -> repr (a, b)
  default tup2' :: Applicative repr => repr a -> repr b -> repr (a, b)
  tup2' = liftA2 (,)

instance Tuple2 Identity

class (forall a b c. Proj1 (a, b, c) a repr, forall a b c. Proj2 (a, b, c) b repr, forall a b c. Proj3 (a, b, c) c repr) => Tuple3 repr where
  tup3' :: repr a -> repr b -> repr c -> repr (a, b, c)
  default tup3' :: Applicative repr => repr a -> repr b -> repr c -> repr (a, b, c)
  tup3' = liftA3 (,,)

instance Tuple3 Identity

--
-- Prelude
--

class Eq a => Eq' a repr where
  eq' :: repr a -> repr a -> repr Bool
  neq' :: repr a -> repr a -> repr Bool
  default eq' :: Applicative repr => repr a -> repr a -> repr Bool
  eq' = liftA2 (==)
  default neq' :: Applicative repr => repr a -> repr a -> repr Bool
  neq' = liftA2 (/=)

instance Eq a => Eq' a Identity

infix 4 %==
(%==) :: Eq' a repr => repr a -> repr a -> repr Bool
(%==) = eq'

infix 4 %/=
(%/=) :: Eq' a repr => repr a -> repr a -> repr Bool
(%/=) = neq'

class (Eq' a repr, Ord a) => Ord' a repr where
  compare' :: repr a -> repr a -> repr Ordering
  lt' :: repr a -> repr a -> repr Bool
  lte' :: repr a -> repr a -> repr Bool
  gt' :: repr a -> repr a -> repr Bool
  gte' :: repr a -> repr a -> repr Bool
  max' :: repr a -> repr a -> repr a
  min' :: repr a -> repr a -> repr a
  default compare' :: Applicative repr => repr a -> repr a -> repr Ordering
  compare' = liftA2 compare
  default lt' :: Applicative repr => repr a -> repr a -> repr Bool
  lt' = liftA2 (<)
  default lte' :: Applicative repr => repr a -> repr a -> repr Bool
  lte' = liftA2 (<=)
  default gt' :: Applicative repr => repr a -> repr a -> repr Bool
  gt' = liftA2 (>)
  default gte' :: Applicative repr => repr a -> repr a -> repr Bool
  gte' = liftA2 (>=)
  default max' :: Applicative repr => repr a -> repr a -> repr a
  max' = liftA2 max
  default min' :: Applicative repr => repr a -> repr a -> repr a
  min' = liftA2 min

instance Ord a => Ord' a Identity

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

infixr 6 %<>

newtype L repr a = L { unL :: repr a }

instance Semigroup' a repr => Semigroup (L repr a) where
  L a <> L b = L $ a %<> b

instance Monoid' a repr => Monoid (L repr a) where
  mempty = L mempty'

instance Num' a repr => Num (L repr a) where
  L a + L b = L $ a %+ b
  L a - L b = L $ a %- b
  L a * L b = L $ a %* b
  negate (L a) = L $ negate' a
  abs (L a) = L $ abs' a
  signum (L a) = L $ signum' a
  fromInteger = L . fromInteger

instance (Applicative repr, Fractional' a repr) => Fractional (L repr a) where
  fromRational = L . fromRational' . pure
  recip = L . recip' . unL

instance (Applicative repr, Floating' a repr) => Floating (L repr a) where
  pi = L pi'
  exp (L x) = L $ exp' x
  log (L x) = L $ log' x
  sin (L x) = L $ sin' x
  cos (L x) = L $ cos' x
  asin (L x) = L $ asin' x
  acos (L x) = L $ acos' x
  atan (L x) = L $ atan' x
  sinh (L x) = L $ sinh' x
  cosh (L x) = L $ cosh' x
  tanh (L x) = L $ tanh' x
  asinh (L x) = L $ asinh' x
  acosh (L x) = L $ acosh' x
  atanh (L x) = L $ atanh' x

class Semigroup' a repr where
  (%<>) :: repr a -> repr a -> repr a
  default (%<>) :: (Semigroup a, Applicative repr) => repr a -> repr a -> repr a
  (%<>) = liftA2 (<>)

class Semigroup' a repr => Monoid' a repr where
  mempty' :: repr a
  default mempty' :: (Monoid a, Applicative repr) => repr a
  mempty' = pure mempty

class Num (repr a) => Num' a repr where
  plus' :: repr a -> repr a -> repr a
  minus' :: repr a -> repr a -> repr a
  times' :: repr a -> repr a -> repr a
  negate' :: repr a -> repr a
  abs' :: repr a -> repr a
  signum' :: repr a -> repr a
  fromInteger' :: repr Integer -> repr a
  default plus' :: (Num a, Applicative repr) => repr a -> repr a -> repr a
  plus' = liftA2 (+)
  default minus' :: (Num a, Applicative repr) => repr a -> repr a -> repr a
  minus' = liftA2 (-)
  default times' :: (Num a, Applicative repr) => repr a -> repr a -> repr a
  times' = liftA2 (*)
  default negate' :: (Num a, Applicative repr) => repr a -> repr a
  negate' = fmap negate
  default abs' :: (Num a, Applicative repr) => repr a -> repr a
  abs' = fmap abs
  default signum' :: (Num a, Applicative repr) => repr a -> repr a
  signum' = fmap signum
  default fromInteger' :: (Num a, Applicative repr) => repr Integer -> repr a
  fromInteger' = fmap fromInteger

infixl 6 %+
(%+) :: Num' a repr => repr a -> repr a -> repr a
(%+) = plus'

infixl 6 %-
(%-) :: Num' a repr => repr a -> repr a -> repr a
(%-) = minus'

infixl 7 %*
(%*) :: Num' a repr => repr a -> repr a -> repr a
(%*) = times'

instance Num a => Num' a Identity

class Num' a repr => Fractional' a repr where
  fdiv' :: repr a -> repr a -> repr a
  recip' :: repr a -> repr a
  fromRational' :: repr Rational -> repr a
  default fdiv' :: (Fractional a, Applicative repr) => repr a -> repr a -> repr a
  fdiv' = liftA2 (/)
  default recip' :: (Fractional a, Applicative repr) => repr a -> repr a
  recip' = fmap recip
  default fromRational' :: (Fractional a, Applicative repr) => repr Rational -> repr a
  fromRational' = fmap fromRational

instance Fractional a => Fractional' a Identity

infixl 7 %/
(%/) :: Fractional' a repr => repr a -> repr a -> repr a
(%/) = fdiv'

class (Fractional' a repr) => Floating' a repr where
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
  default pi' :: (Floating a, Applicative repr) => repr a
  pi' = pure pi
  default exp' :: (Floating a, Applicative repr) => repr a -> repr a
  exp' = fmap exp
  default log' :: (Floating a, Applicative repr) => repr a -> repr a
  log' = fmap log
  default sqrt' :: (Floating a, Applicative repr) => repr a -> repr a
  sqrt' = fmap sqrt
  default exponent' :: (Floating a, Applicative repr) => repr a -> repr a -> repr a
  exponent' = liftA2 (**)
  default logBase' :: (Floating a, Applicative repr) => repr a -> repr a -> repr a
  logBase' = liftA2 logBase
  default sin' :: (Floating a, Applicative repr) => repr a -> repr a
  sin' = fmap sin
  default cos' :: (Floating a, Applicative repr) => repr a -> repr a
  cos' = fmap cos
  default tan' :: (Floating a, Applicative repr) => repr a -> repr a
  tan' = fmap tan
  default asin' :: (Floating a, Applicative repr) => repr a -> repr a
  asin' = fmap asin
  default acos' :: (Floating a, Applicative repr) => repr a -> repr a
  acos' = fmap acos
  default atan' :: (Floating a, Applicative repr) => repr a -> repr a
  atan' = fmap atan
  default sinh' :: (Floating a, Applicative repr) => repr a -> repr a
  sinh' = fmap sinh
  default cosh' :: (Floating a, Applicative repr) => repr a -> repr a
  cosh' = fmap cosh
  default tanh' :: (Floating a, Applicative repr) => repr a -> repr a
  tanh' = fmap tanh
  default asinh' :: (Floating a, Applicative repr) => repr a -> repr a
  asinh' = fmap asinh
  default acosh' :: (Floating a, Applicative repr) => repr a -> repr a
  acosh' = fmap acosh
  default atanh' :: (Floating a, Applicative repr) => repr a -> repr a
  atanh' = fmap atanh

instance Floating a => Floating' a Identity

infixr 8 %**
(%**) :: Floating' a repr => repr a -> repr a -> repr a
(%**) = exponent'

class (Num' a repr, Ord' a repr) => Real' a repr where
  toRational' :: repr a -> repr Rational
  default toRational' :: (Real a, Functor repr) => repr a -> repr Rational
  toRational' = fmap toRational

instance Real a => Real' a Identity

class Enum' a repr where
  succ' :: repr a -> repr a
  pred' :: repr a -> repr a
  toEnum' :: repr Int -> repr a
  fromEnum' :: repr a -> repr Int
  enumFrom' :: repr a -> repr [a]
  enumFromThen' :: repr a -> repr a -> repr [a]
  enumFromTo' :: repr a -> repr a -> repr [a]
  enumFromThenTo' :: repr a -> repr a -> repr a -> repr [a]
  default succ' :: (Enum a, Applicative repr) => repr a -> repr a
  succ' = fmap succ
  default pred' :: (Enum a, Applicative repr) => repr a -> repr a
  pred' = fmap pred
  default toEnum' :: (Enum a, Applicative repr) => repr Int -> repr a
  toEnum' = fmap toEnum
  default fromEnum' :: (Enum a, Applicative repr) => repr a -> repr Int
  fromEnum' = fmap fromEnum
  default enumFrom' :: (Enum a, Applicative repr) => repr a -> repr [a]
  enumFrom' = fmap enumFrom
  default enumFromThen' :: (Enum a, Applicative repr) => repr a -> repr a -> repr [a]
  enumFromThen' = liftA2 enumFromThen
  default enumFromTo' :: (Enum a, Applicative repr) => repr a -> repr a -> repr [a]
  enumFromTo' = liftA2 enumFromTo
  default enumFromThenTo' :: (Enum a, Applicative repr) => repr a -> repr a -> repr a -> repr [a]
  enumFromThenTo' = liftA3 enumFromThenTo

instance Enum a => Enum' a Identity

class (Real' a repr, Enum' a repr) => Integral' a repr where
  quot' :: repr a -> repr a -> repr a
  rem' :: repr a -> repr a -> repr a
  div' :: repr a -> repr a -> repr a
  mod' :: repr a -> repr a -> repr a
  quotRem' :: repr a -> repr a -> repr (a,a)
  divMod' :: repr a -> repr a -> repr (a,a)
  toInteger' :: repr a -> repr Integer
  default quot' :: (Integral a, Applicative repr) => repr a -> repr a -> repr a
  quot' = liftA2 quot
  default rem' :: (Integral a, Applicative repr) => repr a -> repr a -> repr a
  rem' = liftA2 rem
  default div' :: (Integral a, Applicative repr) => repr a -> repr a -> repr a
  div' = liftA2 div
  default mod' :: (Integral a, Applicative repr) => repr a -> repr a -> repr a
  mod' = liftA2 mod
  default quotRem' :: (Integral a, Applicative repr) => repr a -> repr a -> repr (a,a)
  quotRem' = liftA2 quotRem
  default divMod' :: (Integral a, Applicative repr) => repr a -> repr a -> repr (a,a)
  divMod' = liftA2 divMod
  default toInteger' :: (Integral a, Applicative repr) => repr a -> repr Integer
  toInteger' = fmap toInteger

instance Integral a => Integral' a Identity

fromIntegral' :: (Integral' a repr, Num' b repr) => repr a -> repr b
fromIntegral' = fromInteger' . toInteger'

class LiftBool repr where
  true' :: repr Bool
  false' :: repr Bool
  if' :: repr Bool -> repr a -> repr a -> repr a
  default true' :: Applicative repr => repr Bool
  true' = pure True
  default false' :: Applicative repr => repr Bool
  false' = pure False
  default if' :: Applicative repr => repr Bool -> repr a -> repr a -> repr a
  if' = liftA3 $ \b x y -> if b then x else y

instance LiftBool Identity

--
-- Higher kinds
--

newtype T1 repr f a = T1 { unT1 :: f (repr a) }
  deriving (Semigroup, Monoid)

unlift1 :: (Monad repr, Traversable f) => repr (T1 repr f a) -> repr (f a)
unlift1 = (join .) $ fmap $ \(T1 fa) -> sequence fa

newtype T2 repr f a b = T2 { unT2 :: f (repr a) (repr b) }

class Lambda repr => Functor' f repr where
  fmap' :: repr (Arr repr a b) -> repr (f a) -> repr (f b)
  default fmap' :: (Lambda repr, Functor repr, f ~ T1 repr g, Functor g) => repr (Arr repr a b) -> repr (f a) -> repr (f b)
  fmap' rf rx = flip fmap rx $ \(T1 x) -> T1 $ fmap (rf %$) x

instance {-# OVERLAPPABLE #-} Functor f => Functor' (T1 Identity f) Identity

instance Lambda repr => Functor' (T2 repr (->) a) repr where
  fmap' = (%.)

instance (Lambda repr, Tuple2 repr) => Functor' ((,) a) repr where
  fmap' f ab = tup2' (pi1' ab) $ f %$ pi2' ab

infixl 4 <%$>
(<%$>) :: Functor' f repr => repr (Arr repr a b) -> repr (f a) -> repr (f b)
(<%$>) = fmap'

class Functor' f repr => Applicative' f repr where
  pure' :: repr a -> repr (f a)
  ap' :: repr (f (Arr repr a b)) -> repr (f a) -> repr (f b)
  default pure' :: (f ~ T1 repr g, Applicative g, Applicative repr) => repr a -> repr (f a)
  pure' = pure . T1 . pure
  default ap' :: (Lambda repr, Applicative repr, f ~ T1 repr g, Applicative g) => repr (f (Arr repr a b)) -> repr (f a) -> repr (f b)
  ap' = liftA2 $ \(T1 ff) (T1 fx) -> T1 $ liftA2 (%$) ff fx

infixl 4 <%*>
(<%*>) :: Applicative' f repr => repr (f (Arr repr a b)) -> repr (f a) -> repr (f b)
(<%*>) = ap'

liftA2' :: Applicative' f repr => repr (Arr repr a (Arr repr b c)) -> repr (f a) -> repr (f b) -> repr (f c)
liftA2' f x y = f <%$> x <%*> y

instance {-# OVERLAPPABLE #-} Applicative f => Applicative' (T1 Identity f) Identity

instance Lambda repr => Applicative' (T2 repr (->) a) repr where
  pure' x = lam $ \_ -> x
  ap' f x = lam $ \a -> f %$ a %$ (x %$ a)

class Foldable' t repr where
  foldMap' :: Monoid' m repr => repr (Arr repr a m) -> repr (t a) -> repr m
  foldl'' :: repr (Arr repr b (Arr repr a b)) -> repr b -> repr (t a) -> repr b
  length' :: repr (t a) -> repr Int
  product' :: Num' a repr => repr (t a) -> repr a
  default foldMap' :: (Monoid' m repr, Lambda repr, Monad repr, t ~ T1 repr g, Foldable g) => repr (Arr repr a m) -> repr (t a) -> repr m
  foldMap' rf = join . fmap (\(T1 g) -> unL . foldMap (L . (rf %$)) $ g)
  default foldl'' :: (Lambda repr, Monad repr, t ~ T1 repr g, Foldable g) => repr (Arr repr b (Arr repr a b)) -> repr b -> repr (t a) -> repr b
  foldl'' rf a = join . fmap (\(T1 g) -> foldl (\x y -> rf %$ x %$ y) a g)
  default length' :: (Monad repr, t ~ T1 repr g, Foldable g) => repr (t a) -> repr Int
  length' = fmap (length . unT1)
  default product' :: (Num' a repr, Monad repr, t ~ T1 repr g, Foldable g) => repr (t a) -> repr a
  product' = join . fmap (unL . getProduct . foldMap (Product . L) . unT1)

mconcat' :: (Lambda repr, Monoid' m repr, Foldable' t repr) => repr (t m) -> repr m
mconcat' = foldMap' id'

instance {-# OVERLAPPABLE #-} Foldable f => Foldable' (T1 Identity f) Identity

type Maybe' repr = T1 repr Maybe

class Functor' (T1 repr Maybe) repr => LiftMaybe repr where
  nothing' :: repr (T1 repr Maybe a)
  just' :: repr a -> repr (T1 repr Maybe a)
  maybe' :: repr (T1 repr Maybe b) -> repr a -> repr (Arr repr b a) -> repr a
  default nothing' :: Applicative repr => repr (T1 repr Maybe a)
  nothing' = pure $ T1 Nothing
  default just' :: Applicative repr => repr a -> repr (T1 repr Maybe a)
  just' = pure . T1 . Just
  default maybe' :: (Lambda repr, Monad repr) => repr (T1 repr Maybe b) -> repr a -> repr (Arr repr b a) -> repr a
  maybe' mx e0 e1 = join $ fmap (\(T1 m) -> maybe e0 (e1 %$) m) mx

instance LiftMaybe Identity

type List' repr = T1 repr []

class (Functor' (T1 repr []) repr, Foldable' (T1 repr []) repr) => LiftList repr where
  nil' :: repr (T1 repr [] a)
  cons' :: repr a -> repr (T1 repr [] a) -> repr (T1 repr [] a)
  foldr' :: repr (T1 repr [] a) -> repr b -> repr (Arr repr a (Arr repr b b)) -> repr b
  default nil' :: Applicative repr => repr (T1 repr [] a)
  nil' = pure (T1 [])
  default cons' :: Functor repr => repr a -> repr (T1 repr [] a) -> repr (T1 repr [] a)
  cons' x = fmap $ \(T1 xs) -> T1 (x:xs)
  default foldr' :: (Lambda repr, Monad repr) => repr (T1 repr [] a) -> repr b -> repr (Arr repr a (Arr repr b b)) -> repr b
  foldr' rxs b0 bf = join $ flip fmap rxs $ \(T1 xs) -> foldr (\a b -> bf %$ a $% b) b0 xs

instance LiftList Identity

dropWhile' :: (LiftBool repr, LiftList repr) => repr (Arr repr a Bool) -> repr (List' repr a) -> repr (List' repr a)
dropWhile' p xs = foldr' xs nil' $ lam \y -> lam \ys -> if' (p %$ y) (cons' y ys) ys

last' :: (LiftMaybe repr, LiftList repr) => repr (List' repr a) -> repr (Maybe' repr a)
last' xs = foldr' xs nothing' $ lam \y -> lam \ys -> maybe' ys (just' y) (lam just')

-- TODO: This is a little bit unsatisfactory because Set can't be T1 usefully
class LiftList repr => LiftSet repr where
  fromList' :: Ord' a repr => repr (List' repr a) -> repr (Set a)
  toAscList' :: Ord' a repr => repr (Set a) -> repr (List' repr a)
  default fromList' :: (Monad repr, Ord' a repr, List' repr ~ T1 repr []) => repr (List' repr a) -> repr (Set a)
  fromList' = (join .) . fmap $ \(T1 xs) -> fmap (Set.fromList) $ sequence xs
  default toAscList' :: (Monad repr, Ord' a repr, List' repr ~ T1 repr []) => Ord' a repr => repr (Set a) -> repr (List' repr a)
  toAscList' = fmap $ T1 . fmap pure . Set.toAscList

instance LiftSet Identity

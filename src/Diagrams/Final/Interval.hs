{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
module Diagrams.Final.Interval where

import Control.Monad
import qualified Numeric.Interval.Kaucher as I

import Diagrams.Final.Core

type Interval' repr a = I.Interval (repr a)

infix 3 %...

class (forall a. Val repr (Interval' repr a)) => LiftInterval repr where
  (%...) :: repr a -> repr a -> repr (Interval' repr a)
  interval' :: repr (Interval' repr a) -> (repr a -> repr a -> repr r) -> repr r
  default (%...) :: Applicative repr => repr a -> repr a -> repr (Interval' repr a)
  (%...) x y = pure $ x I.... y
  default interval' :: Monad repr => repr (Interval' repr a) -> (repr a -> repr a -> repr r) -> repr r
  interval' xi k = join $ flip fmap xi $ \(I.I x y) -> k x y

negInfinity' :: Fractional' repr a => repr a
negInfinity' = (-1) %/ 0

posInfinity' :: Fractional' repr a => repr a
posInfinity' = 1 %/ 0

nan' :: Fractional' repr a => repr a
nan' = 0 %/ 0

whole' :: (LiftInterval repr, Fractional' repr a) => repr (Interval' repr a)
whole' = negInfinity' %... posInfinity'

empty' :: (LiftInterval repr, Fractional' repr a) => repr (Interval' repr a)
empty' = nan' %... nan'

null' :: (LiftInterval repr, Ord' repr a, LiftBool repr) => repr (Interval' repr a) -> repr Bool
null' xi = interval' xi $ \inf sup -> not' (inf %<= sup)

inf' :: LiftInterval repr => repr (Interval' repr a) -> repr a
inf' xi = interval' xi $ \inf _ -> inf

sup' :: LiftInterval repr => repr (Interval' repr a) -> repr a
sup' xi = interval' xi $ \_ sup -> sup

midpoint' :: (LiftInterval repr, Fractional' repr a) => repr (Interval' repr a) -> repr a
midpoint' xi = interval' xi $ \inf sup -> inf %+ (sup %- inf) %/ 2

singleton' :: LiftInterval repr => repr a -> repr (Interval' repr a)
singleton' x = x %... x

member' :: (LiftInterval repr, LiftBool repr, Ord' repr a) => repr a -> repr (Interval' repr a) -> repr Bool
member' x xi = interval' xi $ \inf sup -> inf %<= x %&& x %<= sup

notMember' :: (LiftInterval repr, LiftBool repr, Ord' repr a) => repr a -> repr (Interval' repr a) -> repr Bool
notMember' x xi = not' $ member' x xi

width' :: (LiftInterval repr, Num' repr a) => repr (Interval' repr a) -> repr a
width' xi = interval' xi $ \inf sup -> sup %- inf

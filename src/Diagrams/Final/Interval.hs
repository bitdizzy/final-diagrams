{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Diagrams.Final.Interval where

import Control.Monad
import qualified Numeric.Interval.Kaucher as I

import Diagrams.Final.Core

newtype Interval' repr a = Interval' { unInterval' :: I.Interval (repr a) }

infix 3 %...

class (forall a. Val repr (Interval' repr a)) => LiftInterval repr where
  (%...) :: repr a -> repr a -> repr (Interval' repr a)
  interval' :: repr (Interval' repr a) -> (repr a -> repr a -> repr r) -> repr r
  default (%...) :: Applicative repr => repr a -> repr a -> repr (Interval' repr a)
  (%...) x y = pure $ Interval' $ x I.... y
  default interval' :: Monad repr => repr (Interval' repr a) -> (repr a -> repr a -> repr r) -> repr r
  interval' xi k = join $ flip fmap xi $ \(Interval' (I.I x y)) -> k x y

instance (LiftInterval repr, Eq' repr a) => Eq' repr (Interval' repr a) where
  eq' i1 i2 = interval' i1 $ \l1 u1 -> interval' i2 $ \l2 u2 ->
    l1 %== l2 %&& u1 %== u2
  neq' i1 i2 = interval' i1 $ \l1 u1 -> interval' i2 $ \l2 u2 ->
    l1 %/= l2 %|| u1 %/= u2

instance (LiftInterval repr, Ord' repr a) => Ord' repr (Interval' repr a) where
  compare' i1 i2 = interval' i1 $ \l1 u1 -> interval' i2 $ \l2 u2 ->
    ordering' (compare' l1 l2) \case
      LT -> ltV'
      GT -> gtV'
      EQ -> compare' u1 u2
  lt' i1 i2 = ordering' (compare' i1 i2) $ \case
    LT -> true'
    _ -> false'
  lte' i1 i2 = ordering' (compare' i1 i2) $ \case
    GT -> false'
    _ -> true'
  gt' i1 i2 = ordering' (compare' i1 i2) $ \case
    GT -> true'
    _ -> false'
  gte' i1 i2 = ordering' (compare' i1 i2) $ \case
    LT -> false'
    _ -> true'
  max' i1 i2 = ordering' (compare' i1 i2) $ \case
    GT -> i1
    _ -> i2
  min' i1 i2 = ordering' (compare' i1 i2) $ \case
    LT -> i1
    _ -> i2

instance (LiftInterval repr, LiftList repr, LiftMin repr, LiftMax repr, Ord' repr a, Num' repr a) => Num' repr (Interval' repr a) where
  plus' i1 i2 = interval' i1 \l1 u1 -> interval' i2 \l2 u2 ->
    (l1 %+ l2) %... (u1 %+ u2)
  minus' i1 i2 = interval' i1 \l1 u1 -> interval' i2 \l2 u2 ->
    (l1 %- u2) %... (u1 %- l2)
  times' i1 i2 = interval' i1 \l1 u1 -> interval' i2 \l2 u2 ->
    let_ (val1 [l1 %* l2, l1 %* u2, l2 %* u1, u1 %* u2]) \points ->
    -- Nothing case will never happen
      maybe' (minimum' points) (l1 %* l2) id'
        %... maybe' (maximum' points) (l1 %* l2) id'
  negate' i1 = interval' i1 \l1 u1 ->
    negate' u1 %... negate' l1
  abs' i1 = interval' i1 \l1 u1 ->
    if' (l1 %>= num 0) i1 $ if' (u1 %<= num 0) (negate' i1) $ if' ((l1 %< num 0) %&& (u1 %> num 0)) (num 0 %... (max' (negate' l1) u1)) $ i1
  signum' i1 = interval' i1 \l1 u1 ->
    signum' l1 %... signum' u1
  fromInteger' x = singleton' (fromInteger' x)

negInfinity' :: Fractional' repr a => repr a
negInfinity' = num (-1) %/ num 0

posInfinity' :: Fractional' repr a => repr a
posInfinity' = num 1 %/ num 0

nan' :: Fractional' repr a => repr a
nan' = num 0 %/ num 0

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
midpoint' xi = interval' xi $ \inf sup -> inf %+ (sup %- inf) %/ num 2

singleton' :: LiftInterval repr => repr a -> repr (Interval' repr a)
singleton' x = x %... x

member' :: (LiftInterval repr, LiftBool repr, Ord' repr a) => repr a -> repr (Interval' repr a) -> repr Bool
member' x xi = interval' xi $ \inf sup -> inf %<= x %&& x %<= sup

notMember' :: (LiftInterval repr, LiftBool repr, Ord' repr a) => repr a -> repr (Interval' repr a) -> repr Bool
notMember' x xi = not' $ member' x xi

width' :: (LiftInterval repr, Num' repr a) => repr (Interval' repr a) -> repr a
width' xi = interval' xi $ \inf sup -> sup %- inf

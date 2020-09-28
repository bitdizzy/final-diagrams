{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Diagrams.Final.Transform where

import Linear.Affine

import Diagrams.Final.Base

class Action repr t a where
  action :: repr t -> repr (a -> a)

class LinearTrans repr v n t | t -> v n where
  fromLinear :: repr (v (v n)) -> repr t
  toLinear :: repr t -> repr (v (v n))

class LinearTrans repr v n (LinearOf t) => AffineTrans repr v n t where
  type LinearOf t
  translate :: repr (v n) -> repr t
  translationOf :: repr t -> repr (v n)
  linearOf :: repr t -> repr (LinearOf t)

class Invertible repr t where
  invert :: repr t -> repr t

type Transformation repr v n t = (Monoidal repr t, AffineTrans repr v n t, Invertible repr t, Action repr t (Point v n))

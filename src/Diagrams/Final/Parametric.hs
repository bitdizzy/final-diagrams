{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Diagrams.Final.Parametric where

import Diagrams.Final.Core
import Diagrams.Final.Interval

class (PDom p ~ d, PCod p ~ r) => Parametric repr p d r | p -> d r where
  type PDom p
  type PCod p
  atParam :: repr p -> repr d -> repr r

instance Lambda repr => Parametric repr (Arr repr a b) a b where
  type PDom (Arr repr a b) = a
  type PCod (Arr repr a b) = b
  atParam = app

class Parametric repr p (PDom p) (PCod p) => DomainBounds repr p where
  domainLower :: repr p -> repr (PDom p)
  domainUpper :: repr p -> repr (PDom p)
  evalAtLower :: repr p -> repr (PCod p)
  evalAtLower p = p `atParam` domainLower p
  evalAtUpper :: repr p -> repr (PCod p)
  evalAtUpper p = p `atParam` domainUpper p

class (Tuple2 repr, DomainBounds repr p) => Sectionable repr p where
  splitAtParam :: repr p -> repr (PDom p) -> repr (p, p)
  splitAtParam p t = tup2' (section p (domainLower p) t) (section p t (domainUpper p))
  section :: repr p -> repr (PDom p) -> repr (PDom p) -> repr p
  default section :: Fractional' repr (PDom p) => repr p -> repr (PDom p) -> repr (PDom p) -> repr p
  section p t1 t2 = pi2' $ splitAtParam (pi1' (splitAtParam p t2)) (t1 %/ t2)
  reverseDomain :: repr p -> repr p

class (LiftInterval repr, Parametric repr p (PDom p) (PCod p)) => HasArcLength repr p where
  arcLengthBounded :: repr Scalar -> repr p -> repr (Interval' repr Scalar)
  arcLength :: repr Scalar -> repr p -> repr Scalar
  arcLengthToParam :: repr Scalar -> repr p -> repr Scalar -> repr (PDom p)

stdArcLength :: (Spatial repr, HasArcLength repr p) => repr p -> repr Scalar
stdArcLength = arcLength stdTolerance

stdArcLengthToParam :: (Spatial repr, HasArcLength repr p) => repr p -> repr Scalar -> repr (PDom p)
stdArcLengthToParam = arcLengthToParam stdTolerance

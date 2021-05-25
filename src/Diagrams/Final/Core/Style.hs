{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Core.Style where

import Control.Monad
import Data.Kind

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space
import Diagrams.Final.Core.Measure

type Style repr style = ((Semigroup' repr style, AffineAction' repr Scalar style) :: Constraint)

class Style repr style => Styled repr style a where
  style' :: repr style -> repr a -> repr a

data AttributeType = InvariantA | ScaledA | TransformedA

data Attribute repr a tp where
  Attribute_Invariant :: repr a -> Attribute repr a 'InvariantA
  Attribute_Scaled :: repr (Scaled repr a) -> Attribute repr a 'ScaledA
  Attribute_Transformed :: AffineAction' repr Scalar a => repr a -> Attribute repr a 'TransformedA

class (forall a tp. Val repr (Attribute repr a tp), Scales repr) => Attributes repr where
  invariantA' :: repr a -> repr (Attribute repr a 'InvariantA)
  scaledA' :: repr (Scaled repr a) -> repr (Attribute repr a 'ScaledA)
  transformedA' :: AffineAction' repr Scalar a => repr a -> repr (Attribute repr a 'TransformedA)
  attr'
    :: repr (Attribute repr a tp)
    -> (repr a -> repr r)
    -> (repr (Scaled repr a) -> repr r)
    -> (AffineAction' repr Scalar a => repr a -> repr r)
    -> repr r
  attr''
    :: repr (Attribute repr a tp)
    -> (repr a -> repr (r a 'InvariantA))
    -> (repr (Scaled repr a) -> repr (r a 'ScaledA))
    -> (AffineAction' repr Scalar a => repr a -> repr (r a 'TransformedA))
    -> repr (r a tp)
  default invariantA' :: Applicative repr => repr a -> repr (Attribute repr a 'InvariantA)
  invariantA' = pure . Attribute_Invariant
  default scaledA' :: Applicative repr => repr (Scaled repr a) -> repr (Attribute repr a 'ScaledA)
  scaledA' = pure . Attribute_Scaled
  default transformedA' :: (Applicative repr, AffineAction' repr Scalar a) => repr a -> repr (Attribute repr a 'TransformedA)
  transformedA' = pure . Attribute_Transformed
  default attr'
    :: Monad repr
    => repr (Attribute repr a tp)
    -> (repr a -> repr r)
    -> (repr (Scaled repr a) -> repr r)
    -> (AffineAction' repr Scalar a => repr a -> repr r)
    -> repr r
  attr' a ie se te = join $ flip fmap a $ \case
    Attribute_Invariant x -> ie x
    Attribute_Scaled x -> se x
    Attribute_Transformed x -> te x
  default attr''
    :: Monad repr
    => repr (Attribute repr a tp)
    -> (repr a -> repr (r a 'InvariantA))
    -> (repr (Scaled repr a) -> repr (r a 'ScaledA))
    -> (AffineAction' repr Scalar a => repr a -> repr (r a 'TransformedA))
    -> repr (r a tp)
  attr'' a ie se te = join $ flip fmap a $ \case
    Attribute_Invariant x -> ie x
    Attribute_Scaled x -> se x
    Attribute_Transformed x -> te x

instance Attributes repr => AffineAction' repr Scalar (Attribute repr a tp) where
  actA' t a = attr'' a invariantA' (scaledA' . actA' t) (transformedA' . actA' t)

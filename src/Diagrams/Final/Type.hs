{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Type where

import Data.Kind
import Data.Monoid
import Data.Set (Set)
import Linear (Additive, Metric, Conjugate)
import Linear.Affine (Affine(type Diff))

import qualified Diagrams.Final.Space.Primitive as T
import Diagrams.Final.Base
import Diagrams.Final.Envelope
import Diagrams.Final.Measure
import Diagrams.Final.Space
import Diagrams.Final.Trace

data DiagramContext repr = DiagramContext
  { _diagramContext_envelope :: repr (Envelope repr)
  , _diagramContext_trace :: repr (Trace repr)
  }

instance (Semigroup' (Envelope repr) repr, Semigroup' (Trace repr) repr) => Semigroup (DiagramContext repr) where
  DiagramContext e0 t0 <> DiagramContext e1 t1 = DiagramContext (e0 %<> e1) (t0 %<> t1)

transformContext
  :: (AffineAction' Scalar (Envelope repr) repr, AffineAction' Scalar (Trace repr) repr)
  => repr (AffineTransform repr Scalar)
  -> DiagramContext repr
  -> DiagramContext repr
transformContext t (DiagramContext e tr) = DiagramContext (actA' t e) (actA' t tr)

class ( Envelopes repr, Traces repr, Scales repr
      , Semigroup' (Style repr) repr
      , Semigroup' (Diagram repr) repr
      , AffineAction' Scalar (Style repr) repr
      , AffineAction' Scalar (Prim repr) repr
      , AffineAction' Scalar (Diagram repr) repr
      ) => Diagrams repr where
  type Diagram repr :: Type
  type Diagram repr = DefaultDiagram repr
  type Prim repr :: Type
  type Style repr :: Type
  type Ann repr :: Type
  prim :: repr (Envelope repr) -> repr (Trace repr) -> repr (Prim repr) -> repr (Diagram repr)
  delayed :: repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr)) -> repr (Diagram repr)
  ann :: repr (Ann repr) -> repr (Diagram repr) -> repr (Diagram repr)
  style :: repr (Style repr) -> repr (Diagram repr) -> repr (Diagram repr)
  default prim :: (Applicative repr, Diagram repr ~ DefaultDiagram repr) => repr (Envelope repr) -> repr (Trace repr) -> repr (Prim repr) -> repr (Diagram repr)
  prim e tr p = pure $ DefaultDiagram $ \_ _ _ pr _ _ -> pr (DiagramContext e tr) p
  default delayed :: (Applicative repr, Diagram repr ~ DefaultDiagram repr) => repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr)) -> repr (Diagram repr)
  delayed e tr p = pure $ DefaultDiagram $ \_ _ _ _ delayed' _ -> delayed' (DiagramContext e tr) p
  default ann :: (Functor repr, Diagram repr ~ DefaultDiagram repr) => repr (Ann repr) -> repr (Diagram repr) -> repr (Diagram repr)
  ann x = fmap $ \(DefaultDiagram d) -> DefaultDiagram $ \t s a p delayed' l -> a x $ d t s a p delayed' l
  default style :: (Functor repr, Diagram repr ~ DefaultDiagram repr) => repr (Style repr) -> repr (Diagram repr) -> repr (Diagram repr)
  style x = fmap $ \(DefaultDiagram d) -> DefaultDiagram $ \t s a p delayed' l -> s x $ d t s a p delayed' l

-- | Reference implementation of non-empty diagrams
newtype DefaultDiagram repr = DefaultDiagram
  { unDefaultDiagram
      :: forall r. (repr (AffineTransform repr Scalar) -> r -> r)
      -> (repr (Style repr) -> r -> r)
      -> (repr (Ann repr) -> r -> r)
      -> (DiagramContext repr -> repr (Prim repr) -> r)
      -> (DiagramContext repr -> repr (Scaled repr (Diagram repr)) -> r)
      -> (r -> r -> r)
      -> r
  }

instance (Monad repr) => Semigroup (DefaultDiagram repr) where
  DefaultDiagram d0 <> DefaultDiagram d1 = DefaultDiagram $ \t s a p d l ->
    let r0 = d0 t s a p d l
        r1 = d1 t s a p d l
     in l r0 r1

instance
  ( AffineAction' Scalar (Style repr) repr
  , AffineAction' Scalar (Prim repr) repr
  , Monad repr
  , Envelopes repr
  , Traces repr
  , Diagram repr ~ DefaultDiagram repr
  ) => AffineAction' Scalar (DefaultDiagram repr) repr where
  actA' tf = fmap $ \(DefaultDiagram d) -> DefaultDiagram $ \t s a p l m -> t tf $ d t s a p l m

renderDiagramM
  :: (Monad repr, Diagrams repr, Diagram repr ~ DefaultDiagram repr)
  => repr (Diagram repr)
  -> repr (AffineTransform repr Scalar)
  -- ^ Transformation from global diagram coordinates to output coordinates
  -> (repr (AffineTransform repr Scalar) -> r -> r)
  -> (repr (Style repr) -> r -> r)
  -> (repr (Ann repr) -> r -> r)
  -> (repr (Prim repr) -> r)
  -> (DiagramContext repr -> r -> r)
  -> (r -> r -> r)
  -> (repr r -> r)
  -> (r -> DiagramContext repr)
  -> repr r
renderDiagramM d' tf0 t s a p attachContext l f getCtx = flip fmap (actA' tf0 d') $ \(DefaultDiagram d) ->
  -- Tie the knot to instantiate parts of the diagram that depend on
  -- the global context.
  let runPrim c x = attachContext c $ p x
      runDelayed preCtx dl =
        let dl' = withScaleOf dl tf0 (_diagramContext_envelope finalContext)
         in attachContext preCtx $ f (flip fmap dl' $ \x -> unDefaultDiagram x t s a runPrim runDelayed l)
      finalDiagram = d t s a runPrim runDelayed l
      finalContext = getCtx finalDiagram
   in finalDiagram

newtype MonadicDiagram repr prim style ann a = MonadicDiagram { unMonadicDiagram :: repr a }
  deriving (Functor, Applicative, Monad)

deriving via (Ap repr a) instance (Applicative repr, Num a) => Num (MonadicDiagram repr prim style ann a)

instance Monad repr => Lambda (MonadicDiagram repr prim style ann)
instance Monad repr => Proj1 (a, b) a (MonadicDiagram repr prim style ann)
instance Monad repr => Proj2 (a, b) b (MonadicDiagram repr prim style ann)
instance Monad repr => Proj1 (a, b, c) a (MonadicDiagram repr prim style ann)
instance Monad repr => Proj2 (a, b, c) b (MonadicDiagram repr prim style ann)
instance Monad repr => Proj3 (a, b, c) c (MonadicDiagram repr prim style ann)
instance Monad repr => Tuple2 (MonadicDiagram repr prim style ann)
instance Monad repr => Tuple3 (MonadicDiagram repr prim style ann)
instance (Eq n, Monad repr) => Eq' n (MonadicDiagram repr prim style ann)
instance (Ord n, Monad repr) => Ord' n (MonadicDiagram repr prim style ann)
instance (Num n, Monad repr) => Num' n (MonadicDiagram repr prim style ann)
instance (Conjugate n, Monad repr) => Conjugate' n (MonadicDiagram repr prim style ann)
instance (Real n, Monad repr) => Real' n (MonadicDiagram repr prim style ann)
instance (Enum n, Monad repr) => Enum' n (MonadicDiagram repr prim style ann)
instance (Integral n, Monad repr) => Integral' n (MonadicDiagram repr prim style ann)
instance (Fractional n, Monad repr) => Fractional' n (MonadicDiagram repr prim style ann)
instance (Floating n, Monad repr) => Floating' n (MonadicDiagram repr prim style ann)
instance (Functor f, Monad repr) => Functor' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Applicative f, Monad repr) => Applicative' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Foldable f, Monad repr) => Foldable' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Additive f, Monad repr) => Additive' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Metric f, Monad repr) => Metric' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Functor f, Affine f, Monad repr) => Affine' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann) where
  type Diff' (Lift1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann) = Lift1 (MonadicDiagram repr prim style ann) (Diff f)
instance (forall x. Num x => T.LinearAction x (f x), Num n, Functor f, Monad repr) => LinearAction' n (Lift1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance (forall x. Num x => T.AffineAction x (f x), Num n, Functor f, Monad repr) => AffineAction' n (Lift1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMaybe (MonadicDiagram repr prim style ann)
instance Monad repr => LiftList (MonadicDiagram repr prim style ann)
instance Monad repr => LiftSet (MonadicDiagram repr prim style ann)

instance Monad repr => Semigroup' (Lift1 (MonadicDiagram repr prim style ann) T.LinearTransform Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (Lift1 (MonadicDiagram repr prim style ann) T.LinearTransform Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Semigroup' (Lift1 (MonadicDiagram repr prim style ann) T.AffineTransform Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (Lift1 (MonadicDiagram repr prim style ann) T.AffineTransform Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Semigroup' (Set Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (Set Scalar) (MonadicDiagram repr prim style ann)

instance (Monad repr, T.IsDiffOf T.Point T.Vector) => Semigroup' (DefaultDiagram (MonadicDiagram repr prim style ann)) (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Spatial (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Envelopes (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Scales (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Traces (MonadicDiagram repr prim style ann)

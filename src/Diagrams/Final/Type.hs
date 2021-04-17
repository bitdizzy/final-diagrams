{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Type where

import Control.Applicative
import Control.Lens
import Data.Coerce
import Data.Kind
import Data.Monoid
import Linear (Additive, Metric)
import Linear.Affine (Affine(type Diff))

import qualified Diagrams.Final.Sig.Space as T
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
  type Prim repr :: Type
  type Style repr :: Type
  type Ann repr :: Type
  prim :: repr (Envelope repr) -> repr (Trace repr) -> repr (Prim repr) -> repr (Diagram repr)
  delayed :: repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr)) -> repr (Diagram repr)
  ann :: repr (Ann repr) -> repr (Diagram repr) -> repr (Diagram repr)
  style :: repr (Style repr) -> repr (Diagram repr) -> repr (Diagram repr)

-- | Reference implementation of non-empty diagrams
newtype Diagram repr = Diagram
  { unDiagram
      :: forall r. (repr (Style repr) -> r -> r)
      -> (repr (Ann repr) -> r -> r)
      -> (repr (Prim repr) -> r)
      -> (repr (Scaled repr (Diagram repr)) -> r)
      -> (r -> r -> r)
      -> (DiagramContext repr, r)
  }

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
instance (Semigroup a, Monad repr) => Semigroup' a (MonadicDiagram repr prim style ann)
instance (Monoid a, Monad repr) => Monoid' a (MonadicDiagram repr prim style ann)
instance (forall x. Num x => T.LinearAction x (f x), Num n, Functor f, Monad repr) => LinearAction' n (Lift1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance (forall x. Num x => T.AffineAction x (f x), Num n, Functor f, Monad repr) => AffineAction' n (Lift1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMaybe (MonadicDiagram repr prim style ann)
instance Monad repr => LiftList (MonadicDiagram repr prim style ann)
instance Monad repr => LiftSet (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Representational repr, Monad repr) => Spatial (MonadicDiagram repr prim style ann) where
  type NumConstr (MonadicDiagram repr prim style ann) = Num

instance (T.IsDiffOf T.Point T.Vector, Representational repr, Monad repr) => Envelopes (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Representational repr, Monad repr) => Scales (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Representational repr, Monad repr) => Traces (MonadicDiagram repr prim style ann)

instance (Monad repr, Envelopes repr, Traces repr) => Semigroup (Diagram repr) where
  Diagram d0 <> Diagram d1 = Diagram $ \s a p d l ->
    let (ctx0, r0) = d0 s a p d l
        (ctx1, r1) = d1 s a p d l
     in (ctx0 <> ctx1, l r0 r1)

instance
  ( Representational repr
  , Monad repr
  , Semigroup style
  , AffineAction' Scalar style (MonadicDiagram repr prim style ann)
  , AffineAction' Scalar prim (MonadicDiagram repr prim style ann)
  ) => Diagrams (MonadicDiagram repr prim style ann) where
  type Prim (MonadicDiagram repr prim style ann) = prim
  type Style (MonadicDiagram repr prim style ann) = style
  type Ann (MonadicDiagram repr prim style ann) = ann
  prim e tr p = pure $ Diagram $ \_ _ pr _ _ ->
    (DiagramContext e tr, pr p)
  delayed e tr p = pure $ Diagram $ \_ _ _ delayed' _ ->
    (DiagramContext e tr, delayed' p)
  ann x = fmap $ \(Diagram d) -> Diagram $ \s a p delayed' l -> fmap (a x) (d s a p delayed' l)
  style x = fmap $ \(Diagram d) -> Diagram $ \s -> d (s . flip (liftA2 (<>)) x)

instance
  ( AffineAction' Scalar style (MonadicDiagram repr prim style ann)
  , AffineAction' Scalar prim (MonadicDiagram repr prim style ann)
  , Representational repr
  , Monad repr
  ) => AffineAction' Scalar (Diagram (MonadicDiagram repr prim style ann)) (MonadicDiagram repr prim style ann) where
  actA' t = fmap $ \(Diagram d) -> Diagram $ \s a p l -> fmap (_1 %~ transformContext') $ d
    (s . actA' t)
    a
    (p . actA' t)
    l
   where
    transformContext' (DiagramContext (MonadicDiagram e) (MonadicDiagram tr)) =
     let DiagramContext e' tr' = transformContext t $ DiagramContext (coerce e) (coerce tr)
      in DiagramContext (MonadicDiagram (coerce e')) (MonadicDiagram (coerce tr'))

renderDiagramM
  :: (Monad repr, Diagrams repr)
  => repr (Diagram repr)
  -> repr (AffineTransform repr Scalar)
  -- ^ Transformation from global diagram coordinates to output coordinates
  -> (repr (Style repr) -> r -> r)
  -> (repr (Ann repr) -> r -> r)
  -> (repr (Prim repr) -> r)
  -> (r -> r -> r)
  -> (repr r -> r)
  -> repr r
renderDiagramM d' t s a p l f = flip fmap (actA' t d') $ \(Diagram d) ->
  -- Tie the knot to instantiate parts of the diagram that depend on
  -- the global context.
  let runDelayed dl =
        let dl' = withScaleOf dl t (_diagramContext_envelope finalContext)
         in f (flip fmap dl' $ \x -> snd $ unDiagram x s a p runDelayed l)
      (finalContext, finalDiagram) = d s a p runDelayed l
   in finalDiagram


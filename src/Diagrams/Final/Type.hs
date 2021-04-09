{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Diagrams.Final.Type where

import Control.Lens
import Data.Kind

import Diagrams.Final.Base
import Diagrams.Final.Envelope
import Diagrams.Final.Measure
import Diagrams.Final.Space
import Diagrams.Final.Trace

data DiagramContext repr = DiagramContext
  { _diagramContext_envelope :: repr Envelope
  , _diagramContext_trace :: repr Trace
  }

instance (Semigroup (repr Envelope), Semigroup (repr Trace)) => Semigroup (DiagramContext repr) where
  DiagramContext e0 t0 <> DiagramContext e1 t1 = DiagramContext (e0 <> e1) (t0 <> t1)

transformContext
  :: (AffineAction' Envelope repr, AffineAction' Trace repr)
  => repr (AffineTransform Scalar)
  -> DiagramContext repr
  -> DiagramContext repr
transformContext t (DiagramContext e tr) = DiagramContext (actA' t e) (actA' t tr)

class ( Envelopes repr, Traces repr
      , Semigroup (repr (Style repr))
      , Semigroup (repr (Diagram repr))
      , AffineAction' (Style repr) repr
      , AffineAction' (Prim repr) repr
      , AffineAction' (Diagram repr) repr
      ) => Diagrams repr where
  type Prim repr :: Type
  type Style repr :: Type
  type Ann repr :: Type
  prim :: repr Envelope -> repr Trace -> repr (Prim repr) -> repr (Diagram repr)
  delayed :: repr Envelope -> repr Trace -> repr (Scaled (Diagram repr)) -> repr (Diagram repr)
  ann :: repr (Ann repr) -> repr (Diagram repr) -> repr (Diagram repr)
  style :: repr (Style repr) -> repr (Diagram repr) -> repr (Diagram repr)

-- | Reference implementation of non-empty diagrams
newtype Diagram repr = Diagram
  { unDiagram
      :: forall r. (repr (Style repr) -> r -> r)
      -> (repr (Ann repr) -> r -> r)
      -> (repr (Prim repr) -> r)
      -> (repr (Scaled (Diagram repr)) -> r)
      -> (r -> r -> r)
      -> (DiagramContext repr, r)
  }

{-
renderDiagram
  :: ( Action (repr (AffineTransform Scalar)) (repr style)
     , Action (repr (AffineTransform Scalar)) (repr prim)
     )
  => Diagram repr style ann prim
  -> repr (AffineTransform Scalar)
  -- ^ Transformation from global diagram coordinates to output coordinates
  -> (repr style -> r -> r)
  -> (repr ann -> r -> r)
  -> (repr prim -> r)
  -> (r -> r -> r)
  -> r
renderDiagram d' t s a p l =
  let (Diagram d) = act t d'
      (finalContext, finalDiagram) = d s a p runDelayed l
      -- Tie the knot to instantiate parts of the diagram that depend on
      -- the global context.
      runDelayed dl = snd $
        unDiagram (withScaleOf dl t (_diagramContext_envelope finalContext)) s a p runDelayed l
   in finalDiagram
-}
newtype ApplicativeDiagram repr prim style ann a = ApplicativeDiagram { unApplicativeDiagram :: repr a }

deriving via (repr :: * -> *) instance Functor repr => Functor (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Applicative repr => Applicative (ApplicativeDiagram repr prim style ann)

deriving via (repr :: * -> *) instance Apply repr => Apply (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Compose repr => Compose (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Eq' a repr => Eq' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Ord' a repr => Ord' a (ApplicativeDiagram repr prim style ann)
deriving via (repr a) instance Num (repr a) => Num (ApplicativeDiagram repr prim style ann a)
deriving via (repr :: * -> *) instance Num' a repr => Num' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance LiftNum repr => LiftNum (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Fractional' a repr => Fractional' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Integral' a repr => Integral' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Enum' a repr => Enum' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Floating' a repr => Floating' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance LiftFloating repr => LiftFloating (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Real' a repr => Real' a (ApplicativeDiagram repr prim style ann)
deriving via (repr m) instance Semigroup (repr m) => Semigroup (ApplicativeDiagram repr prim style ann m)
deriving via (repr :: * -> *) instance LiftSemigroup repr => LiftSemigroup (ApplicativeDiagram repr prim style ann)
deriving via (repr m) instance Monoid (repr m) => Monoid (ApplicativeDiagram repr prim style ann m)
deriving via (repr :: * -> *) instance LiftMonoid repr => LiftMonoid (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Functor' t repr => Functor' t (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Foldable' t repr => Foldable' t (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Traversable' t repr => Traversable' t (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance LiftTraversable repr => LiftTraversable (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Applicative' t repr => Applicative' t (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance LiftApplicative repr => LiftApplicative (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance (Additive' f repr) => Additive' f (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance (Metric' f repr) => Metric' f (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance (Affine' f repr) => Affine' f (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Spatial repr => Spatial (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Envelopes repr => Envelopes (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance Traces repr => Traces (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance LinearAction' a repr => LinearAction' a (ApplicativeDiagram repr prim style ann)
deriving via (repr :: * -> *) instance AffineAction' a repr => AffineAction' a (ApplicativeDiagram repr prim style ann)

instance (Applicative repr, Envelopes repr, Traces repr) => Semigroup (Diagram repr) where
  Diagram d0 <> Diagram d1 = Diagram $ \s a p d l ->
    let (ctx0, r0) = d0 s a p d l
        (ctx1, r1) = d1 s a p d l
     in (ctx0 <> ctx1, l r0 r1)

instance
  ( AffineAction' style repr
  , AffineAction' prim repr
  , AffineAction' Envelope repr
  , AffineAction' Trace repr
  , Applicative repr
  , Traces repr
  , Envelopes repr
  , Lambda repr
  ) => AffineAction' (Diagram (ApplicativeDiagram repr prim style ann)) repr where
  actA' t = fmap $ \(Diagram d) -> Diagram $ \s a p l -> fmap (_1 %~ transformContext') $ d
    (s . ApplicativeDiagram . actA' t . unApplicativeDiagram)
    a
    (p . ApplicativeDiagram . actA' t . unApplicativeDiagram)
    l
   where
    transformContext' (DiagramContext (ApplicativeDiagram e) (ApplicativeDiagram tr)) =
     let DiagramContext e' tr' = transformContext t $ DiagramContext e tr
      in DiagramContext (ApplicativeDiagram e') (ApplicativeDiagram tr')

instance
  ( Applicative repr
  , Envelopes repr
  , Traces repr
  , Semigroup style
  , Lambda repr
  , AffineAction' style repr
  , AffineAction' prim repr
  , AffineAction' Envelope repr
  , AffineAction' Trace repr
  ) => Diagrams (ApplicativeDiagram repr prim style ann) where
  type Prim (ApplicativeDiagram repr prim style ann) = prim
  type Style (ApplicativeDiagram repr prim style ann) = style
  type Ann (ApplicativeDiagram repr prim style ann) = ann
  prim e tr p = pure $ Diagram $ \_ _ pr _ _ ->
    (DiagramContext e tr, pr p)
  delayed e tr p = pure $ Diagram $ \_ _ _ delayed' _ ->
    (DiagramContext e tr, delayed' p)
  ann x = fmap $ \(Diagram d) -> Diagram $ \s a p delayed' l -> fmap (a x) (d s a p delayed' l)
  style x = fmap $ \(Diagram d) -> Diagram $ \s -> d (s . (<> x))


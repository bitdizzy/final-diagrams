{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Core.Type where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Monoid
import Data.Set (Set)
import Linear (Additive, Metric, Conjugate)

import qualified Diagrams.Final.Core.Space.Primitive as T
import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Envelope
import Diagrams.Final.Core.Measure
import Diagrams.Final.Core.Space
import Diagrams.Final.Core.Trace

data DiagramContext repr = DiagramContext
  { _diagramContext_envelope :: repr (Envelope repr)
  , _diagramContext_trace :: repr (Trace repr)
  }

instance (Semigroup' (Envelope repr) repr, Semigroup' (Trace repr) repr) => Semigroup (DiagramContext repr) where
  DiagramContext e0 t0 <> DiagramContext e1 t1 = DiagramContext (e0 %<> e1) (t0 %<> t1)

instance (Monoid' (Envelope repr) repr, Monoid' (Trace repr) repr) => Monoid (DiagramContext repr) where
  mempty = DiagramContext mempty' mempty'

transformContext
  :: (AffineAction' Scalar (Envelope repr) repr, AffineAction' Scalar (Trace repr) repr)
  => repr (AffineTransform repr Scalar)
  -> DiagramContext repr
  -> DiagramContext repr
transformContext t (DiagramContext e tr) = DiagramContext (actA' t e) (actA' t tr)

class ( Envelopes repr, Traces repr, Scales repr
      , Monoid' style repr
      , AffineAction' Scalar style repr
      , AffineAction' Scalar prim repr
      ) => Diagrams style ann prim repr | repr -> style ann prim where
  prim :: repr (Envelope repr) -> repr (Trace repr) -> repr prim -> repr (Diagram repr style ann prim)
  delayed :: repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr style ann a)) -> repr (Diagram repr style ann a)
  ann :: repr ann -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  style :: repr style -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  -- TODO: This isn't written in the same style as other higher order DSL functions
  modifyContext :: (DiagramContext repr -> DiagramContext repr) -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  -- TODO: Bleh
  joinContext :: repr (DiagramContext repr) -> DiagramContext repr
  transformDia :: repr (AffineTransform repr Scalar) -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  envelopeDia :: repr (Diagram repr style ann prim) -> repr (Envelope repr)
  traceDia :: repr (Diagram repr style ann prim) -> repr (Trace repr)
  default prim :: (Applicative repr) => repr (Envelope repr) -> repr (Trace repr) -> repr prim -> repr (Diagram repr style ann prim)
  prim e tr p = pure $ Diagram $ \f -> (DiagramContext e tr, f $ DiaF_Prim p)
  default delayed :: (Applicative repr) => repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr style ann a)) -> repr (Diagram repr style ann a)
  delayed e tr p = pure $ Diagram $ \f -> (DiagramContext e tr, f $ DiaF_Delayed p)
  default ann :: (Functor repr) => repr ann -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  ann x = fmap $ \(Diagram d) -> Diagram \f ->
    let (ctx, r) = d f
     in (ctx, f $ DiaF_Ann x r)
  default style :: (Functor repr) => repr style -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  style x = fmap $ \(Diagram d) -> Diagram \f ->
    let (ctx, r) = d f
     in (ctx, f $ DiaF_Style x r)
  default modifyContext :: (Functor repr) => (DiagramContext repr -> DiagramContext repr) -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  modifyContext t = fmap $ \(Diagram d) -> Diagram \f ->
    let (ctx, r) = d f
     in (t ctx, r)
  default joinContext :: Monad repr => repr (DiagramContext repr) -> DiagramContext repr
  joinContext mctx = DiagramContext
    { _diagramContext_envelope = join $ fmap _diagramContext_envelope mctx
    , _diagramContext_trace = join $ fmap _diagramContext_trace mctx
    }
  default transformDia :: Functor repr => repr (AffineTransform repr Scalar) -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  transformDia tf = fmap $ \(Diagram d) -> Diagram \f ->
    let (ctx, r) = d f
     in (transformContext tf ctx, f (DiaF_Transform tf r))
  default envelopeDia :: Monad repr => repr (Diagram repr style ann prim) -> repr (Envelope repr)
  envelopeDia = join . fmap \(Diagram d) -> _diagramContext_envelope . fst $ d (\_ -> ())
  default traceDia :: Monad repr => repr (Diagram repr style ann prim) -> repr (Trace repr)
  traceDia = join . fmap \(Diagram d) -> _diagramContext_trace . fst $ d (\_ -> ())

data DiaF repr x style ann a
   = DiaF_Transform (repr (AffineTransform repr Scalar)) x
   | DiaF_Style (repr style) x
   | DiaF_Ann (repr ann) x
   | DiaF_Prim (repr a)
   | DiaF_Delayed (repr (Scaled repr (Diagram repr style ann a)))

deriving instance (Functor repr, Functor (Scaled repr), Functor (Diagram repr style ann)) => Functor (DiaF repr x style ann )

instance Diagrams style ann prim repr => Enveloped (Diagram repr style ann prim) repr where
  envelopeOf = envelopeDia

instance Diagrams style ann prim repr => Traced (Diagram repr style ann prim) repr where
  traceOf = traceDia

instance Diagrams style ann prim repr => Juxtapose (Diagram repr style ann prim) repr

-- | We can implement diagrams as trees
-- The F-algebra supplied should respect the monoid structure of its carrier
-- when it applies a transformation or style. e.g.
--     'cata (DiaF_Transform t (r <> s))'
--   ~ 'cata (DiaF_Transform t r) <> cata (DiaF_Transform t s)'
--
-- However the annotations need not (think SVG grouping) nor do context transformations
newtype Diagram repr style ann a = Diagram { unDiagram :: forall r. Monoid r => (DiaF repr r style ann a -> r) -> (DiagramContext repr, r) }

deriving instance (Functor repr, Functor (Scaled repr), Functor (Diagram repr style ann)) => Functor (Diagram repr style ann)

instance (Envelopes repr, Traces repr) => Semigroup (Diagram repr style ann a) where
  Diagram d0 <> Diagram d1 = Diagram \cata -> d0 cata <> d1 cata

instance (Envelopes repr, Traces repr) => Monoid (Diagram repr style ann a) where
  mempty = Diagram \_ -> mempty

instance
  ( Diagrams style ann prim repr
  ) => AffineAction' Scalar (Diagram repr style ann a) repr where
  actA' = transformDia

data DiagramFold repr style ann a x = DiagramFold
  { _diagramFold_transform :: repr (AffineTransform repr Scalar) -> x -> x
  , _diagramFold_style :: repr style -> x -> x
  , _diagramFold_ann :: repr ann -> x -> x
  , _diagramFold_context :: (DiagramContext repr -> DiagramContext repr) -> x -> x
  , _diagramFold_prim :: repr a -> x
  }

foldPair :: DiagramFold repr style ann x a -> DiagramFold repr style ann x b -> DiagramFold repr style ann x (a, b)
foldPair d1 d2 = DiagramFold
  { _diagramFold_transform = \t -> _diagramFold_transform d1 t *** _diagramFold_transform d2 t
  , _diagramFold_style = \s -> _diagramFold_style d1 s *** _diagramFold_style d2 s
  , _diagramFold_ann = \a -> _diagramFold_ann d1 a *** _diagramFold_ann d2 a
  , _diagramFold_context = \f -> _diagramFold_context d1 f *** _diagramFold_context d2 f
  , _diagramFold_prim = _diagramFold_prim d1 &&& _diagramFold_prim d2
  }

foldDiagram
  :: (Monad repr, Lambda repr, Monoid r, Diagrams style ann prim repr, AffineAction' Scalar a repr)
  => repr (Diagram repr style ann a)
  -- ^ The representation of our diagram
  -> repr (AffineTransform repr Scalar)
  -- ^ The top-level transformation from diagram coordinates to output coordinates
  -> DiagramContext repr
  -- ^ The top-level diagram context for determining scales
  -> DiagramFold repr style ann a r
  -- ^ How to process a concrete tree with no delayed leaves
  -> (repr r -> r)
  -- ^ How to incorporate the results of delayed leaves
  -> repr (DiagramContext repr, r)
foldDiagram d' t0 finalContext foldResult reprAlgebra  =
  flip fmap (actA' t0 d') $ \(Diagram d) ->
    let cata = \case
          DiaF_Transform tf r -> _diagramFold_transform foldResult tf r
          DiaF_Style st r -> _diagramFold_style foldResult st r
          DiaF_Ann an r -> _diagramFold_ann foldResult an r
          DiaF_Prim p -> _diagramFold_prim foldResult p
          DiaF_Delayed dl ->
            let dl' = flip fmap (withScaleOf dl t0 (_diagramContext_envelope finalContext)) $ \(Diagram x) -> x cata
             in reprAlgebra (fmap snd dl')
     in d cata

-- TODO: Trash?
newtype MonadicDiagram repr prim style ann a = MonadicDiagram { unMonadicDiagram :: repr a }
  deriving (Functor, Applicative, Monad)

deriving via (Ap repr a) instance (Applicative repr, Num a) => Num (MonadicDiagram repr prim style ann a)
instance (Applicative repr, Fractional a) => Fractional (MonadicDiagram repr prim style ann a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)

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
instance (Functor f, Monad repr) => Functor' (T1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Applicative f, Monad repr) => Applicative' (T1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Foldable f, Monad repr) => Foldable' (T1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Additive f, Monad repr) => Additive' (T1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance (Metric f, Monad repr) => Metric' (T1 (MonadicDiagram repr prim style ann) f) (MonadicDiagram repr prim style ann)
instance Monad repr => Affine' (Point (MonadicDiagram repr prim style ann)) (MonadicDiagram repr prim style ann) where
instance (forall x. Num x => T.LinearAction x (f x), Num n, Functor f, Monad repr) => LinearAction' n (T1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance (forall x. Num x => T.AffineAction x (f x), Num n, Functor f, Monad repr) => AffineAction' n (T1 (MonadicDiagram repr prim style ann) f n) (MonadicDiagram repr prim style ann)
instance Monad repr => LiftBool (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMax (MonadicDiagram repr prim style ann)
instance Monad repr => LiftEndo (MonadicDiagram repr prim style ann)
instance Monad repr => LiftOrdering (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMaybe (MonadicDiagram repr prim style ann)
instance Monad repr => LiftList (MonadicDiagram repr prim style ann)
instance Monad repr => LiftSet (MonadicDiagram repr prim style ann)

instance Monad repr => Semigroup' (LinearTransform (MonadicDiagram repr prim style ann) Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (LinearTransform (MonadicDiagram repr prim style ann) Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Semigroup' (AffineTransform (MonadicDiagram repr prim style ann) Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (AffineTransform (MonadicDiagram repr prim style ann) Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Semigroup' (Set Scalar) (MonadicDiagram repr prim style ann)
instance Monad repr => Monoid' (Set Scalar) (MonadicDiagram repr prim style ann)

instance (Monad repr, T.IsDiffOf T.Point T.Vector, Semigroup a) => Semigroup' (Diagram (MonadicDiagram repr prim style ann) style ann a) (MonadicDiagram repr prim style ann)

instance Monad repr => Val Scalar (MonadicDiagram repr prim style ann)
instance Monad repr => Val1 T.Vector (MonadicDiagram repr prim style ann)
instance Monad repr => Val1 T.Point (MonadicDiagram repr prim style ann)
instance Monad repr => Val1 T.LinearTransform (MonadicDiagram repr prim style ann)
instance Monad repr => Val1 T.AffineTransform (MonadicDiagram repr prim style ann)
instance Monad repr => LiftRepresentable T.Vector (MonadicDiagram repr prim style ann)
instance Monad repr => LiftRepresentable T.Point (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Spatial (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Envelopes (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Scales (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Traces (MonadicDiagram repr prim style ann)

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Core.Type where

import Control.Arrow
import Control.Monad
import Data.Kind
import Data.Monoid
import Data.Set (Set)
import Linear (Additive, Metric, Conjugate)
import Linear.Affine (Affine(type Diff))

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

joinContext :: Monad repr => repr (DiagramContext repr) -> DiagramContext repr
joinContext mctx = DiagramContext
  { _diagramContext_envelope = join $ fmap _diagramContext_envelope mctx
  , _diagramContext_trace = join $ fmap _diagramContext_trace mctx
  }

class ( Envelopes repr, Traces repr, Scales repr
      , Monoid' (Style repr) repr
      , AffineAction' Scalar (Style repr) repr
      , AffineAction' Scalar (Prim repr) repr
      ) => Diagrams repr where
  type Diagram repr :: Type -> Type
  type Diagram repr = DefaultDiagram repr
  type Prim repr :: Type
  type Style repr :: Type
  type Ann repr :: Type
  prim :: repr (Envelope repr) -> repr (Trace repr) -> repr (Prim repr) -> repr (Diagram repr (Prim repr))
  delayed :: repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr a)) -> repr (Diagram repr a)
  ann :: repr (Ann repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  style :: repr (Style repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  -- TODO: This isn't written in the same style as other higher order DSL functions
  modifyContext :: (DiagramContext repr -> DiagramContext repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  -- TODO: Bleh
  default prim :: (Applicative repr, Diagram repr ~ DefaultDiagram repr) => repr (Envelope repr) -> repr (Trace repr) -> repr (Prim repr) -> repr (Diagram repr (Prim repr))
  prim e tr p = pure $ DefaultDiagram ($ DefaultDiaF_Prim (DiagramContext e tr) p)
  default delayed :: (Applicative repr, Diagram repr ~ DefaultDiagram repr) => repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr a)) -> repr (Diagram repr a)
  delayed e tr p = pure $ DefaultDiagram ($ DefaultDiaF_Delayed (DiagramContext e tr) p)
  default ann :: (Functor repr, Diagram repr ~ DefaultDiagram repr) => repr (Ann repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  ann x = fmap $ \(DefaultDiagram d) -> DefaultDiagram \cata -> cata (DefaultDiaF_Ann x (d cata))
  default style :: (Functor repr, Diagram repr ~ DefaultDiagram repr) => repr (Style repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  style x = fmap $ \(DefaultDiagram d) -> DefaultDiagram \cata -> cata (DefaultDiaF_Style x (d cata))
  default modifyContext :: (Functor repr, Diagram repr ~ DefaultDiagram repr) => (DiagramContext repr -> DiagramContext repr) -> repr (Diagram repr a) -> repr (Diagram repr a)
  modifyContext f = fmap $ \(DefaultDiagram d) -> DefaultDiagram \cata -> cata (DefaultDiaF_Context f (d cata))

data DefaultDiaF repr x a
   = DefaultDiaF_Transform (repr (AffineTransform repr Scalar)) x
   | DefaultDiaF_Style (repr (Style repr)) x
   | DefaultDiaF_Ann (repr (Ann repr)) x
   | DefaultDiaF_Context (DiagramContext repr -> DiagramContext repr) x
   | DefaultDiaF_Prim (DiagramContext repr) (repr a)
   | DefaultDiaF_Delayed (DiagramContext repr) (repr (Scaled repr (Diagram repr a)))

deriving instance (Functor repr, Functor (Scaled repr), Functor (Diagram repr)) => Functor (DefaultDiaF repr x)

-- | We can implement diagrams as trees
-- The F-algebra supplied should respect the monoid structure of its carrier
-- when it applies a transformation or style. e.g.
--     'cata (DefaultDiaF_Transform t (r <> s))'
--   ~ 'cata (DefaultDiaF_Transform t r) <> cata (DefaultDiaF_Transform t s)'
--
-- However the annotations need not (think SVG grouping) nor do context transformations
newtype DefaultDiagram repr a = DefaultDiagram { unDefaultDiagram :: forall r. Monoid r => (DefaultDiaF repr r a -> r) -> r }

deriving instance (Functor repr, Functor (Scaled repr), Functor (Diagram repr)) => Functor (DefaultDiagram repr)

instance Semigroup (DefaultDiagram repr a) where
  DefaultDiagram d0 <> DefaultDiagram d1 = DefaultDiagram \cata -> d0 cata <> d1 cata

instance Monoid (DefaultDiagram repr a) where
  mempty = DefaultDiagram \_ -> mempty

instance
  ( AffineAction' Scalar (Style repr) repr
  , AffineAction' Scalar a repr
  , Monad repr
  , Envelopes repr
  , Traces repr
  , Diagram repr ~ DefaultDiagram repr
  ) => AffineAction' Scalar (DefaultDiagram repr a) repr where
  actA' tf = fmap $ \(DefaultDiagram d) -> DefaultDiagram \cata -> cata $ DefaultDiaF_Transform tf (d cata)

data DiagramFold repr a x = DiagramFold
  { _diagramFold_transform :: repr (AffineTransform repr Scalar) -> x -> x
  , _diagramFold_style :: repr (Style repr) -> x -> x
  , _diagramFold_ann :: repr (Ann repr) -> x -> x
  , _diagramFold_context :: (DiagramContext repr -> DiagramContext repr) -> x -> x
  , _diagramFold_prim :: repr a -> x
  }

foldContext :: Diagrams repr => DiagramFold repr a (DiagramContext repr)
foldContext = DiagramFold
  { _diagramFold_transform = transformContext
  , _diagramFold_style = const id
  , _diagramFold_ann = const id
  , _diagramFold_context = id
  , _diagramFold_prim = const mempty
  }

foldPair :: DiagramFold repr x a -> DiagramFold repr x b -> DiagramFold repr x (a, b)
foldPair d1 d2 = DiagramFold
  { _diagramFold_transform = \t -> _diagramFold_transform d1 t *** _diagramFold_transform d2 t
  , _diagramFold_style = \s -> _diagramFold_style d1 s *** _diagramFold_style d2 s
  , _diagramFold_ann = \a -> _diagramFold_ann d1 a *** _diagramFold_ann d2 a
  , _diagramFold_context = \f -> _diagramFold_context d1 f *** _diagramFold_context d2 f
  , _diagramFold_prim = _diagramFold_prim d1 &&& _diagramFold_prim d2
  }

foldDiagram
  :: (Monad repr, Lambda repr, Monoid r, Diagrams repr, Diagram repr ~ DefaultDiagram repr, AffineAction' Scalar a repr)
  => repr (Diagram repr a)
  -- ^ The representation of our diagram
  -> repr (AffineTransform repr Scalar)
  -- ^ The top-level transformation from diagram coordinates to output coordinates
  -> DiagramContext repr
  -- ^ The top-level diagram context for determining scales
  -> DiagramFold repr a r
  -- ^ How to process a concrete tree with no delayed leaves
  -> (repr r -> r)
  -- ^ How to incorporate the results of delayed leaves
  -> repr r
foldDiagram d' t0 finalContext foldResult reprAlgebra  =
  flip fmap (actA' t0 d') $ \(DefaultDiagram d) ->
    let cata = \case
          DefaultDiaF_Transform tf r -> _diagramFold_transform foldResult tf r
          DefaultDiaF_Style st r -> _diagramFold_style foldResult st r
          DefaultDiaF_Ann an r -> _diagramFold_ann foldResult an r
          DefaultDiaF_Context f r -> _diagramFold_context foldResult f r
          DefaultDiaF_Prim ctx p -> _diagramFold_context foldResult (\_ -> ctx) $ _diagramFold_prim foldResult p
          DefaultDiaF_Delayed ctx dl ->
            let dl' = flip fmap (withScaleOf dl t0 (_diagramContext_envelope finalContext)) $ \(DefaultDiagram x) -> x cata
             in _diagramFold_context foldResult (\_ -> ctx) $ reprAlgebra dl'
     in d cata

-- TODO: Trash?
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

instance (Monad repr, T.IsDiffOf T.Point T.Vector, Semigroup a) => Semigroup' (DefaultDiagram (MonadicDiagram repr prim style ann) a) (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Spatial (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Envelopes (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Scales (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Traces (MonadicDiagram repr prim style ann)

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
import Diagrams.Final.Core.Style
import Diagrams.Final.Core.Trace

data DiagramContext repr = DiagramContext
  { _diagramContext_envelope :: repr (Envelope repr)
  , _diagramContext_trace :: repr (Trace repr)
  }

instance (Semigroup' repr (Envelope repr), Semigroup' repr (Trace repr)) => Semigroup (DiagramContext repr) where
  DiagramContext e0 t0 <> DiagramContext e1 t1 = DiagramContext (e0 %<> e1) (t0 %<> t1)

instance (Monoid' repr (Envelope repr), Monoid' repr (Trace repr)) => Monoid (DiagramContext repr) where
  mempty = DiagramContext mempty' mempty'

transformContext
  :: (AffineAction' repr Scalar (Envelope repr), AffineAction' repr Scalar (Trace repr))
  => repr (AffineTransform repr Scalar)
  -> DiagramContext repr
  -> DiagramContext repr
transformContext t (DiagramContext e tr) = DiagramContext (actA' t e) (actA' t tr)

class ( Envelopes repr, Traces repr, Scales repr
      , Monoid' repr style
      , Style repr style
      , AffineAction' repr Scalar prim
      ) => Diagrams repr style ann prim | repr -> style ann prim where
  prim :: repr (Envelope repr) -> repr (Trace repr) -> repr prim -> repr (Diagram repr style ann prim)
  delayed :: repr (Envelope repr) -> repr (Trace repr) -> repr (Scaled repr (Diagram repr style ann a)) -> repr (Diagram repr style ann a)
  ann :: repr ann -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  styleDia :: repr style -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
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
  default styleDia :: (Functor repr) => repr style -> repr (Diagram repr style ann a) -> repr (Diagram repr style ann a)
  styleDia x = fmap $ \(Diagram d) -> Diagram \f ->
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

instance Diagrams repr style ann prim => Enveloped repr (Diagram repr style ann prim) where
  envelopeOf = envelopeDia

instance Diagrams repr style ann prim => Traced repr (Diagram repr style ann prim) where
  traceOf = traceDia

instance Diagrams repr style ann prim => Juxtapose repr (Diagram repr style ann prim)

instance Diagrams repr style ann prim => Styled repr style (Diagram repr style ann prim) where
  style' = styleDia

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
  ( Diagrams repr style ann prim
  ) => AffineAction' repr Scalar (Diagram repr style ann a) where
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
  :: (Monad repr, Lambda repr, Monoid r, Diagrams repr style ann prim, AffineAction' repr Scalar a)
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

instance (Applicative repr, Floating a) => Floating (MonadicDiagram repr prim style ann a) where
  pi = pure pi
  exp = fmap exp
  log = fmap log
  sin = fmap sin
  cos = fmap cos
  asin = fmap asin
  acos = fmap acos
  atan = fmap atan
  sinh = fmap sinh
  cosh = fmap cosh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh

instance Monad repr => Lambda (MonadicDiagram repr prim style ann)
instance Monad repr => Proj1 (MonadicDiagram repr prim style ann) (a, b) a
instance Monad repr => Proj2 (MonadicDiagram repr prim style ann) (a, b) b
instance Monad repr => Proj1 (MonadicDiagram repr prim style ann) (a, b, c) a
instance Monad repr => Proj2 (MonadicDiagram repr prim style ann) (a, b, c) b
instance Monad repr => Proj3 (MonadicDiagram repr prim style ann) (a, b, c) c
instance Monad repr => Tuple2 (MonadicDiagram repr prim style ann)
instance Monad repr => Tuple3 (MonadicDiagram repr prim style ann)
instance (Eq n, Monad repr) => Eq' (MonadicDiagram repr prim style ann) n
instance (Ord n, Monad repr) => Ord' (MonadicDiagram repr prim style ann) n
instance (Num n, Monad repr) => Num' (MonadicDiagram repr prim style ann) n
instance (Conjugate n, Monad repr) => Conjugate' (MonadicDiagram repr prim style ann) n
instance (Real n, Monad repr) => Real' (MonadicDiagram repr prim style ann) n
instance (Enum n, Monad repr) => Enum' (MonadicDiagram repr prim style ann) n
instance (Integral n, Monad repr) => Integral' (MonadicDiagram repr prim style ann) n
instance (Fractional n, Monad repr) => Fractional' (MonadicDiagram repr prim style ann) n
instance (Floating n, Monad repr) => Floating' (MonadicDiagram repr prim style ann) n
instance (RealFrac n, Monad repr) => RealFrac' (MonadicDiagram repr prim style ann) n
instance (Functor f, Monad repr) => Functor' (MonadicDiagram repr prim style ann) (T1 (MonadicDiagram repr prim style ann) f)
instance (Applicative f, Monad repr) => Applicative' (MonadicDiagram repr prim style ann) (T1 (MonadicDiagram repr prim style ann) f)
instance (Foldable f, Monad repr) => Foldable' (MonadicDiagram repr prim style ann) (T1 (MonadicDiagram repr prim style ann) f)
instance (Additive f, Monad repr) => Additive' (MonadicDiagram repr prim style ann) (T1 (MonadicDiagram repr prim style ann) f)
instance (Metric f, Monad repr) => Metric' (MonadicDiagram repr prim style ann) (T1 (MonadicDiagram repr prim style ann) f)
instance Monad repr => Affine' (MonadicDiagram repr prim style ann) (Point (MonadicDiagram repr prim style ann))
instance (forall x. Num x => T.LinearAction x (f x), Num n, Functor f, Monad repr) => LinearAction' (MonadicDiagram repr prim style ann) n (T1 (MonadicDiagram repr prim style ann) f n)
instance (forall x. Num x => T.AffineAction x (f x), Num n, Functor f, Monad repr) => AffineAction' (MonadicDiagram repr prim style ann) n (T1 (MonadicDiagram repr prim style ann) f n)
instance Monad repr => LiftBool (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMax (MonadicDiagram repr prim style ann)
instance Monad repr => LiftEndo (MonadicDiagram repr prim style ann)
instance Monad repr => LiftOrdering (MonadicDiagram repr prim style ann)
instance Monad repr => LiftMaybe (MonadicDiagram repr prim style ann)
instance Monad repr => LiftList (MonadicDiagram repr prim style ann)
instance Monad repr => LiftSet (MonadicDiagram repr prim style ann)

instance Monad repr => Semigroup' (MonadicDiagram repr prim style ann) (LinearTransform (MonadicDiagram repr prim style ann) Scalar)
instance Monad repr => Monoid' (MonadicDiagram repr prim style ann) (LinearTransform (MonadicDiagram repr prim style ann) Scalar)
instance Monad repr => Semigroup' (MonadicDiagram repr prim style ann) (AffineTransform (MonadicDiagram repr prim style ann) Scalar)
instance Monad repr => Monoid' (MonadicDiagram repr prim style ann) (AffineTransform (MonadicDiagram repr prim style ann) Scalar)
instance Monad repr => Semigroup' (MonadicDiagram repr prim style ann) (Set Scalar)
instance Monad repr => Monoid' (MonadicDiagram repr prim style ann) (Set Scalar)

instance (Monad repr, T.IsDiffOf T.Point T.Vector, Semigroup a) => Semigroup' (MonadicDiagram repr prim style ann) (Diagram (MonadicDiagram repr prim style ann) style ann a)

instance Monad repr => Val (MonadicDiagram repr prim style ann) Scalar
instance Monad repr => Val1 (MonadicDiagram repr prim style ann) T.Vector
instance Monad repr => Val1 (MonadicDiagram repr prim style ann) T.Point
instance Monad repr => Val1 (MonadicDiagram repr prim style ann) T.LinearTransform
instance Monad repr => Val1 (MonadicDiagram repr prim style ann) T.AffineTransform
instance Monad repr => LiftRepresentable (MonadicDiagram repr prim style ann) T.Vector
instance Monad repr => LiftRepresentable (MonadicDiagram repr prim style ann) T.Point

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Spatial (MonadicDiagram repr prim style ann)

instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Envelopes (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Scales (MonadicDiagram repr prim style ann)
instance (T.IsDiffOf T.Point T.Vector, Monad repr) => Traces (MonadicDiagram repr prim style ann)

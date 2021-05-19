{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Diagrams.Final.Core.Trace where

import Control.Lens
import Data.Set (Set)

import Diagrams.Final.Core.Base
import Diagrams.Final.Core.Space

newtype Trace repr = Trace { unTrace :: Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar)) }

instance Wrapped (Trace repr) where
  type Unwrapped (Trace repr) = Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))
  _Wrapped' = iso unTrace Trace

instance Rewrapped (Trace repr) (Trace repr)

class (Spatial repr, Monoid' (Set Scalar) repr, AffineAction' Scalar (Trace repr) repr, Semigroup' (Trace repr) repr, Monoid' (Trace repr) repr) => Traces repr where
  emptyTrace :: repr (Trace repr)
  toTrace :: repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))) -> repr (Trace repr)
  appTrace :: repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set Scalar)
  default emptyTrace :: (Applicative repr, Lambda repr) => repr (Trace repr)
  emptyTrace = toTrace $ lam $ \_ -> lam $ \_ -> mempty' -- pure mempty
  default toTrace :: (Functor repr) => repr (Arr repr (Point repr Scalar) (Arr repr (Vector repr Scalar) (Set Scalar))) -> repr (Trace repr)
  toTrace = fmap Trace
  default appTrace :: (Functor repr, Lambda repr) => repr (Trace repr) -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Set Scalar)
  appTrace f p v = fmap unTrace f %$ p %$ v

instance Semigroup' (Set Scalar) Identity
instance Monoid' (Set Scalar) Identity
instance Traces Identity

instance (Lambda repr, Traces repr) => AffineAction' Scalar (Trace repr) repr where
  actA' a t =
    let_ (linearOf a) $ \l ->
      toTrace $ lam $ \p -> lam $ \v ->
        appTrace t (actA' (inverseAffine a) p) (actL' (inverseLinear l) v)

instance (Lambda repr, Traces repr) => Semigroup' (Trace repr) repr where
  t1 %<> t2 = toTrace $ lam $ \p -> lam $ \v -> appTrace t1 p v %<> appTrace t2 p v

instance (Lambda repr, Traces repr) => Monoid' (Trace repr) repr where
  mempty' = emptyTrace

class Traced a repr where
  traceOf :: repr a -> repr (Trace repr)

instance Traced (Trace repr) repr where
  traceOf = id

instance (Lambda repr, Traces repr) => Traced (Point repr n) repr where
  traceOf = const mempty'

instance (Lambda repr, Traces repr, Traced a repr, Traced b repr) => Traced (a, b) repr where
  traceOf xy = traceOf (pi1' xy) %<> traceOf (pi2' xy)

instance (Lambda repr, Traces repr, LiftList repr, Traced a repr) => Traced (List' repr a) repr where
  traceOf = foldMap' (lam traceOf)

instance (Lambda repr, Traces repr, LiftSet repr, Traced a repr, Ord' a repr) => Traced (Set a) repr where
  traceOf = traceOf . toAscList'

traceV :: (Traces repr, Traced a repr) => repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Vector repr Scalar))
traceV p v a = foldr' (toAscList' $ (appTrace (traceOf a) p v)) nothing' $ lam $ \x -> lam $ \_ -> just' (x %*^ v)

traceP :: (Traces repr, Traced a repr) => repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Point repr Scalar))
traceP p v a = lam (p %.+^) <%$> traceV p v a

maxTraceV :: (Traces repr, Traced a repr) => repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Vector repr Scalar))
maxTraceV p = traceV p . negated'

maxTraceP :: (Traces repr, Traced a repr) => repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr a -> repr (Maybe' repr (Point repr Scalar))
maxTraceP p v a = lam (p %.+^) <%$> maxTraceV p v a

rayTraceOf :: (Traces repr, Traced a repr) => repr a -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (List' repr Scalar)
rayTraceOf a p v = dropWhile' (lam (%< 0)) $ toAscList' $ appTrace (traceOf a) p v

rayTraceOfV :: (Traces repr, Traced a repr) => repr a -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Maybe' repr (Vector repr Scalar))
rayTraceOfV a p v = foldr' (rayTraceOf a p v) nothing' $ lam $ \x -> lam $ \_ -> just' (x %*^ v)

rayTraceOfP :: (Traces repr, Traced a repr) => repr a -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Maybe' repr (Point repr Scalar))
rayTraceOfP a p v = lam (p %.+^) <%$> rayTraceOfV a p v

rayTraceOfMaxV :: (Traces repr, Traced a repr) => repr a -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Maybe' repr (Vector repr Scalar))
rayTraceOfMaxV a p v = lam (%*^ v) <%$> last' (rayTraceOf a p v)

rayTraceOfMaxP :: (Traces repr, Traced a repr) => repr a -> repr (Point repr Scalar) -> repr (Vector repr Scalar) -> repr (Maybe' repr (Point repr Scalar))
rayTraceOfMaxP a p v = lam (p %.+^) <%$> rayTraceOfMaxV a p v

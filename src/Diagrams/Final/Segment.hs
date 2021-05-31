{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Segment where

import Diagrams.Final.Core
import Diagrams.Final.Parametric
import Diagrams.Final.Solve

data SegmentEnd = Open | Closed

data Offset repr c where
  Offset_Open :: Offset repr 'Open
  Offset_Closed :: repr (Vector repr Scalar) -> Offset repr 'Closed

class Spatial repr => Offsets repr where
  offset_open :: repr (Offset repr 'Open)
  offset_closed :: repr (Vector repr Scalar) -> repr (Offset repr 'Closed)
  -- TODO: Review other eliminators and make them manifestly more like a bind?
  offset' :: repr (Offset repr c) -> (Offset repr c -> repr r) -> repr r
  offset'' :: repr (Offset repr c) -> (forall c'. Offset repr c' -> repr (r c')) -> repr (r c)
  default offset_open :: Applicative repr => repr (Offset repr 'Open)
  offset_open = pure Offset_Open
  default offset_closed :: Applicative repr => repr (Vector repr Scalar) -> repr (Offset repr 'Closed)
  offset_closed = pure . Offset_Closed
  default offset' :: Monad repr => repr (Offset repr c) -> (Offset repr c -> repr r) -> repr r
  offset' = (>>=)
  default offset'' :: Monad repr => repr (Offset repr c) -> (forall c'. Offset repr c' -> repr (r c')) -> repr (r c)
  offset'' = (>>=)

instance (Spatial repr, Offsets repr) => LinearAction' repr Scalar (Offset repr c) where
  actL' t o = offset'' o $ \case
    Offset_Open -> offset_open
    Offset_Closed v -> offset_closed $ actL' t v

data Segment repr c
   = Linear (repr (Offset repr c))
   | Cubic (repr (Vector repr Scalar)) (repr (Vector repr Scalar)) (repr (Offset repr c))

class Offsets repr => Segments repr where
  linearS :: repr (Offset repr c) -> repr (Segment repr c)
  cubicS :: repr (Vector repr Scalar) -> repr (Vector repr Scalar) -> repr (Offset repr c) -> repr (Segment repr c)
  segment' :: repr (Segment repr c) -> (Segment repr c -> repr r) -> repr r
  segment'' :: repr (Segment repr c) -> (forall c'. Segment repr c' -> repr (r c')) -> repr (r c)
  default linearS :: Applicative repr => repr (Offset repr c) -> repr (Segment repr c)
  linearS = pure . Linear
  default cubicS :: Applicative repr => repr (Vector repr Scalar) -> repr (Vector repr Scalar) -> repr (Offset repr c) -> repr (Segment repr c)
  cubicS c1 c2 e = pure $ Cubic c1 c2 e
  default segment' :: Monad repr => repr (Segment repr c) -> (Segment repr c -> repr r) -> repr r
  segment' = (>>=)
  default segment'' :: Monad repr => repr (Segment repr c) -> (forall c'. Segment repr c' -> repr (r c')) -> repr (r c)
  segment'' = (>>=)

-- TODO: Switch to external function arguments in most places
mapSegmentVectors
  :: forall repr c. Segments repr
  => (repr (Vector repr Scalar) -> repr (Vector repr Scalar))
  -> repr (Segment repr c)
  -> repr (Segment repr c)
mapSegmentVectors f s = segment'' s $ \case
  Linear o -> linearS $ mapOffset o
  Cubic c1 c2 o -> cubicS
    (f c1)
    (f c2)
    (mapOffset o)
 where
  mapOffset :: repr (Offset repr x) -> repr (Offset repr x)
  mapOffset o = offset'' o $ \case
    Offset_Open -> offset_open
    Offset_Closed v -> offset_closed (f v)

instance Segments repr => LinearAction' repr Scalar (Segment repr c) where
  actL' t = mapSegmentVectors (actL' t)

straight :: Segments repr => repr (Vector repr Scalar) -> repr (Segment repr 'Closed)
straight = linearS . offset_closed

bezier3
  :: Segments repr
  => repr (Vector repr Scalar)
  -> repr (Vector repr Scalar)
  -> repr (Vector repr Scalar)
  -> repr (Segment repr 'Closed)
bezier3 c1 c2 x = cubicS c1 c2 (offset_closed x)

instance Segments repr => Parametric repr (Segment repr 'Closed) Scalar (Vector repr Scalar) where
  type PDom (Segment repr 'Closed) = Scalar
  type PCod (Segment repr 'Closed) = Vector repr Scalar
  atParam s t = segment' s $ \case
    Linear o -> offset' o $ \case
      Offset_Closed v -> t %*^ v
    Cubic c1 c2 o ->
      let t' = 1 %- t
       in offset' o \case
            (Offset_Closed v) -> (3 %* t' %* t' %* t) %*^ c1
                            %^+^ (3 %* t' %* t %* t) %*^ c2
                            %^+^ (t %* t %* t) %*^ v

instance Segments repr => DomainBounds repr (Segment repr 'Closed) where
  domainLower _ = 0
  domainUpper _ = 1
  evalAtLower _ = zero'
  evalAtUpper = offsetS

offsetS :: Segments repr => repr (Segment repr 'Closed) -> repr (Vector repr Scalar)
offsetS s = segment' s $ \case
  Linear o -> offset' o $ \case
    Offset_Closed v -> v
  Cubic _ _ o -> offset' o $ \case
    Offset_Closed v -> v

openLinear :: Segments repr => repr (Segment repr 'Open)
openLinear = linearS offset_open

openCubic
  :: Segments repr
  => repr (Vector repr Scalar)
  -> repr (Vector repr Scalar)
  -> repr (Segment repr 'Open)
openCubic v1 v2 = cubicS v1 v2 offset_open

instance (Envelopes repr, Segments repr) => Enveloped repr (Segment repr 'Closed) where
  envelopeOf s = envelope $ lam $ \u -> segment' s $ \case
    Linear _ -> max' ((s `atParam` 0) `dot'` u) ((s `atParam` 1) `dot'` u) %/ quadrance' u
    Cubic c1 c2 o' -> offset' o' $ \case
      Offset_Closed v2 ->
        let test :: repr Scalar -> repr Scalar
            test t = s `atParam` t `dot'` u %/ quadrance' u
            extrema = quadForm
              (3 %* ((3 %*^ c1 %^-^ 3 %*^ c2 %^+^ v2) `dot'` u))
              (6 %* (((-2) %*^ c1 %^+^ c2) `dot'` u))
              ((3 %*^ c1) `dot'` u)
            candidates = maximum' $ fmap' (lam test) $
              (0 `cons'` (1 `cons'` maybe' extrema nil' (lam $ filter' \x -> x %> 0 %&& x %< 1)))
         in maybe' candidates (test 0) id'

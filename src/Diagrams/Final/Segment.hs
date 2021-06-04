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
import qualified Diagrams.Final.Interval as I
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

instance Offsets repr => LinearAction' repr Scalar (Offset repr c) where
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
      let t' = num 1 %- t
       in offset' o \case
            (Offset_Closed v) -> (num 3 %* t' %* t' %* t) %*^ c1
                            %^+^ (num 3 %* t' %* t %* t) %*^ c2
                            %^+^ (t %* t %* t) %*^ v

instance Segments repr => DomainBounds repr (Segment repr 'Closed) where
  domainLower _ = num 0
  domainUpper _ = num 1
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
  envelopeOf s = envelope $ lam \u -> segment' s \case
    Linear _ -> max' ((s `atParam` num 0) `dot'` u) ((s `atParam` num 1) `dot'` u) %/ quadrance' u
    Cubic c1 c2 o' -> offset' o' $ \case
      Offset_Closed v2 ->
        let test :: repr Scalar -> repr Scalar
            test t = s `atParam` t `dot'` u %/ quadrance' u
            extrema = quadForm
              (num 3 %* ((num 3 %*^ c1 %^-^ num 3 %*^ c2 %^+^ v2) `dot'` u))
              (num 6 %* ((num (-2) %*^ c1 %^+^ c2) `dot'` u))
              ((num 3 %*^ c1) `dot'` u)
            candidates = maximum' $ fmap' (lam test) $
              (num 0 `cons'` (num 1 `cons'` maybe' extrema nil' (lam $ filter' \x -> x %> num 0 %&& x %< num 1)))
         in maybe' candidates (test (num 0)) id'

instance Segments repr => Sectionable repr (Segment repr 'Closed) where
  splitAtParam s t = segment' s \case
    Linear o' -> offset' o' \case
      Offset_Closed v2 ->
        let p = lerp' t v2 zero'
            left = straight p
            right = straight (v2 %^-^ p)
         in tup2' left right
    Cubic c1 c2 o' -> offset' o' \case
      Offset_Closed v2 ->
        let p = lerp' t c2 c1
            a = lerp' t c1 zero'
            b = lerp' t p a
            d = lerp' t v2 c2
            c = lerp' t d p
            e = lerp' t c b
         in tup2' (bezier3 a b e) (bezier3 (c %^-^ e) (d %^-^ e) (v2 %^-^ e))
  reverseDomain = reverseSegment

reverseSegment :: Segments repr => repr (Segment repr 'Closed) -> repr (Segment repr 'Closed)
reverseSegment s = segment' s \case
  Linear o' -> offset' o' \case
    Offset_Closed v2 -> straight (negated' v2)
  Cubic c1 c2 o' -> offset' o' \case
    Offset_Closed v2 -> bezier3 (c2 %^-^ v2) (c1 %^-^ v2) (negated' v2)

-- TODO: Replace this stuff with more robust quadrature
instance (I.LiftInterval repr, Segments repr) => HasArcLength repr (Segment repr 'Closed) where
  arcLengthBounded m s = segment' s \case
    Linear o' -> offset' o' \case
      Offset_Closed v2 -> I.singleton' $ norm' v2
    Cubic c1 c2 o' -> offset' o' \case
      Offset_Closed v2 ->
        let lb = norm' v2
            ub = sum' (fmap' (lam norm') $ val1 [c1, c2 %^-^ c1, v2 %^-^ c2])
            (l, r) = untup2 $ s `splitAtParam` (fnum 0.5)
         in if' (ub %- lb %< m) (lb I.%... ub) $ arcLengthBounded (m %/ num 2) l %+ arcLengthBounded (m %/ num 2) r
  arcLengthToParam m s len = if' (arcLength m s %== num 0) (fnum 0.5) $ segment' s $ \case
    Linear _ -> len %/ arcLength m s
    Cubic _ _ _ -> if' (len `I.member'` ((negate' m %/ num 2) I.%... (m %/ num 2))) (num 0) $
      if' (len %< num 0) (negate' $ arcLengthToParam m (pi1' (splitAtParam s (num (-1)))) (negate' len)) $ let_ (s `splitAtParam` fnum 0.5) $ \lr ->
        let (l, r) = untup2 lr
         in let_ (arcLengthBounded (m %/ num 10) l) \llen -> let_ (arcLengthBounded m s) $ \slen ->
              if' (len `I.member'` slen) (num 1) $ if' (len %> I.sup' slen) (num 2 %* arcLengthToParam m (pi1' (splitAtParam s (num 2))) len) $
                if' (len %< I.sup' llen) ((%* fnum 0.5) $ arcLengthToParam m l len) $
                  (%+ fnum 0.5) . (%* fnum 0.5) $ arcLengthToParam (num 9 %* m %/ num 10) r (len %- I.midpoint' llen)

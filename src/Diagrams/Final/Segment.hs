{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Data.Functor.Identity

import Diagrams.Final.Core
import qualified Diagrams.Final.Interval as I
import Diagrams.Final.Located
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

instance Offsets Identity

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

instance Segments Identity

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

instance Segments repr => EndValues repr (Segment repr 'Closed) where
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

-- Fixed segments

data FixedSegment repr
   = FixedLinear (repr (Point repr Scalar)) (repr (Point repr Scalar))
   | FixedCubic (repr (Point repr Scalar)) (repr (Point repr Scalar)) (repr (Point repr Scalar)) (repr (Point repr Scalar))

class Spatial repr => FixedSegments repr where
  linearF :: repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (FixedSegment repr)
  cubicF :: repr (Point repr Scalar) ->  repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (FixedSegment repr)
  segmentF' :: repr (FixedSegment repr) -> (FixedSegment repr -> repr r) -> repr r
  default linearF :: Applicative repr => repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (FixedSegment repr)
  linearF x0 x1 = pure $ FixedLinear x0 x1
  default cubicF :: Applicative repr => repr (Point repr Scalar) ->  repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (Point repr Scalar) -> repr (FixedSegment repr)
  cubicF x0 c0 c1 x1 = pure $ FixedCubic x0 c0 c1 x1
  default segmentF' :: Monad repr => repr (FixedSegment repr) -> (FixedSegment repr -> repr r) -> repr r
  segmentF' = (>>=)

instance FixedSegments Identity

locatedToFixed :: (LiftLocated repr, Segments repr, FixedSegments repr) => repr (Located repr (Segment repr 'Closed)) -> repr (FixedSegment repr)
locatedToFixed ls = located' ls $ \s p -> segment' s $ \case
  Linear o -> offset' o $ \case
    Offset_Closed v -> linearF p (p %.+^ v)
  Cubic c1 c2 o -> offset' o $ \case
    Offset_Closed v -> cubicF p (p %.+^ c1) (p %.+^ c2) (p %.+^ v)

fixedToLocated :: (LiftLocated repr, Segments repr, FixedSegments repr) => repr (FixedSegment repr) -> repr (Located repr (Segment repr 'Closed))
fixedToLocated fs = segmentF' fs $ \case
  FixedLinear p0 p1 -> linearS (offset_closed (p1 %.-. p0)) `locatedAt'` p0
  FixedCubic p0 c1 c2 p1 -> cubicS (c1 %.-. p0) (c2 %.-. p0) (offset_closed (p1 %.-. p0)) `locatedAt'` p0

instance FixedSegments repr => Parametric repr (FixedSegment repr) Scalar (Point repr Scalar) where
  type PDom (FixedSegment repr) = Scalar
  type PCod (FixedSegment repr) = Point repr Scalar
  atParam s t = segmentF' s $ \case
    FixedLinear p0 p1 -> lerp' t p1 p0
    FixedCubic p1 c1 c2 p2 ->
      let_ (lerp' t c1 p1) \p11 ->
      let_ (lerp' t c2 c1) \p12 ->
      let_ (lerp' t p2 c2) \p13 ->
      let_ (lerp' t p12 p11) \p21 ->
      let_ (lerp' t p13 p12) \p22 ->
        lerp' t p22 p21

instance FixedSegments repr => DomainBounds repr (FixedSegment repr) where
  domainLower _ = num 0
  domainUpper _ = num 1

instance FixedSegments repr => EndValues repr (FixedSegment repr) where
  evalAtLower fs = segmentF' fs $ \case
    FixedLinear p0 _ -> p0
    FixedCubic p0 _ _ _ -> p0
  evalAtUpper fs = segmentF' fs $ \case
    FixedLinear _ p1 -> p1
    FixedCubic _ _ _ p1 -> p1

instance FixedSegments repr => Sectionable repr (FixedSegment repr) where
  splitAtParam fs t = segmentF' fs $ \case
    FixedLinear p0 p1 -> let_ (lerp' t p1 p0) \p -> tup2' (linearF p0 p) (linearF p p1)
    (FixedCubic p0 c1 c2 p1) ->
      let_ (lerp' t c1 p0) \a ->
      let_ (lerp' t c2 c1) \p ->
      let_ (lerp' t p1 c2) \d ->
      let_ (lerp' t p a) \b ->
      let_ (lerp' t d p) \c ->
      let_ (lerp' t c b) \cut ->
        tup2' (cubicF p0 a b cut) (cubicF cut c d p1)
  reverseDomain fs = segmentF' fs $ \case
    FixedLinear p0 p1 -> linearF p1 p0
    FixedCubic p0 c1 c2 p1 -> cubicF p1 c2 c1 p0

data SegMeasure repr = SegMeasure
  { _segMeasure_count :: repr Int
  , _segMeasure_arcLength :: repr (I.Interval' repr Scalar)
  , _segMeasure_arcLengthF :: repr (Arr repr Scalar (I.Interval' repr Scalar))
  , _segMeasure_offset :: repr (Vector repr Scalar)
  , _segMeasure_envelope :: repr (Envelope repr)
  , _segMeasure_trace :: repr (Trace repr)
  }

class (I.LiftInterval repr, Envelopes repr, Traces repr, Segments repr) => LiftSegMeasure repr where
  liftMeasure :: SegMeasure repr -> repr (SegMeasure repr)
  measureSeg :: repr (Segment repr 'Closed) -> repr (SegMeasure repr)
  segCount :: repr (SegMeasure repr) -> repr Int
  segArcLength :: repr (SegMeasure repr) -> repr (I.Interval' repr Scalar)
  segArcLengthF :: repr (SegMeasure repr) -> repr (Arr repr Scalar (I.Interval' repr Scalar))
  segOffset :: repr (SegMeasure repr) -> repr (Vector repr Scalar)
  segEnvelope :: repr (SegMeasure repr) -> repr (Envelope repr)
  segTrace :: repr (SegMeasure repr) -> repr (Trace repr)
  default measureSeg :: Spatial repr => repr (Segment repr 'Closed) -> repr (SegMeasure repr)
  measureSeg s = liftMeasure $ SegMeasure
    { _segMeasure_count = val 1
    , _segMeasure_arcLength = arcLengthBounded (stdTolerance %/ val 100) s
    , _segMeasure_arcLengthF = lam \tol -> arcLengthBounded tol s
    , _segMeasure_offset = offsetS s
    , _segMeasure_envelope = envelopeOf s
    -- TODO: Assume we're 2D so we can have traces
    , _segMeasure_trace = mempty'
    }
  default liftMeasure :: Applicative repr => SegMeasure repr -> repr (SegMeasure repr)
  liftMeasure = pure
  default segCount :: Monad repr => repr (SegMeasure repr) -> repr Int
  segCount = (_segMeasure_count =<<)
  default segArcLength :: Monad repr => repr (SegMeasure repr) -> repr (I.Interval' repr Scalar)
  segArcLength = (_segMeasure_arcLength =<<)
  default segArcLengthF :: Monad repr => repr (SegMeasure repr) -> repr (Arr repr Scalar (I.Interval' repr Scalar))
  segArcLengthF = (_segMeasure_arcLengthF =<<)
  default segOffset :: Monad repr => repr (SegMeasure repr) -> repr (Vector repr Scalar)
  segOffset = (_segMeasure_offset =<<)
  default segEnvelope :: Monad repr => repr (SegMeasure repr) -> repr (Envelope repr)
  segEnvelope = (_segMeasure_envelope =<<)
  default segTrace :: Monad repr => repr (SegMeasure repr) -> repr (Trace repr)
  segTrace = (_segMeasure_trace =<<)

instance LiftSegMeasure repr => Semigroup' repr (SegMeasure repr) where
  r1 %<> r2 = liftMeasure $ SegMeasure
    { _segMeasure_count = segCount r1 %+ segCount r2
    , _segMeasure_arcLength = segArcLength r1 %+ segArcLength r2
    -- This is incorrect, but it's what the original diagrams do
    , _segMeasure_arcLengthF = lam \tol -> (segArcLengthF r1 %$ tol) %+ (segArcLengthF r2 %$ tol)
    , _segMeasure_offset = segOffset r1 %^+^ segOffset r2
    , _segMeasure_envelope = segEnvelope r1 %<> actA' (translateBy (segOffset r1)) (segEnvelope r2)
    , _segMeasure_trace = segTrace r1 %<> actA' (translateBy (segOffset r1)) (segTrace r2)
    }

instance (Spatial repr, LiftSegMeasure repr) => Monoid' repr (SegMeasure repr) where
  mempty' = liftMeasure $ SegMeasure
    { _segMeasure_count = val 0
    , _segMeasure_arcLength = fromInteger' (val 0)
    , _segMeasure_arcLengthF = lam \_ -> fromInteger' (val 0)
    , _segMeasure_offset = zero'
    , _segMeasure_envelope = mempty'
    , _segMeasure_trace = mempty'
    }

segArcLengthBounded :: LiftSegMeasure repr => repr Scalar -> repr (SegMeasure repr) -> repr (I.Interval' repr Scalar)
segArcLengthBounded tolerance sm =
  let cached = segArcLength sm
   in if' (I.width' cached %<= tolerance) cached $ segArcLengthF sm %$ tolerance

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Diagrams.Final.Trail.Internal where

import Prelude hiding (null, reverse, lookup)
import Data.MonoTraversable

import Diagrams.Final.Core hiding (Measure)
import Diagrams.Final.Segment

type Elem repr = repr (Segment repr 'Closed)
type Measure repr = repr (SegMeasure repr)

data Level = Level_Leaf | Level_Branch Level

data LevelS k where
  LevelS_Leaf :: LevelS 'Level_Leaf
  LevelS_Branch :: LevelS k -> LevelS ('Level_Branch k)

data Node repr l where
  Node_Leaf2
    :: !(Measure repr)
    -> !(Elem repr)
    -> !(Elem repr)
    -> Node repr 'Level_Leaf
  Node_Leaf3
    :: !(Measure repr)
    -> !(Elem repr)
    -> !(Elem repr)
    -> !(Elem repr)
    -> Node repr 'Level_Leaf
  Node_Branch2
    :: !(Measure repr)
    -> Node repr l
    -> Node repr l
    -> Node repr ('Level_Branch l)
  Node_Branch3
    :: !(Measure repr)
    -> Node repr l
    -> Node repr l
    -> Node repr l
    -> Node repr ('Level_Branch l)

-- TODO eqord

measureNode :: Node repr l -> Measure repr
measureNode = \case
  Node_Leaf2 m _ _ -> m
  Node_Leaf3 m _ _ _ -> m
  Node_Branch2 m _ _ -> m
  Node_Branch3 m _ _ _ -> m

node2L :: LiftSegMeasure repr => Elem repr -> Elem repr -> Node repr 'Level_Leaf
node2L a b = Node_Leaf2 (measureSeg a %<> measureSeg b) a b

node3L :: LiftSegMeasure repr => Elem repr -> Elem repr -> Elem repr -> Node repr 'Level_Leaf
node3L a b c = Node_Leaf3 (measureSeg a %<> measureSeg b %<> measureSeg c) a b c

node2N :: LiftSegMeasure repr => Node repr l -> Node repr l -> Node repr ('Level_Branch l)
node2N a b = Node_Branch2 (measureNode a %<> measureNode b) a b

node3N :: LiftSegMeasure repr => Node repr l -> Node repr l -> Node repr l -> Node repr ('Level_Branch l)
node3N a b c = Node_Branch3 (measureNode a %<> measureNode b %<> measureNode c) a b c

data DigitN repr l
   = OneN !(Node repr l)
   | TwoN !(Node repr l) !(Node repr l)
   | ThreeN !(Node repr l) !(Node repr l) !(Node repr l)
   | FourN !(Node repr l) !(Node repr l) !(Node repr l) !(Node repr l)

-- TODO eqord

measureDigitN :: LiftSegMeasure repr => DigitN repr l -> Measure repr
measureDigitN = \case
  OneN x -> measureNode x
  TwoN x y -> measureNode x %<> measureNode y
  ThreeN x y z -> measureNode x %<> measureNode y %<> measureNode z
  FourN w x y z -> measureNode w %<> measureNode x %<> measureNode y %<> measureNode z

data DigitL repr
   = OneL !(Elem repr)
   | TwoL !(Elem repr) !(Elem repr)
   | ThreeL !(Elem repr) !(Elem repr) !(Elem repr)
   | FourL !(Elem repr) !(Elem repr) !(Elem repr) !(Elem repr)

-- TODO eqord

measureDigitL :: LiftSegMeasure repr => DigitL repr -> Measure repr
measureDigitL = \case
  OneL x -> measureSeg x
  TwoL x y -> measureSeg x %<> measureSeg y
  ThreeL x y z -> measureSeg x %<> measureSeg y %<> measureSeg z
  FourL w x y z -> measureSeg w %<> measureSeg x %<> measureSeg y %<> measureSeg z

nodeToDigitN :: Node repr ('Level_Branch l) -> DigitN repr l
nodeToDigitN = \case
  Node_Branch2 _ x y -> TwoN x y
  Node_Branch3 _ x y z -> ThreeN x y z

nodeToDigitL :: Node repr 'Level_Leaf -> DigitL repr
nodeToDigitL = \case
  Node_Leaf2 _ x y -> TwoL x y
  Node_Leaf3 _ x y z -> ThreeL x y z

data DeepTree repr l where
  DeepTree_Empty
    :: DeepTree repr l
  DeepTree_Single
    :: Node repr l
    -> DeepTree repr l
  DeepTree_Deep
    :: {-# UNPACK #-} !(Measure repr)
    -> DigitN repr l
    -> DeepTree repr ('Level_Branch l)
    -> DigitN repr l
    -> DeepTree repr l

-- TODO eqord

measureDeepTree :: LiftSegMeasure repr => DeepTree repr l -> Measure repr
measureDeepTree = \case
  DeepTree_Empty -> mempty'
  DeepTree_Single n -> measureNode n
  DeepTree_Deep m _ _ _ -> m

data FingerTree repr
   = FingerTree_Empty
   | FingerTree_Single !(Elem repr)
   | FingerTree_Deep !(Measure repr) (DigitL repr) (DeepTree repr 'Level_Leaf) (DigitL repr)

-- TODO eqord

measureFingerTree :: LiftSegMeasure repr => FingerTree repr -> Measure repr
measureFingerTree = \case
  FingerTree_Empty -> mempty'
  FingerTree_Single n -> measureSeg n
  FingerTree_Deep m _ _ _ -> m

deepL
  :: LiftSegMeasure repr
  => DigitL repr
  -> DeepTree repr 'Level_Leaf
  -> DigitL repr
  -> FingerTree repr
deepL pr m sf = FingerTree_Deep
  (measureDigitL pr %<> measureDeepTree m %<> measureDigitL sf)
  pr
  m
  sf

deepN
  :: LiftSegMeasure repr
  => DigitN repr l
  -> DeepTree repr ('Level_Branch l)
  -> DigitN repr l
  -> DeepTree repr l
deepN pr m sf = DeepTree_Deep
  (measureDigitN pr %<> measureDeepTree m %<> measureDigitN sf)
  pr
  m
  sf

----

type instance Element (FingerTree repr) = Elem repr

instance LiftSegMeasure repr => MonoFunctor (FingerTree repr) where
  omap f = \case
    FingerTree_Empty -> FingerTree_Empty
    FingerTree_Single x -> FingerTree_Single (f x)
    FingerTree_Deep _ pr t sf -> deepL
      (omapDigitL f pr)
      (omapDeepTree f t)
      (omapDigitL f sf)

omapDigitL :: LiftSegMeasure repr => (Elem repr -> Elem repr) -> DigitL repr -> DigitL repr
omapDigitL f = \case
  OneL x -> OneL (f x)
  TwoL x y -> TwoL (f x) (f y)
  ThreeL x y z -> ThreeL (f x) (f y) (f z)
  FourL w x y z -> FourL (f w) (f x) (f y) (f z)

omapDeepTree :: LiftSegMeasure repr => (Elem repr -> Elem repr) -> DeepTree repr l -> DeepTree repr l
omapDeepTree f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single (omapNode f x)
  DeepTree_Deep _ pr t sf -> deepN
    (omapDigitN f pr)
    (omapDeepTree f t)
    (omapDigitN f sf)

omapNode :: LiftSegMeasure repr => (Elem repr -> Elem repr) -> Node repr l -> Node repr l
omapNode f = \case
  Node_Leaf2 _ x y -> node2L (f x) (f y)
  Node_Leaf3 _ x y z -> node3L (f x) (f y) (f z)
  Node_Branch2 _ x y -> node2N (omapNode f x) (omapNode f y)
  Node_Branch3 _ x y z -> node3N (omapNode f x) (omapNode f y) (omapNode f z)

omapDigitN :: LiftSegMeasure repr => (Elem repr -> Elem repr) -> DigitN repr l -> DigitN repr l
omapDigitN f = \case
  OneN x -> OneN (omapNode f x)
  TwoN x y -> TwoN (omapNode f x) (omapNode f y)
  ThreeN x y z -> ThreeN (omapNode f x) (omapNode f y) (omapNode f z)
  FourN w x y z -> FourN (omapNode f w) (omapNode f x) (omapNode f y) (omapNode f z)

instance LiftSegMeasure repr => MonoFoldable (FingerTree repr) where
  ofoldMap f = \case
    FingerTree_Empty -> mempty
    FingerTree_Single x -> f x
    FingerTree_Deep _ pr t sf -> mconcat
      [ ofoldMapDigitL f pr
      , ofoldMapDeepTree f t
      , ofoldMapDigitL f sf
      ]
  ofoldr f x0 = \case
    FingerTree_Empty -> x0
    FingerTree_Single x -> f x x0
    FingerTree_Deep _ pr t sf -> ofoldrDigitL f (ofoldrDeepTree f (ofoldrDigitL f x0 sf) t) pr
  ofoldl' f x0 = \case
    FingerTree_Empty -> x0
    FingerTree_Single x -> f x0 x
    FingerTree_Deep _ pr t sf -> (ofoldlDigitL f $! (ofoldlDeepTree f $! ofoldlDigitL f x0 pr) t) sf
  ofoldr1Ex f = \case
    FingerTree_Empty -> error "ofoldr1Ex: empty FingerTree"
    FingerTree_Single x -> x
    FingerTree_Deep _ pr t sf -> ofoldrDigitL f (ofoldrDeepTree f (ofoldr1DigitL f sf) t) pr
  ofoldl1Ex' f = \case
    FingerTree_Empty -> error "ofoldr1Ex: empty FingerTree"
    FingerTree_Single x -> x
    FingerTree_Deep _ pr t sf -> (ofoldlDigitL f $! (ofoldlDeepTree f $! ofoldl1DigitL f pr) t) sf

ofoldMapDigitL :: Monoid m => (Elem repr -> m) -> DigitL repr -> m
ofoldMapDigitL f = \case
  OneL x -> f x
  TwoL x y -> f x <> f y
  ThreeL x y z -> f x <> f y <> f z
  FourL w x y z -> f w <> f x <> f y <> f z

ofoldMapDeepTree :: Monoid m => (Elem repr -> m) -> DeepTree repr l -> m
ofoldMapDeepTree f = \case
  DeepTree_Empty -> mempty
  DeepTree_Single x -> ofoldMapNode f x
  DeepTree_Deep _ pr t sf -> ofoldMapDigitN f pr <> ofoldMapDeepTree f t <> ofoldMapDigitN f sf

ofoldMapNode :: Monoid m => (Elem repr -> m) -> Node repr l -> m
ofoldMapNode f = \case
  Node_Leaf2 _ x y -> f x <> f y
  Node_Leaf3 _ x y z -> f x <> f y <> f z
  Node_Branch2 _ x y -> ofoldMapNode f x <> ofoldMapNode f y
  Node_Branch3 _ x y z -> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z

ofoldMapDigitN :: Monoid m => (Elem repr -> m) -> DigitN repr l -> m
ofoldMapDigitN f = \case
  OneN x -> ofoldMapNode f x
  TwoN x y -> ofoldMapNode f x <> ofoldMapNode f y
  ThreeN x y z -> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z
  FourN w x y z -> ofoldMapNode f w <> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z

ofoldrDigitL
  :: (Elem repr -> r -> r)
  -> r
  -> DigitL repr
  -> r
ofoldrDigitL f x0 = \case
  OneL x -> f x x0
  TwoL x y -> f x (f y x0)
  ThreeL x y z -> f x (f y (f z x0))
  FourL w x y z -> f w (f x (f y (f z x0)))

ofoldr1DigitL
  :: (Elem repr -> Elem repr -> Elem repr)
  -> DigitL repr
  -> Elem repr
ofoldr1DigitL f = \case
  OneL x -> x
  TwoL x y -> f x y
  ThreeL x y z -> f x (f y z)
  FourL w x y z -> f w (f x (f y z))

ofoldl1DigitL
  :: (Elem repr -> Elem repr -> Elem repr)
  -> DigitL repr
  -> Elem repr
ofoldl1DigitL f = \case
  OneL x -> x
  TwoL x y -> f x y
  ThreeL x y z -> (f $! f x y) z
  FourL w x y z -> (f $! (f $! f w x) y) z

ofoldrDeepTree
  :: (Elem repr -> r -> r)
  -> r
  -> DeepTree repr l
  -> r
ofoldrDeepTree f x0 = \case
  DeepTree_Empty -> x0
  DeepTree_Single x -> ofoldrNode f x0 x
  DeepTree_Deep _ pr t sf -> ofoldrDigitN f (ofoldrDeepTree f (ofoldrDigitN f x0 sf) t) pr

ofoldrDigitN
  :: (Elem repr -> r -> r)
  -> r
  -> DigitN repr l
  -> r
ofoldrDigitN f x0 = \case
  OneN x -> ofoldrNode f x0 x
  TwoN x y -> ofoldrNode f (ofoldrNode f x0 y) x
  ThreeN x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x
  FourN w x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x) w

ofoldrNode
  :: (Elem repr -> r -> r)
  -> r
  -> Node repr l
  -> r
ofoldrNode f x0 = \case
  Node_Leaf2 _ x y -> f x (f y x0)
  Node_Leaf3 _ x y z -> f x (f y (f z x0))
  Node_Branch2 _ x y -> ofoldrNode f (ofoldrNode f x0 y) x
  Node_Branch3 _ x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x

ofoldlDigitL
  :: (r -> Elem repr -> r)
  -> r
  -> DigitL repr
  -> r
ofoldlDigitL f x0 = \case
  OneL x -> f x0 x
  TwoL x y -> (f $! f x0 x) y
  ThreeL x y z -> (f $! (f $! f x0 x) y) z
  FourL w x y z -> (f $! (f $! (f $! f x0 w) x) y) z

ofoldlDeepTree
  :: (r -> Elem repr -> r)
  -> r
  -> DeepTree repr l
  -> r
ofoldlDeepTree f x0 = \case
  DeepTree_Empty -> x0
  DeepTree_Single x -> ofoldlNode f x0 x
  DeepTree_Deep _ pr t sf -> (ofoldlDigitN f $! (ofoldlDeepTree f $! ofoldlDigitN f x0 pr) t) sf

ofoldlDigitN
  :: (r -> Elem repr -> r)
  -> r
  -> DigitN repr l
  -> r
ofoldlDigitN f x0 = \case
  OneN x -> ofoldlNode f x0 x
  TwoN x y -> (ofoldlNode f $! ofoldlNode f x0 x) y
  ThreeN x y z -> (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 x) y) z
  FourN w x y z -> (ofoldlNode f $! (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 w) x) y) z

ofoldlNode
  :: (r -> Elem repr -> r)
  -> r
  -> Node repr l
  -> r
ofoldlNode f x0 = \case
  Node_Leaf2 _ x y -> (f $! f x0 x) y
  Node_Leaf3 _ x y z -> (f $! (f $! f x0 x) y) z
  Node_Branch2 _ x y -> (ofoldlNode f $! ofoldlNode f x0 x) y
  Node_Branch3 _ x y z -> (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 x) y) z

instance LiftSegMeasure repr => MonoTraversable (FingerTree repr) where
  otraverse f = \case
    FingerTree_Empty -> pure FingerTree_Empty
    FingerTree_Single x -> FingerTree_Single <$> f x
    FingerTree_Deep _ pr t sf -> otraverseDigitL (otraverseDigitL (pure deepL) f pr <*> otraverseDeepTree f t) f sf

withOneL :: Functor f => f (DigitL repr -> b) -> f (Elem repr -> b)
withOneL = fmap (\f x -> f (OneL x))

withTwoL :: Applicative f => f (DigitL repr -> b) -> f (Elem repr -> Elem repr -> b)
withTwoL = fmap (\f x y -> f (TwoL x y))

withThreeL :: Applicative f => f (DigitL repr -> b) -> f (Elem repr -> Elem repr -> Elem repr -> b)
withThreeL = fmap (\f x y z -> f (ThreeL x y z))

withFourL :: Applicative f => f (DigitL repr -> b) -> f (Elem repr -> Elem repr -> Elem repr -> Elem repr -> b)
withFourL = fmap (\f w x y z -> f (FourL w x y z))

otraverseDigitL :: Applicative f => f (DigitL repr -> b) -> (Elem repr -> f (Elem repr)) -> DigitL repr -> f b
otraverseDigitL k f d = case d of
  OneL x -> withOneL k <*> f x
  TwoL x y -> withTwoL k <*> f x <*> f y
  ThreeL x y z -> withThreeL k <*> f x <*> f y <*> f z
  FourL w x y z -> withFourL k <*> f w <*> f x <*> f y <*> f z

otraverseDeepTree :: (LiftSegMeasure repr, Applicative f) => (Elem repr -> f (Elem repr)) -> DeepTree repr l -> f (DeepTree repr l)
otraverseDeepTree f = \case
  DeepTree_Empty -> pure DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single <$> otraverseNode f x
  DeepTree_Deep _ pr t sf -> otraverseDigitN (otraverseDigitN (pure deepN) f pr <*> otraverseDeepTree f t) f sf

withOneN :: Functor f => f (DigitN repr l -> b) -> f (Node repr l -> b)
withOneN = fmap (\f x -> f (OneN x))

withTwoN :: Applicative f => f (DigitN repr l -> b) -> f (Node repr l -> Node repr l -> b)
withTwoN = fmap (\f x y -> f (TwoN x y))

withThreeN :: Applicative f => f (DigitN repr l -> b) -> f (Node repr l -> Node repr l -> Node repr l -> b)
withThreeN = fmap (\f x y z -> f (ThreeN x y z))

withFourN :: Applicative f => f (DigitN repr l -> b) -> f (Node repr l -> Node repr l -> Node repr l -> Node repr l -> b)
withFourN = fmap (\f w x y z -> f (FourN w x y z))

otraverseDigitN :: (LiftSegMeasure repr, Applicative f) => f (DigitN repr l -> b) -> (Elem repr -> f (Elem repr)) -> DigitN repr l -> f b
otraverseDigitN k f d = case d of
  OneN x -> withOneN k <*> otraverseNode f x
  TwoN x y -> withTwoN k <*> otraverseNode f x <*> otraverseNode f y
  ThreeN x y z -> withThreeN k <*> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z
  FourN w x y z -> withFourN k <*> otraverseNode f w <*> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z

otraverseNode :: (LiftSegMeasure repr, Applicative f) => (Elem repr -> f (Elem repr)) -> Node repr l -> f (Node repr l)
otraverseNode f = \case
  Node_Leaf2 _ x y -> node2L <$> f x <*> f y
  Node_Leaf3 _ x y z -> node3L <$> f x <*> f y <*> f z
  Node_Branch2 _ x y -> node2N <$> otraverseNode f x <*> otraverseNode f y
  Node_Branch3 _ x y z -> node3N <$> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z

omapWithPos
  :: LiftSegMeasure repr => (Measure repr -> Elem repr -> Elem repr)
  -> FingerTree repr
  -> FingerTree repr
omapWithPos f = omapWithContext (\pr x _ -> f pr x)

omapWithContext
  :: LiftSegMeasure repr => (Measure repr -> Elem repr -> Measure repr -> Elem repr)
  -> FingerTree repr
  -> FingerTree repr
omapWithContext f = \case
  FingerTree_Empty -> FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single (f mempty' x mempty')
  FingerTree_Deep _ pr t sf ->
    let prm = measureDigitL pr
        tm = measureDeepTree t
        sfm = measureDigitL sf
     in deepL
       (omapWithContextDigitL mempty' (tm %<> sfm) f pr)
       (omapWithContextDeepTree prm sfm f t)
       (omapWithContextDigitL (prm %<> tm) mempty' f sf)

omapWithContextDigitL :: LiftSegMeasure repr => Measure repr -> Measure repr -> (Measure repr -> Elem repr -> Measure repr -> Elem repr) -> DigitL repr -> DigitL repr
omapWithContextDigitL m0 m1 f = \case
  OneL x -> OneL (f m0 x m1)
  TwoL x y ->
    let mx = measureSeg x
        my = measureSeg y
     in TwoL (f m0 x (my %<> m1)) (f (m0 %<> mx) y m1)
  ThreeL x y z ->
    let mx = measureSeg x
        my = measureSeg y
        mz = measureSeg z
     in ThreeL (f m0 x (my %<> mz %<> m1)) (f (m0 %<> mx) y (mz %<> m1)) (f (m0 %<> mx %<> my) z m1)
  FourL w x y z ->
    let mw = measureSeg w
        mx = measureSeg x
        my = measureSeg y
        mz = measureSeg z
     in FourL
          (f m0 w (mx %<> my %<> mz %<> m1))
          (f (m0 %<> mw) x (my %<> mz %<> m1))
          (f (m0 %<> mw %<> mx) y (mz %<> m1))
          (f (m0 %<> mw %<> mx %<> my) z m1)

omapWithContextDeepTree :: LiftSegMeasure repr => Measure repr -> Measure repr -> (Measure repr -> Elem repr -> Measure repr -> Elem repr) -> DeepTree repr l -> DeepTree repr l
omapWithContextDeepTree m0 m1 f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single (omapWithContextNode m0 m1 f x)
  DeepTree_Deep _ pr t sf ->
    let prm = measureDigitN pr
        tm = measureDeepTree t
        sfm = measureDigitN sf
     in deepN
       (omapWithContextDigitN m0 (tm %<> sfm %<> m1) f pr)
       (omapWithContextDeepTree (m0 %<> prm) (sfm %<> m1) f t)
       (omapWithContextDigitN (m0 %<> prm %<> tm) m1 f sf)

omapWithContextDigitN :: LiftSegMeasure repr => Measure repr -> Measure repr -> (Measure repr -> Elem repr -> Measure repr -> Elem repr) -> DigitN repr l -> DigitN repr l
omapWithContextDigitN m0 m1 f = \case
  OneN x -> OneN (omapWithContextNode m0 m1 f x)
  TwoN x y ->
    let mx = measureNode x
        my = measureNode y
     in TwoN (omapWithContextNode m0 (my %<> m1) f x) (omapWithContextNode (m0 %<> mx) m1 f y)
  ThreeN x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in ThreeN
          (omapWithContextNode m0 (my %<> mz %<> m1) f x)
          (omapWithContextNode (m0 %<> mx) (mz %<> m1) f y)
          (omapWithContextNode (m0 %<> mx %<> my) m1 f z)
  FourN w x y z ->
    let mw = measureNode w
        mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in FourN
          (omapWithContextNode m0 (mx %<> my %<> mz %<> m1) f w)
          (omapWithContextNode (m0 %<> mw) (my %<> mz %<> m1) f x)
          (omapWithContextNode (m0 %<> mw %<> mx) (mz %<> m1) f y)
          (omapWithContextNode (m0 %<> mw %<> mx %<> my) m1 f z)

omapWithContextNode :: LiftSegMeasure repr => Measure repr -> Measure repr -> (Measure repr -> Elem repr -> Measure repr -> Elem repr) -> Node repr l -> Node repr l
omapWithContextNode m0 m1 f = \case
  Node_Leaf2 _ x y ->
    let mx = measureSeg x
        my = measureSeg y
     in node2L (f m0 x (my %<> m1)) (f (m0 %<> mx) y m1)
  Node_Leaf3 _ x y z ->
    let mx = measureSeg x
        my = measureSeg y
        mz = measureSeg z
     in node3L (f m0 x (my %<> mz %<> m1)) (f (m0 %<> mx) y (mz %<> m1)) (f (m0 %<> mx %<> my) z m1)
  Node_Branch2 _ x y ->
    let mx = measureNode x
        my = measureNode y
     in node2N (omapWithContextNode m0 (my %<> m1) f x) (omapWithContextNode (m0 %<> mx) m1 f y)
  Node_Branch3 _ x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in node3N
          (omapWithContextNode m0 (my %<> mz %<> m1) f x)
          (omapWithContextNode (m0 %<> mx) (mz %<> m1) f y)
          (omapWithContextNode (m0 %<> mx %<> my) m1 f z)

otraverseWithPos
  :: (LiftSegMeasure repr, Applicative f)
  => (Measure repr -> Elem repr -> f (Elem repr))
  -> FingerTree repr
  -> f (FingerTree repr)
otraverseWithPos f = otraverseWithContext (\pr x _ -> f pr x)

otraverseWithContext
  :: (LiftSegMeasure repr, Applicative f)
  => (Measure repr -> Elem repr -> Measure repr -> f (Elem repr))
  -> FingerTree repr
  -> f (FingerTree repr)
otraverseWithContext f = \case
  FingerTree_Empty -> pure FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single <$> f mempty' x mempty'
  FingerTree_Deep _ pr t sf ->
    let mpr = measureDigitL pr
        mt = measureDeepTree t
        msf = measureDigitL sf
     in otraverseWithContextDigitL (mpr %<> mt) mempty'
          (otraverseWithContextDigitL mempty' (mt %<> msf) (pure deepL) f pr <*> otraverseWithContextDeepTree mpr msf f t) f sf

otraverseWithContextDigitL
  :: (LiftSegMeasure repr, Applicative f)
  => Measure repr
  -> Measure repr
  -> f (DigitL repr -> b)
  -> (Measure repr -> Elem repr -> Measure repr -> f (Elem repr))
  -> DigitL repr
  -> f b
otraverseWithContextDigitL m0 m1 k f = \case
  OneL x -> withOneL k <*> f m0 x m1
  TwoL x y ->
    let mx = measureSeg x
        my = measureSeg y
     in withTwoL k <*> f m0 x (my %<> m1) <*> f (m0 %<> mx) y m1
  ThreeL x y z ->
    let mx = measureSeg x
        my = measureSeg y
        mz = measureSeg z
     in withThreeL k
          <*> f m0 x (my %<> mz %<> m1)
          <*> f (m0 %<> mx) y (mz %<> m1)
          <*> f (m0 %<> mx %<> my) z m1
  FourL w x y z ->
   let mw = measureSeg w
       mx = measureSeg x
       my = measureSeg y
       mz = measureSeg z
    in withFourL k
         <*> f m0 w (mx %<> my %<> mz %<> m1)
         <*> f (m0 %<> mw) x (my %<> mz %<> m1)
         <*> f (m0 %<> mw %<> mx) y (mz %<> m1)
         <*> f (m0 %<> mw %<> mx %<> my) z m1

otraverseWithContextDeepTree
  :: (LiftSegMeasure repr, Applicative f)
  => Measure repr
  -> Measure repr
  -> (Measure repr -> Elem repr -> Measure repr -> f (Elem repr))
  -> DeepTree repr l
  -> f (DeepTree repr l)
otraverseWithContextDeepTree m0 m1 f = \case
  DeepTree_Empty -> pure DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single <$> otraverseWithContextNode m0 m1 f x
  DeepTree_Deep _ pr t sf ->
    let mpr = measureDigitN pr
        mt = measureDeepTree t
        msf = measureDigitN sf
     in otraverseWithContextDigitN (m0 %<> mpr %<> mt) m1
          (otraverseWithContextDigitN m0 (mt %<> msf %<> m1) (pure deepN) f pr
             <*> otraverseWithContextDeepTree (m0 %<> mpr) (msf %<> m1) f t) f sf

otraverseWithContextDigitN
  :: (LiftSegMeasure repr, Applicative f)
  => Measure repr
  -> Measure repr
  -> f (DigitN repr l -> b)
  -> (Measure repr -> Elem repr -> Measure repr -> f (Elem repr))
  -> DigitN repr l
  -> f b
otraverseWithContextDigitN m0 m1 k f = \case
  OneN x -> withOneN k <*> otraverseWithContextNode m0 m1 f x
  TwoN x y ->
    let mx = measureNode x
        my = measureNode y
     in withTwoN k <*> otraverseWithContextNode m0 (my %<> m1) f x <*> otraverseWithContextNode (m0 %<> mx) m1 f y
  ThreeN x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in withThreeN k
          <*> otraverseWithContextNode m0 (my %<> mz %<> m1) f x
          <*> otraverseWithContextNode (m0 %<> mx) (mz %<> m1) f y
          <*> otraverseWithContextNode (m0 %<> mx %<> my) m1 f z
  FourN w x y z ->
   let mw = measureNode w
       mx = measureNode x
       my = measureNode y
       mz = measureNode z
    in withFourN k
         <*> otraverseWithContextNode m0 (mx %<> my %<> mz %<> m1) f w
         <*> otraverseWithContextNode (m0 %<> mw) (my %<> mz %<> m1) f x
         <*> otraverseWithContextNode (m0 %<> mw %<> mx) (mz %<> m1) f y
         <*> otraverseWithContextNode (m0 %<> mw %<> mx %<> my) m1 f z

otraverseWithContextNode
  :: (LiftSegMeasure repr, Applicative f)
  => Measure repr
  -> Measure repr
  -> (Measure repr -> Elem repr -> Measure repr -> f (Elem repr))
  -> Node repr l
  -> f (Node repr l)
otraverseWithContextNode m0 m1 f = \case
  Node_Leaf2 _ x y ->
   let mx = measureSeg x
       my = measureSeg y
    in node2L <$> f m0 x (my %<> m1) <*> f (m0 %<> mx) y m1
  Node_Leaf3 _ x y z ->
   let mx = measureSeg x
       my = measureSeg y
       mz = measureSeg z
    in node3L <$> f m0 x (my %<> mz %<> m1) <*> f (m0 %<> mx) y (mz %<> m1) <*> f (m0 %<> mx %<> my) z m1
  Node_Branch2 _ x y ->
   let mx = measureNode x
       my = measureNode y
    in node2N <$> otraverseWithContextNode m0 (my %<> m1) f x <*> otraverseWithContextNode (m0 %<> mx) m1 f y
  Node_Branch3 _ x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in node3N
          <$> otraverseWithContextNode m0 (my %<> mz %<> m1) f x
          <*> otraverseWithContextNode (m0 %<> mx) (mz %<> m1) f y
          <*> otraverseWithContextNode (m0 %<> mx %<> my) m1 f z

--

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

infixr 5 <<|, :<<
infixl 5 |>>, :>>

data ViewL repr
   = EmptyL
   | Elem repr :< FingerTree repr

-- TODO: eqord

data ViewR repr
   = EmptyR
   | FingerTree repr :> Elem repr

-- TODO: eqord

data ViewNL repr l
   = EmptyNL
   | Node repr l :<< DeepTree repr l

data ViewNR repr l
   = EmptyNR
   | DeepTree repr l :>> Node repr l

empty :: FingerTree repr
empty = FingerTree_Empty

singleton :: Elem repr -> FingerTree repr
singleton = FingerTree_Single

fromList :: LiftSegMeasure repr => [Elem repr] -> FingerTree repr
fromList = foldr (<|) FingerTree_Empty

(<|) :: LiftSegMeasure repr => Elem repr -> FingerTree repr -> FingerTree repr
(!a) <| t = case t of
  FingerTree_Empty -> FingerTree_Single a
  FingerTree_Single b -> deepL (OneL a) DeepTree_Empty (OneL b)
  FingerTree_Deep m (FourL b c d e) t' sf -> t' `seq` FingerTree_Deep
    (measureSeg a %<> m)
    (TwoL a b)
    (node3L c d e <<| t')
    sf
  FingerTree_Deep m pr t' sf -> FingerTree_Deep
    (measureSeg a %<> m)
    (consDigitL a pr)
    t'
    sf

(|>) :: LiftSegMeasure repr => FingerTree repr -> Elem repr -> FingerTree repr
t |> (!x) = case t of
  FingerTree_Empty -> FingerTree_Single x
  FingerTree_Single a -> deepL (OneL a) DeepTree_Empty (OneL x)
  FingerTree_Deep m pr t' (FourL a b c d) -> t `seq` FingerTree_Deep
    (m %<> measureSeg x)
    pr
    (t' |>> node3L a b c) (TwoL d x)
  FingerTree_Deep m pr t' sf -> FingerTree_Deep
    (m %<> measureSeg x)
    pr
    t'
    (snocDigitL sf x)

(<<|) :: LiftSegMeasure repr => Node repr l -> DeepTree repr l -> DeepTree repr l
(!a) <<| t = case t of
  DeepTree_Empty -> DeepTree_Single a
  DeepTree_Single b -> deepN (OneN a) DeepTree_Empty (OneN b)
  DeepTree_Deep m (FourN b c d e) t' sf -> t `seq` DeepTree_Deep
    (measureNode a %<> m)
    (TwoN a b)
    (node3N c d e <<| t')
    sf
  DeepTree_Deep m pr t' sf -> DeepTree_Deep
    (measureNode a %<> m)
    (consDigitN a pr)
    t'
    sf

(|>>) :: LiftSegMeasure repr => DeepTree repr l -> Node repr l -> DeepTree repr l
t |>> (!x) = case t of
  DeepTree_Empty -> DeepTree_Single x
  DeepTree_Single a -> deepN (OneN a) DeepTree_Empty (OneN x)
  DeepTree_Deep m pr t' (FourN a b c d) -> DeepTree_Deep
    (m %<> measureNode x)
    pr
    (t' |>> node3N a b c) (TwoN d x)
  DeepTree_Deep m pr t' sf -> DeepTree_Deep
    (m %<> measureNode x)
    pr
    t'
    (snocDigitN sf x)

consDigitL :: Elem repr -> DigitL repr -> DigitL repr
consDigitL a = \case
  OneL b -> TwoL a b
  TwoL b c -> ThreeL a b c
  ThreeL b c d -> FourL a b c d
  FourL _ _ _ _ -> undefined

consDigitN :: Node repr l -> DigitN repr l -> DigitN repr l
consDigitN a = \case
  OneN b -> TwoN a b
  TwoN b c -> ThreeN a b c
  ThreeN b c d -> FourN a b c d
  FourN _ _ _ _ -> undefined

snocDigitL :: DigitL repr -> Elem repr -> DigitL repr
snocDigitL d x = case d of
  OneL a -> TwoL a x
  TwoL a b -> ThreeL a b x
  ThreeL a b c -> FourL a b c x
  FourL _ _ _ _ -> undefined

snocDigitN :: DigitN repr l -> Node repr l -> DigitN repr l
snocDigitN d x = case d of
  OneN a -> TwoN a x
  TwoN a b -> ThreeN a b x
  ThreeN a b c -> FourN a b c x
  FourN _ _ _ _ -> undefined

null :: FingerTree repr -> Bool
null = \case
  FingerTree_Empty -> True
  _ -> False

viewl :: LiftSegMeasure repr => FingerTree repr -> ViewL repr
viewl = \case
  FingerTree_Empty -> EmptyL
  FingerTree_Single x -> x :< FingerTree_Empty
  FingerTree_Deep _ (OneL x) t sf -> x :< rotLL t sf
  FingerTree_Deep _ pr t sf -> lheadDigitL pr :< deepL (ltailDigitL pr) t sf

viewNL :: LiftSegMeasure repr => DeepTree repr l -> ViewNL repr l
viewNL = \case
  DeepTree_Empty -> EmptyNL
  DeepTree_Single x -> x :<< DeepTree_Empty
  DeepTree_Deep _ (OneN x) t sf -> x :<< rotNL t sf
  DeepTree_Deep _ pr t sf -> lheadDigitN pr :<< deepN (ltailDigitN pr) t sf

rotLL :: LiftSegMeasure repr => DeepTree repr 'Level_Leaf -> DigitL repr -> FingerTree repr
rotLL t sf = case viewNL t of
  EmptyNL -> digitToTreeL sf
  a :<< t' -> FingerTree_Deep (measureDeepTree t %<> measureDigitL sf) (nodeToDigitL a) t' sf

rotNL :: LiftSegMeasure repr => DeepTree repr ('Level_Branch l) -> DigitN repr l -> DeepTree repr l
rotNL t sf = case viewNL t of
  EmptyNL -> digitToTreeN sf
  a :<< t' -> DeepTree_Deep (measureDeepTree t %<> measureDigitN sf) (nodeToDigitN a) t' sf

lheadDigitL :: DigitL repr -> Elem repr
lheadDigitL = \case
  (OneL a) -> a
  (TwoL a _) -> a
  (ThreeL a _ _) -> a
  (FourL a _ _ _) -> a

ltailDigitL :: DigitL repr -> DigitL repr
ltailDigitL = \case
  (OneL _) -> undefined
  (TwoL _ b) -> OneL b
  (ThreeL _ b c) -> TwoL b c
  (FourL _ b c d) -> ThreeL b c d

lheadDigitN :: DigitN repr l -> Node repr l
lheadDigitN = \case
  (OneN a) -> a
  (TwoN a _) -> a
  (ThreeN a _ _) -> a
  (FourN a _ _ _) -> a

ltailDigitN :: DigitN repr l -> DigitN repr l
ltailDigitN = \case
  (OneN _) -> undefined
  (TwoN _ b) -> OneN b
  (ThreeN _ b c) -> TwoN b c
  (FourN _ b c d) -> ThreeN b c d

viewr :: LiftSegMeasure repr => FingerTree repr -> ViewR repr
viewr = \case
  FingerTree_Empty -> EmptyR
  FingerTree_Single x -> FingerTree_Empty :> x
  FingerTree_Deep _ pr m (OneL x) -> rotLR pr m :> x
  FingerTree_Deep _ pr t sf -> deepL pr t (rtailDigitL sf) :> rheadDigitL sf

viewNR :: LiftSegMeasure repr => DeepTree repr l -> ViewNR repr l
viewNR = \case
  DeepTree_Empty -> EmptyNR
  DeepTree_Single x -> DeepTree_Empty :>> x
  DeepTree_Deep _ pr t (OneN x) -> rotNR pr t :>> x
  DeepTree_Deep _ pr t sf -> deepN pr t (rtailDigitN sf) :>> rheadDigitN sf

rotLR :: LiftSegMeasure repr => DigitL repr -> DeepTree repr 'Level_Leaf -> FingerTree repr
rotLR pr t = case viewNR t of
  EmptyNR -> digitToTreeL pr
  t' :>> a -> FingerTree_Deep
    (measureDigitL pr %<> measureDeepTree t)
    pr
    t'
    (nodeToDigitL a)

rotNR :: LiftSegMeasure repr => DigitN repr l -> DeepTree repr ('Level_Branch l) -> DeepTree repr l
rotNR pr t = case viewNR t of
  EmptyNR -> digitToTreeN pr
  t' :>> a -> DeepTree_Deep
    (measureDigitN pr %<> measureDeepTree t)
    pr
    t'
    (nodeToDigitN a)

rheadDigitL :: DigitL repr -> Elem repr
rheadDigitL = \case
  (OneL a) -> a
  (TwoL _ b) -> b
  (ThreeL _ _ c) -> c
  (FourL _ _ _ d) -> d

rtailDigitL :: DigitL repr -> DigitL repr
rtailDigitL = \case
  (OneL _) -> undefined
  (TwoL a _) -> OneL a
  (ThreeL a b _) -> TwoL a b
  (FourL a b c _) -> ThreeL a b c

rheadDigitN :: DigitN repr l -> Node repr l
rheadDigitN = \case
  (OneN a) -> a
  (TwoN _ b) -> b
  (ThreeN _ _ c) -> c
  (FourN _ _ _ d) -> d

rtailDigitN :: DigitN repr l -> DigitN repr l
rtailDigitN = \case
  (OneN _) -> undefined
  (TwoN a _) -> OneN a
  (ThreeN a b _) -> TwoN a b
  (FourN a b c _) -> ThreeN a b c

digitToTreeL :: LiftSegMeasure repr => DigitL repr -> FingerTree repr
digitToTreeL = \case
  OneL a -> FingerTree_Single a
  TwoL a b -> deepL (OneL a) DeepTree_Empty (OneL b)
  ThreeL a b c -> deepL (TwoL a b) DeepTree_Empty (OneL c)
  FourL a b c d -> deepL (TwoL a b) DeepTree_Empty (TwoL c d)

digitToTreeN :: LiftSegMeasure repr => DigitN repr l -> DeepTree repr l
digitToTreeN = \case
  OneN a -> DeepTree_Single a
  TwoN a b -> deepN (OneN a) DeepTree_Empty (OneN b)
  ThreeN a b c -> deepN (TwoN a b) DeepTree_Empty (OneN c)
  FourN a b c d -> deepN (TwoN a b) DeepTree_Empty (TwoN c d)

----------------
-- Concatenation
----------------

instance LiftSegMeasure repr => Semigroup (FingerTree repr) where
  (<>) = (><)

instance LiftSegMeasure repr => Monoid (FingerTree repr) where
  mempty = empty

-- | /O(log(min(n1,n2)))/. Concatenate two sequences.
(><) :: LiftSegMeasure repr => FingerTree repr -> FingerTree repr -> FingerTree repr
s >< t = case (s, t) of
  (FingerTree_Empty, x) -> x
  (x, FingerTree_Empty) -> x
  (FingerTree_Single x, xs) -> x <| xs
  (xs, FingerTree_Single x) -> xs |> x
  (FingerTree_Deep _ pr1 x1 sf1, FingerTree_Deep _ pr2 x2 sf2) ->
    deepL pr1 t' sf2
   where
    !t' = addDigitsL0 x1 sf1 pr2 x2

addDigitsL0 :: LiftSegMeasure repr => DeepTree repr 'Level_Leaf -> DigitL repr -> DigitL repr -> DeepTree repr 'Level_Leaf -> DeepTree repr 'Level_Leaf
addDigitsL0 m1 (OneL a) (OneL b) m2 =
    appendTree1 m1 (node2L a b) m2
addDigitsL0 m1 (OneL a) (TwoL b c) m2 =
    appendTree1 m1 (node3L a b c) m2
addDigitsL0 m1 (OneL a) (ThreeL b c d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (OneL a) (FourL b c d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (TwoL a b) (OneL c) m2 =
    appendTree1 m1 (node3L a b c) m2
addDigitsL0 m1 (TwoL a b) (TwoL c d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (TwoL a b) (ThreeL c d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (TwoL a b) (FourL c d e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (ThreeL a b c) (OneL d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (ThreeL a b c) (TwoL d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (ThreeL a b c) (ThreeL d e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (ThreeL a b c) (FourL d e f g) m2 =
    appendTree3 m1 (node3L a b c) (node2L d e) (node2L f g) m2
addDigitsL0 m1 (FourL a b c d) (OneL e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (FourL a b c d) (TwoL e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (FourL a b c d) (ThreeL e f g) m2 =
    appendTree3 m1 (node3L a b c) (node2L d e) (node2L f g) m2
addDigitsL0 m1 (FourL a b c d) (FourL e f g h) m2 =
    appendTree3 m1 (node3L a b c) (node3L d e f) (node2L g h) m2

appendTree1 :: LiftSegMeasure repr => DeepTree repr l -> Node repr l -> DeepTree repr l -> DeepTree repr l
appendTree1 DeepTree_Empty !a xs =
  a <<| xs
appendTree1 xs !a DeepTree_Empty =
  xs |>> a
appendTree1 (DeepTree_Single x) !a xs =
  x <<| a <<| xs
appendTree1 xs !a (DeepTree_Single x) =
  xs |>> a |>> x
appendTree1 (DeepTree_Deep _ pr1 m1 sf1) a (DeepTree_Deep _ pr2 m2 sf2) =
  deepN pr1 t sf2
 where
  !t = addDigits1 m1 sf1 a pr2 m2

addDigits1 :: LiftSegMeasure repr => DeepTree repr ('Level_Branch l) -> DigitN repr l -> Node repr l -> DigitN repr l -> DeepTree repr ('Level_Branch l) -> DeepTree repr ('Level_Branch l)
addDigits1 m1 (OneN a) b (OneN c) m2 =
    appendTree1 m1 (node3N a b c) m2
addDigits1 m1 (OneN a) b (TwoN c d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits1 m1 (OneN a) b (ThreeN c d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (OneN a) b (FourN c d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (TwoN a b) c (OneN d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits1 m1 (TwoN a b) c (TwoN d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (TwoN a b) c (ThreeN d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (TwoN a b) c (FourN d e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (ThreeN a b c) d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (ThreeN a b c) d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (ThreeN a b c) d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (ThreeN a b c) d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits1 m1 (FourN a b c d) e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (FourN a b c d) e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (FourN a b c d) e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits1 m1 (FourN a b c d) e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2

appendTree2 :: LiftSegMeasure repr => DeepTree repr l -> Node repr l -> Node repr l -> DeepTree repr l -> DeepTree repr l
appendTree2 DeepTree_Empty !a !b xs =
  a <<| b <<| xs
appendTree2 xs !a !b DeepTree_Empty =
  xs |>> a |>> b
appendTree2 (DeepTree_Single x) a b xs =
  x <<| a <<| b <<| xs
appendTree2 xs a b (DeepTree_Single x) =
  xs |>> a |>> b |>> x
appendTree2 (DeepTree_Deep _ pr1 m1 sf1) a b (DeepTree_Deep _ pr2 m2 sf2) =
  deepN pr1 m sf2
 where
  !m = addDigits2 m1 sf1 a b pr2 m2

addDigits2 :: LiftSegMeasure repr => DeepTree repr ('Level_Branch l) -> DigitN repr l -> Node repr l -> Node repr l -> DigitN repr l -> DeepTree repr ('Level_Branch l) -> DeepTree repr ('Level_Branch l)
addDigits2 m1 (OneN a) b c (OneN d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits2 m1 (OneN a) b c (TwoN d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits2 m1 (OneN a) b c (ThreeN d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (OneN a) b c (FourN d e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (TwoN a b) c d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits2 m1 (TwoN a b) c d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (TwoN a b) c d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (TwoN a b) c d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (ThreeN a b c) d e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (ThreeN a b c) d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (ThreeN a b c) d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (ThreeN a b c) d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits2 m1 (FourN a b c d) e f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (FourN a b c d) e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (FourN a b c d) e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits2 m1 (FourN a b c d) e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2

appendTree3 :: LiftSegMeasure repr => DeepTree repr l -> Node repr l -> Node repr l -> Node repr l -> DeepTree repr l -> DeepTree repr l
appendTree3 DeepTree_Empty !a !b !c xs =
    a <<| b <<| c <<| xs
appendTree3 xs !a !b !c DeepTree_Empty =
    xs |>> a |>> b |>> c
appendTree3 (DeepTree_Single x) a b c xs =
    x <<| a <<| b <<| c <<| xs
appendTree3 xs a b c (DeepTree_Single x) =
    xs |>> a |>> b |>> c |>> x
appendTree3 (DeepTree_Deep _ pr1 m1 sf1) a b c (DeepTree_Deep _ pr2 m2 sf2) =
  deepN pr1 t sf2
 where
  !t = addDigits3 m1 sf1 a b c pr2 m2

addDigits3 :: LiftSegMeasure repr => DeepTree repr ('Level_Branch l) -> DigitN repr l -> Node repr l -> Node repr l -> Node repr l -> DigitN repr l -> DeepTree repr ('Level_Branch l) -> DeepTree repr ('Level_Branch l)
addDigits3 m1 (OneN a) !b !c !d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits3 m1 (OneN a) b c d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits3 m1 (OneN a) b c d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (OneN a) b c d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (TwoN a b) !c !d !e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits3 m1 (TwoN a b) c d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (TwoN a b) c d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (TwoN a b) c d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (ThreeN a b c) !d !e !f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (ThreeN a b c) d e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (ThreeN a b c) d e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (ThreeN a b c) d e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits3 m1 (FourN a b c d) !e !f !g (OneN h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (FourN a b c d) e f g (TwoN h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (FourN a b c d) e f g (ThreeN h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits3 m1 (FourN a b c d) e f g (FourN h i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2

appendTree4 :: LiftSegMeasure repr => DeepTree repr l -> Node repr l -> Node repr l -> Node repr l -> Node repr l -> DeepTree repr l -> DeepTree repr l
appendTree4 DeepTree_Empty !a !b !c !d xs =
    a <<| b <<| c <<| d <<| xs
appendTree4 xs !a !b !c !d DeepTree_Empty =
    xs |>> a |>> b |>> c |>> d
appendTree4 (DeepTree_Single x) a b c d xs =
    x <<| a <<| b <<| c <<| d <<| xs
appendTree4 xs a b c d (DeepTree_Single x) =
    xs |>> a |>> b |>> c |>> d |>> x
appendTree4 (DeepTree_Deep _ pr1 m1 sf1) a b c d (DeepTree_Deep _ pr2 m2 sf2) =
    deepN pr1 t sf2
 where
  !t = addDigits4 m1 sf1 a b c d pr2 m2

{-# INLINE addDigits4 #-}
addDigits4 :: LiftSegMeasure repr => DeepTree repr ('Level_Branch l) -> DigitN repr l -> Node repr l -> Node repr l -> Node repr l -> Node repr l -> DigitN repr l -> DeepTree repr ('Level_Branch l) -> DeepTree repr ('Level_Branch l)
addDigits4 m1 (OneN a) !b !c !d !e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits4 m1 (OneN a) b c d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits4 m1 (OneN a) b c d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (OneN a) b c d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (TwoN a b) !c !d !e !f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits4 m1 (TwoN a b) c d e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (TwoN a b) c d e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (TwoN a b) c d e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (ThreeN a b c) !d !e !f !g (OneN h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (ThreeN a b c) d e f g (TwoN h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (ThreeN a b c) d e f g (ThreeN h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (ThreeN a b c) d e f g (FourN h i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2
addDigits4 m1 (FourN a b c d) !e !f !g !h (OneN i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (FourN a b c d) !e !f !g !h (TwoN i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (FourN a b c d) !e !f !g !h (ThreeN i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2
addDigits4 m1 (FourN a b c d) !e !f !g !h (FourN i j k l) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node3N j k l) m2

----------------
-- 4.4 Splitting
----------------

data Split t a = Split t a t

data SearchResult repr
    = Position (FingerTree repr) {-# UNPACK #-} !(Elem repr) (FingerTree repr)
        -- ^ A tree opened at a particular element: the prefix to the
        -- left, the element, and the suffix to the right.
    | OnLeft
        -- ^ A position to the left of the sequence, indicating that the
        -- predicate is 'True' at both ends.
    | OnRight
        -- ^ A position to the right of the sequence, indicating that the
        -- predicate is 'False' at both ends.
    | Nowhere
        -- ^ No position in the tree, returned if the predicate is 'True'
        -- at the left end and 'False' at the right end.  This will not
        -- occur if the predicate in monotonic on the tree.

search
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> FingerTree repr
  -> m (SearchResult repr)
search p t = do
  let vt = measureFingerTree t
  p_left <- p mempty' vt
  p_right <- p vt mempty'
  case (p_left, p_right) of
    (True, True) -> pure OnLeft
    (False, True) -> searchTree p mempty' t mempty' >>= \case
      Split l x r -> pure $ Position l x r
    (False, False) -> pure OnRight
    (True, False) -> pure Nowhere

searchTree
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> FingerTree repr
  -> Measure repr
  -> m (Split (FingerTree repr) (Elem repr))
searchTree p vl t vr = case t of
  FingerTree_Empty -> illegal_argument "searchTree"
  FingerTree_Single x -> pure $ Split FingerTree_Empty x FingerTree_Empty
  FingerTree_Deep _ pr m sf ->
    let vlp = vl %<> measureDigitL pr
        vlpm = vlp %<> vm
        vmsr = vm %<> vsr
        vsr = measureDigitL sf %<> vr
        vm = measureDeepTree m
     in p vlp vmsr >>= \case
          True -> do
            Split l x r <- searchDigitL p vl pr vmsr
            let l' = case l of
                  Nothing -> FingerTree_Empty
                  Just lx -> digitToTreeL lx
            pure $ Split l' x (deepLL r m sf)
          False -> p vlpm vsr >>= \case
            True -> do
              Split ml xs mr <- searchDeepTree p vlp m vsr
              Split l x r <- searchLeaf p
                (vlp %<> measureDeepTree ml)
                xs
                (measureDeepTree mr %<> vsr)
              pure $ Split (deepLR pr ml l) x (deepLL r mr sf)
            False -> do
              Split l x r <- searchDigitL p vlpm sf vr
              let r' = case r of
                    Nothing -> FingerTree_Empty
                    Just rx -> digitToTreeL rx
              pure $ Split (deepLR pr m l) x r'

searchDeepTree
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> DeepTree repr l
  -> Measure repr
  -> m (Split (DeepTree repr l) (Node repr l))
searchDeepTree p vl t vr = case t of
  DeepTree_Empty -> illegal_argument "searchTree"
  DeepTree_Single x -> pure $ Split DeepTree_Empty x DeepTree_Empty
  DeepTree_Deep _ pr m sf ->
    let vlp = vl %<> measureDigitN pr
        vlpm = vlp %<> vm
        vmsr = vm %<> vsr
        vsr = measureDigitN sf %<> vr
        vm = measureDeepTree m
     in p vlp vmsr >>= \case
          True -> do
            Split l x r <- searchDigitN p vl pr vmsr
            let l' = case l of
                       Nothing -> DeepTree_Empty
                       Just lx -> digitToTreeN lx
            pure $ Split l' x (deepNL r m sf)
          False -> p vlpm vsr >>= \case
            True -> do
              Split ml xs mr <- searchDeepTree p vlp m vsr
              Split l x r <- searchNode p
                (vlp %<> measureDeepTree ml)
                xs
                (measureDeepTree mr %<> vsr)
              pure $ Split (deepNR pr ml l) x (deepNL r mr sf)
            False -> do
              Split l x r <- searchDigitN p vlpm sf vr
              let r' = case r of
                    Nothing -> DeepTree_Empty
                    Just rx -> digitToTreeN rx
              pure $ Split (deepNR pr m l) x r'

searchLeaf
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> Node repr 'Level_Leaf
  -> Measure repr
  -> m (Split (Maybe (DigitL repr)) (Elem repr))
searchLeaf p vl n vr = case n of
  Node_Leaf2 _ a b ->
    let va = vl %<> measureSeg a
        vb = measureSeg b %<> vr
     in flip fmap (p va vb) \case
          True -> Split Nothing a (Just (OneL b))
          False -> Split (Just (OneL a)) b Nothing
  Node_Leaf3 _ a b c ->
    let va = vl %<> measureSeg a
        vab = va %<> measureSeg b
        vc = measureSeg c %<> vr
        vbc = measureSeg b %<> vc
     in p va vbc >>= \case
          True -> pure $ Split Nothing a (Just (TwoL b c))
          False -> p vab vc >>= \case
            True -> pure $ Split (Just (OneL a)) b (Just (OneL c))
            False -> pure $ Split (Just (TwoL a b)) c Nothing

searchNode
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> Node repr ('Level_Branch l)
  -> Measure repr
  -> m (Split (Maybe (DigitN repr l)) (Node repr l))
searchNode p vl n vr = case n of
  Node_Branch2 _ a b ->
    let va = vl %<> measureNode a
        vb = measureNode b %<> vr
     in flip fmap (p va vb) \case
          True -> Split Nothing a (Just (OneN b))
          False -> Split (Just (OneN a)) b Nothing
  Node_Branch3 _ a b c ->
    let va = vl %<> measureNode a
        vab = va %<> measureNode b
        vc = measureNode c %<> vr
        vbc = measureNode b %<> vc
     in p va vbc >>= \case
          True -> pure $ Split Nothing a (Just (TwoN b c))
          False -> p vab vc >>= \case
            True -> pure $ Split (Just (OneN a)) b (Just (OneN c))
            False -> pure $ Split (Just (TwoN a b)) c Nothing


searchDigitL
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> DigitL repr
  -> Measure repr
  -> m (Split (Maybe (DigitL repr)) (Elem repr))
searchDigitL p vl d' vr = case d' of
  OneL a -> vl `seq` vr `seq` pure (Split Nothing a Nothing)
  TwoL a b ->
    let va = vl %<> measureSeg a
        vb = measureSeg b %<> vr
     in flip fmap (p va vb) \case
          True -> Split Nothing a (Just (OneL b))
          False -> Split (Just (OneL a)) b Nothing
  ThreeL a b c ->
    let va = vl %<> measureSeg a
        vab = va %<> measureSeg b
        vc = measureSeg c %<> vr
        vbc = measureSeg b %<> vc
     in p va vbc >>= \case
         True -> pure $ Split Nothing a (Just (TwoL b c))
         False -> p vab vc >>= \case
           True -> pure $ Split (Just (OneL a)) b (Just (OneL c))
           False -> pure $ Split (Just (TwoL a b)) c Nothing
  FourL a b c d ->
    let va = vl %<> measureSeg a
        vab = va %<> measureSeg b
        vabc = vab %<> measureSeg c
        vd = measureSeg d %<> vr
        vcd = measureSeg c %<> vd
        vbcd = measureSeg b %<> vcd
     in p va vbcd >>= \case
          True -> pure $ Split Nothing a (Just (ThreeL b c d))
          False -> p vab vcd >>= \case
            True -> pure $ Split (Just (OneL a)) b (Just (TwoL c d))
            False -> p vabc vd >>= \case
              True -> pure $ Split (Just (TwoL a b)) c (Just (OneL d))
              False -> pure $ Split (Just (ThreeL a b c)) d Nothing

searchDigitN
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> Measure repr -> m Bool)
  -> Measure repr
  -> DigitN repr l
  -> Measure repr
  -> m (Split (Maybe (DigitN repr l)) (Node repr l))
searchDigitN p vl d' vr = case d' of
  OneN a -> vl `seq` vr `seq` pure (Split Nothing a Nothing)
  TwoN a b ->
    let va = vl %<> measureNode a
        vb = measureNode b %<> vr
     in flip fmap (p va vb) \case
          True -> Split Nothing a (Just (OneN b))
          False -> Split (Just (OneN a)) b Nothing
  ThreeN a b c ->
    let va = vl %<> measureNode a
        vab = va %<> measureNode b
        vc = measureNode c %<> vr
        vbc = measureNode b %<> vc
     in p va vbc >>= \case
         True -> pure $ Split Nothing a (Just (TwoN b c))
         False -> p vab vc >>= \case
           True -> pure $ Split (Just (OneN a)) b (Just (OneN c))
           False -> pure $ Split (Just (TwoN a b)) c Nothing
  FourN a b c d ->
    let va = vl %<> measureNode a
        vab = va %<> measureNode b
        vabc = vab %<> measureNode c
        vd = measureNode d %<> vr
        vcd = measureNode c %<> vd
        vbcd = measureNode b %<> vcd
     in p va vbcd >>= \case
          True -> pure $ Split Nothing a (Just (ThreeN b c d))
          False -> p vab vcd >>= \case
            True -> pure $ Split (Just (OneN a)) b (Just (TwoN c d))
            False -> p vabc vd >>= \case
              True -> pure $ Split (Just (TwoN a b)) c (Just (OneN d))
              False -> pure $ Split (Just (ThreeN a b c)) d Nothing

deepLL
  :: LiftSegMeasure repr
  => Maybe (DigitL repr)
  -> DeepTree repr 'Level_Leaf
  -> DigitL repr
  -> FingerTree repr
deepLL mpr m sf = case mpr of
  Nothing -> rotLL m sf
  Just pr -> deepL pr m sf

deepNL
  :: LiftSegMeasure repr
  => Maybe (DigitN repr l)
  -> DeepTree repr ('Level_Branch l)
  -> DigitN repr l
  -> DeepTree repr l
deepNL mpr m sf = case mpr of
  Nothing -> rotNL m sf
  Just pr -> deepN pr m sf

deepLR
  :: LiftSegMeasure repr
  => DigitL repr
  -> DeepTree repr 'Level_Leaf
  -> Maybe (DigitL repr)
  -> FingerTree repr
deepLR pr m = \case
  Nothing -> rotLR pr m
  Just sf -> deepL pr m sf

deepNR
  :: LiftSegMeasure repr
  => DigitN repr l
  -> DeepTree repr ('Level_Branch l)
  -> Maybe (DigitN repr l)
  -> DeepTree repr l
deepNR pr m = \case
  Nothing -> rotNR pr m
  Just sf -> deepN pr m sf

illegal_argument :: String -> a
illegal_argument name =
    error $ "Logic error: " ++ name ++ " called with illegal argument"

-- | /O(log(min(i,n-i)))/. Split a sequence at a point where the predicate
-- on the accumulated measure of the prefix changes from 'False' to 'True'.
--
-- For predictable results, one should ensure that there is only one such
-- point, i.e. that the predicate is /monotonic/.
split
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> FingerTree repr
  -> m (FingerTree repr, FingerTree repr)
split _ FingerTree_Empty = pure $ (FingerTree_Empty, FingerTree_Empty)
split p xs = do
  Split l x r <- splitTree p mempty' xs
  flip fmap (p (measureFingerTree xs)) $ \case
    True -> (l, x <| r)
    False -> (xs, FingerTree_Empty)

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'takeUntil' p t@ is the largest
-- prefix of @t@ whose measure does not satisfy @p@.
--
-- *  @'takeUntil' p t = 'fst' ('split' p t)@
takeUntil
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> FingerTree repr
  -> m (FingerTree repr)
takeUntil p = fmap fst . split p

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'dropUntil' p t@ is the rest of @t@
-- after removing the largest prefix whose measure does not satisfy @p@.
--
-- * @'dropUntil' p t = 'snd' ('split' p t)@
dropUntil
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> FingerTree repr
  -> m (FingerTree repr)
dropUntil p = fmap snd . split p

splitTree
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> FingerTree repr
  -> m (Split (FingerTree repr) (Elem repr))
splitTree p i = \case
  FingerTree_Empty -> illegal_argument "splitTree"
  FingerTree_Single x -> pure $ Split FingerTree_Empty x FingerTree_Empty
  FingerTree_Deep _ pr m sf ->
    let vpr = i %<> measureDigitL pr
        vm = vpr %<> measureDeepTree m
     in p vpr >>= \case
          True -> do
            Split l x r <- splitDigitL p i pr
            let l' = case l of
                  Nothing -> FingerTree_Empty
                  Just lx -> digitToTreeL lx
            pure $ Split l' x (deepLL r m sf)
          False -> p vm >>= \case
            True -> do
              Split ml xs mr <- splitDeepTree p vpr m
              Split l x r <- splitLeaf p (vpr %<> measureDeepTree ml) xs
              pure $ Split (deepLR pr ml l) x (deepLL r mr sf)
            False -> do
              Split l x r <- splitDigitL p vm sf
              let r' = case r of
                    Nothing -> FingerTree_Empty
                    Just rx -> digitToTreeL rx
              pure $ Split (deepLR pr m l) x r'

splitDeepTree
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> DeepTree repr l
  -> m (Split (DeepTree repr l) (Node repr l))
splitDeepTree p i = \case
  DeepTree_Empty -> illegal_argument "splitDeepTree"
  DeepTree_Single x -> pure $ Split DeepTree_Empty x DeepTree_Empty
  DeepTree_Deep _ pr m sf ->
    let vpr = i %<> measureDigitN pr
        vm = vpr %<> measureDeepTree m
     in p vpr >>= \case
          True -> do
            Split l x r <- splitDigitN p i pr
            let l' = case l of
                  Nothing -> DeepTree_Empty
                  Just lx -> digitToTreeN lx
            pure $ Split l' x (deepNL r m sf)
          False -> p vm >>= \case
            True -> do
              Split ml xs mr <- splitDeepTree p vpr m
              Split l x r <- splitNode p (vpr %<> measureDeepTree ml) xs
              pure $ Split (deepNR pr ml l) x (deepNL r mr sf)
            False -> do
              Split l x r <- splitDigitN p vm sf
              let r' = case r of
                    Nothing -> DeepTree_Empty
                    Just rx -> digitToTreeN rx
              pure $ Split (deepNR pr m l) x r'

splitLeaf
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> Node repr 'Level_Leaf
  -> m (Split (Maybe (DigitL repr)) (Elem repr))
splitLeaf p i = \case
  Node_Leaf2 _ a b -> flip fmap (p (i %<> measureSeg a)) $ \case
    True -> Split Nothing a (Just (OneL b))
    False -> Split (Just (OneL a)) b Nothing
  Node_Leaf3 _ a b c -> p (i %<> measureSeg a) >>= \case
    True -> pure $ Split Nothing a (Just (TwoL b c))
    False -> p (i %<> measureSeg a %<> measureSeg b) >>= \case
      True -> pure $ Split (Just (OneL a)) b (Just (OneL c))
      False -> pure $ Split (Just (TwoL a b)) c Nothing

splitNode
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> Node repr ('Level_Branch l)
  -> m (Split (Maybe (DigitN repr l)) (Node repr l))
splitNode p i = \case
  Node_Branch2 _ a b -> flip fmap (p (i %<> measureNode a)) $ \case
    True -> Split Nothing a (Just (OneN b))
    False -> Split (Just (OneN a)) b Nothing
  Node_Branch3 _ a b c -> p (i %<> measureNode a) >>= \case
    True -> pure $ Split Nothing a (Just (TwoN b c))
    False -> p (i %<> measureNode a %<> measureNode b) >>= \case
      True -> pure $ Split (Just (OneN a)) b (Just (OneN c))
      False -> pure $ Split (Just (TwoN a b)) c Nothing

splitDigitL
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> DigitL repr
  -> m (Split (Maybe (DigitL repr)) (Elem repr))
splitDigitL p i = \case
  OneL a -> i `seq` pure $ Split Nothing a Nothing
  TwoL a b -> flip fmap (p (i %<> measureSeg a)) \case
    True -> Split Nothing a (Just (OneL b))
    False -> Split (Just (OneL a)) b Nothing
  ThreeL a b c -> p (i %<> measureSeg a) >>= \case
    True -> pure $ Split Nothing a (Just (TwoL b c))
    False -> p (i %<> measureSeg a %<> measureSeg b) >>= \case
      True -> pure $ Split (Just (OneL a)) b (Just (OneL c))
      False -> pure $ Split (Just (TwoL a b)) c Nothing
  FourL a b c d -> p (i %<> measureSeg a) >>= \case
    True -> pure $ Split Nothing a (Just (ThreeL b c d))
    False -> p (i %<> measureSeg a %<> measureSeg b) >>= \case
      True -> pure $ Split (Just (OneL a)) b (Just (TwoL c d))
      False -> p (i %<> measureSeg a %<> measureSeg b %<> measureSeg c) >>= \case
        True -> pure $ Split (Just (TwoL a b)) c (Just (OneL d))
        False -> pure $ Split (Just (ThreeL a b c)) d Nothing

splitDigitN
  :: (LiftSegMeasure repr, Monad m)
  => (Measure repr -> m Bool)
  -> Measure repr
  -> DigitN repr l
  -> m (Split (Maybe (DigitN repr l)) (Node repr l))
splitDigitN p i = \case
  OneN a -> i `seq` pure $ Split Nothing a Nothing
  TwoN a b -> flip fmap (p (i %<> measureNode a)) \case
    True -> Split Nothing a (Just (OneN b))
    False -> Split (Just (OneN a)) b Nothing
  ThreeN a b c -> p (i %<> measureNode a) >>= \case
    True -> pure $ Split Nothing a (Just (TwoN b c))
    False -> p (i %<> measureNode a %<> measureNode b) >>= \case
      True -> pure $ Split (Just (OneN a)) b (Just (OneN c))
      False -> pure $ Split (Just (TwoN a b)) c Nothing
  FourN a b c d -> p (i %<> measureNode a) >>= \case
    True -> pure $ Split Nothing a (Just (ThreeN b c d))
    False -> p (i %<> measureNode a %<> measureNode b) >>= \case
      True -> pure $ Split (Just (OneN a)) b (Just (TwoN c d))
      False -> p (i %<> measureNode a %<> measureNode b %<> measureNode c) >>= \case
        True -> pure $ Split (Just (TwoN a b)) c (Just (OneN d))
        False -> pure $ Split (Just (ThreeN a b c)) d Nothing

-- TODO: do lookup if necessary

------------------
-- Transformations
------------------

-- | /O(n)/. The reverse of a sequence.
reverse
  :: LiftSegMeasure repr
  => FingerTree repr
  -> FingerTree repr
reverse = \case
  FingerTree_Empty -> FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single x
  FingerTree_Deep _ pr t sf -> deepL
    (reverseDigitL sf)
    (reverseDeep reverseLeaf t)
    (reverseDigitL pr)

reverseDeep
  :: LiftSegMeasure repr
  => (Node repr l -> Node repr l)
  -> DeepTree repr l
  -> DeepTree repr l
reverseDeep f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single (f x)
  DeepTree_Deep _ pr t sf -> deepN
    (reverseDigitN f sf)
    (reverseDeep (reverseNode f) t)
    (reverseDigitN f pr)

reverseDigitL
  :: LiftSegMeasure repr
  => DigitL repr
  -> DigitL repr
reverseDigitL = \case
  OneL x -> OneL x
  TwoL x y -> TwoL y x
  ThreeL x y z -> ThreeL z y x
  FourL w x y z -> FourL z y x w

reverseDigitN
  :: LiftSegMeasure repr
  => (Node repr l -> Node repr l)
  -> DigitN repr l
  -> DigitN repr l
reverseDigitN f = \case
  OneN x -> OneN (f x)
  TwoN x y -> TwoN (f y) (f x)
  ThreeN x y z -> ThreeN (f z) (f y) (f x)
  FourN w x y z -> FourN (f z) (f y) (f x) (f w)

reverseNode
  :: LiftSegMeasure repr
  => (Node repr l -> Node repr l)
  -> Node repr ('Level_Branch l)
  -> Node repr ('Level_Branch l)
reverseNode f = \case
  Node_Branch2 _ a b -> node2N (f b) (f a)
  Node_Branch3 _ a b c -> node3N (f c) (f b) (f a)

reverseLeaf
  :: LiftSegMeasure repr
  => Node repr 'Level_Leaf
  -> Node repr 'Level_Leaf
reverseLeaf = \case
  Node_Leaf2 _ a b -> node2L b a
  Node_Leaf3 _ a b c -> node3L c b a


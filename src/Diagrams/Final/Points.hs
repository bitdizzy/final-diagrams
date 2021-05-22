{-# LANGUAGE BlockArguments #-}
module Diagrams.Final.Points where

import Diagrams.Final.Core

mirror :: (Spatial repr, Num' n repr) => repr (Point repr n) -> repr (Point repr n)
mirror = reflectThrough origin

reflectThrough :: (Spatial repr, Num' n repr) => repr (Point repr n) -> repr (Point repr n) -> repr (Point repr n)
reflectThrough o = relativeF o negated'

centroid :: (Spatial repr, Functor' t repr, Foldable' t repr, Fractional' n repr) => repr (t (Point repr n)) -> repr (Maybe' repr (Point repr n))
centroid ps = meanV ps

meanV :: (Spatial repr, Functor' t repr, Foldable' t repr, Additive' v repr, Fractional' a repr) => repr (t (v a)) -> repr (Maybe' repr (v a))
meanV ps = fmap' (uncurry' $ lam2 (%^/)) $ foldl1' (fmap' (lam \v -> tup2' v 1) ps) $ lam2 $ \xc yc ->
  tup2' (pi1' xc %^+^ pi1' yc) (pi2' xc %+ pi2' yc)

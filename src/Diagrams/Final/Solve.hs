{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE QuantifiedConstraints #-}
module Diagrams.Final.Solve where

import Diagrams.Final.Core

quadForm
  :: forall repr d. (Spatial repr, Floating' repr d, Ord' repr d)
  => repr d
  -> repr d
  -> repr d
  -> repr (Maybe' repr (List' repr d))
quadForm a b c = if' (a %== num 0)
  (if' (b %== num 0)
    (if' (c %== num 0) nothing' (just' nil'))
    (just' (pure' (negate' c %/ b)))
  )
  ( let d = b %^ (num 2) %- num 4 %* a %* c
        q = num (-1) %/ num 2 %* (b %+ signum' b %* sqrt' d)
     in ordering' (compare' d (num 0)) \case
          LT -> just' nil'
          EQ -> if' (b %== num 0)
            (just' $ val1 [sqrt' (negate' c %/ a), negate' (sqrt' (negate' c %/ a))])
            (just' $ pure' (negate' b %/ num 2 %* a))
          GT -> just' $ val1 $ [q %/ a, c %/ q]
  )

aboutZero' :: (Numerics repr, Ord' repr a, Num' repr a) => repr a -> repr a -> repr Bool
aboutZero' tolerance x = abs' x %<= tolerance

belowZero' :: (Numerics repr, Ord' repr a, Num' repr a) => repr a -> repr a -> repr Bool
belowZero' tolerance x = x %<= negate' (abs' tolerance)

aboveZero' :: (Ord' repr a, Num' repr a) => repr a -> repr a -> repr Bool
aboveZero' tolerance x = x %>= (abs' tolerance)

cubForm
  :: (Spatial repr, RealFloat' repr d, Ord' repr d, Show d, forall a. Show a => Show (repr a))
  => repr d
  -> repr d
  -> repr d
  -> repr d
  -> repr (Maybe' repr (List' repr d))
cubForm a btimes3 ctimes3 d =
  let b = btimes3 %/ num 3
      c = ctimes3 %/ num 3
      d1 = a %* c %- b %* b
      d2 = a %* d %- b %* c
      d3 = b %* d %- c %* c
      disc {- riminant #-} = num 4 %* d1 %* d3 %- d2 %* d2
      -- Calculate a root with two different depressions
      -- for the smallest and largest root.
      -- Largest root, far from 0
      a_max = a
      c_max = d1
      d_max = num (-2) %* b %* d1 %+ a %* d2
      -- Smallest, close to 0 so invert the polynomial
      a_min = d
      c_min = d3
      d_min = negate' d %* d2 %+ num 2 %* c %* d3
      -- the case where there is one real root
      branch1 =
        -- test for whether the max or min depression coefficients
        -- are more numerically accurate.
        let depressionTest = b %^ num 3 %* d %>= a %* (c %^ num 3)
            (a', c', d') = untup3 $ if' depressionTest
              (tup3' a_max c_max d_max)
              (tup3' a_min c_min d_min)
            t0 = signum' d' %* abs' a' %* sqrt' (negate' disc)
            t1 = negate' d' %+ t0
            p = (t1 %/ num 2) %** (fnum (recip 3))
            -- This equality test is allegedly fine
            q = if' (t1 %== t0) (negate' p) (negate' c' %/ p)
            x1 = if' (c' %<= num 0) (p %+ q) (negate' d' %/ (p %^ num 2 %+ q %^ num 2 %+ c'))
         in just' $ pure' $ if' depressionTest
              ((x1 %- b) %/ a)
              (negate' d %/ (x1 %- c))
      -- Three real roots, we use both depressions to solve the extermal
      -- roots and then find the middle root
      branch2 =
        let theta a' d' = fnum (1/3) %* abs' (atan2' (a' %* sqrt' disc) (negate' d'))
            x1 sqrtc' costheta' = num 2 %* sqrtc' %* costheta'
            x3 sqrtc' costheta' sintheta' =
              num 2 %* sqrtc' %* (fnum (-1/2) %* costheta' %- sqrt' (fnum (3 / 2)) %* sintheta')
            -- let_ actually shares expressions as opposed to metalanguage let
         in let_ (theta a_max d_max) \theta_max -> let_ (theta a_min d_min) \theta_min ->
             let_ (sqrt' (negate' c_max)) \sqrtc_max -> let_ (sqrt' (negate' c_min)) \sqrtc_min ->
              let_ (cos' theta_max) \costheta_max -> let_ (cos' theta_min) \costheta_min ->
               let_ (sin' theta_max) \sintheta_max -> let_ (sin' theta_min) \sintheta_min ->
                let_ (x1 sqrtc_max costheta_max) \x1_max ->
                 let_ (x3 sqrtc_max costheta_max sintheta_max) \x3_max ->
                  let_ (x1 sqrtc_min costheta_min) \x1_min ->
                   let_ (x3 sqrtc_min costheta_min sintheta_min) \x3_min ->
                    -- depressed homogeneous coordinates
                    let rootMax_x = if' (x1_max %+ x3_max %> num 2 %* b) x1_max x3_max
                        rootMax_w = a
                        rootMin_x = negate' d
                        rootMin_w = if' (x1_min %+ x3_min %< num 2 %* c) x1_min x3_min
                    -- undepressed homogeneous coordinates
                     in let_ (rootMax_x %- b) \big_x -> let_ rootMax_w \big_w ->
                          let_ rootMin_x \small_x -> let_ (rootMin_w %+ c) \small_w ->
                           let_ (big_w %* small_w) \e ->
                            let_ (negate' big_x %* small_w %- big_w %* small_x) \f ->
                             let_ (big_x %* small_x) \g ->
                               just' $ val1 $
                                 [ big_x %/ big_w
                                 , (c %* f %- b %* g) %/ (negate' b %* f %+ c %* e)
                                 , small_x %/ small_w
                                 ]
   -- Defer to the quadratic formula only when the leading term is 0. We should be able to handle
   -- even tiny a's.
   in if' (a %== num 0) (quadForm b c d) (if' (disc %< num 0) branch1 branch2)

{-
cubFormId :: Double -> Double -> Double -> Double -> Maybe [Double]
cubFormId a b c d = fmap (fmap runIdentity . unT1 . runIdentity) . unT1 . runIdentity $
  cubForm (Identity a) (Identity b) (Identity c) (Identity d)

coefficientsFor :: Double -> Double -> Double -> (Double, Double, Double, Double)
coefficientsFor r1 r2 r3 =
  ( 1
  , negate (r1 + r2 + r3)
  , r1 * r2 + r2 * r3 + r1 * r3
  , negate (r1 * r2 * r3)
  )

roundtrip :: Double -> Double -> Double -> Maybe [Double]
roundtrip r1 r2 r3 =
  let (a, b, c, d) = coefficientsFor r1 r2 r3
   in cubFormId a b c d
-}

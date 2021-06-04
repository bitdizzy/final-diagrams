{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Diagrams.Final.Attributes where

import Control.Monad
import Data.Colour
import Data.Colour.RGBSpace (RGB (..))
import Data.Colour.SRGB (toSRGB, sRGB)

import Diagrams.Final.Core

--
-- Basic units
--

none :: Scales repr => repr (Scaled repr Scalar)
none = output (num 0)

ultraThin :: Scales repr => repr (Scaled repr Scalar)
ultraThin = normalized (fnum 0.0005) `atLeast` output (fnum 0.5)

veryThin :: Scales repr => repr (Scaled repr Scalar)
veryThin = normalized (fnum 0.001) `atLeast` output (fnum 0.5)

thin :: Scales repr => repr (Scaled repr Scalar)
thin = normalized (fnum 0.002) `atLeast` output (fnum 0.5)

medium :: Scales repr => repr (Scaled repr Scalar)
medium = normalized (fnum 0.004) `atLeast` output (fnum 0.5)

thick :: Scales repr => repr (Scaled repr Scalar)
thick = normalized (fnum 0.0075) `atLeast` output (fnum 0.5)

veryThick :: Scales repr => repr (Scaled repr Scalar)
veryThick = normalized (fnum 0.01) `atLeast` output (fnum 0.5)

ultraThick :: Scales repr => repr (Scaled repr Scalar)
ultraThick = normalized (fnum 0.02) `atLeast` output (fnum 0.5)

tiny :: Scales repr => repr (Scaled repr Scalar)
tiny = normalized (fnum 0.01)

verySmall :: Scales repr => repr (Scaled repr Scalar)
verySmall = normalized (fnum 0.015)

small :: Scales repr => repr (Scaled repr Scalar)
small = normalized (fnum 0.023)

normal :: Scales repr => repr (Scaled repr Scalar)
normal = normalized (fnum 0.035)

large :: Scales repr => repr (Scaled repr Scalar)
large = normalized (fnum 0.05)

veryLarge :: Scales repr => repr (Scaled repr Scalar)
veryLarge = normalized (fnum 0.07)

huge :: Scales repr => repr (Scaled repr Scalar)
huge = normalized (fnum 0.1)

--
-- Strokes
--

class Scales repr => LineWidth repr style where
  lineWidth :: repr (Scaled repr Scalar) -> repr style

lw :: LineWidth repr style => repr (Scaled repr Scalar) -> repr style
lw = lineWidth

class Scales repr => StrokeDash repr style where
  dashing' :: repr (Scaled repr (List' repr Scalar, Scalar)) -> repr style

dashing :: StrokeDash repr style => repr (Scaled repr (List' repr Scalar)) -> repr (Scaled repr Scalar) -> repr style
dashing x y = dashing' $ liftA2' (lam2 tup2') x y

--
-- Colors
--
type Colour' = AlphaColour Scalar

class Val repr Colour' => LiftColour repr where
  toSRGBA :: repr Colour' -> repr (Scalar, Scalar, Scalar, Scalar)
  fromSRGBA :: repr (Scalar, Scalar, Scalar, Scalar) -> repr Colour'
  default toSRGBA :: Functor repr => repr Colour' -> repr (Scalar, Scalar, Scalar, Scalar)
  toSRGBA = fmap \c ->
   let RGB r g b = toSRGB (alphaToColour c)
    in (r, g, b, alphaChannel c)
  default fromSRGBA :: Functor repr => repr (Scalar, Scalar, Scalar, Scalar) -> repr Colour'
  fromSRGBA = fmap $ \(r, g, b, a) ->
    sRGB r g b `withOpacity` a

alphaToColour :: (Floating a, Ord a) => AlphaColour a -> Colour a
alphaToColour ac | alphaChannel ac == 0 = ac `over` black
                 | otherwise = darken (recip (alphaChannel ac)) (ac `over` black)

class Opacity repr style where
  opacity :: repr Scalar -> repr style

class FillOpacity repr style where
  fillOpacity :: repr Scalar -> repr style

class StrokeOpacity repr style where
  strokeOpacity :: repr Scalar -> repr style

--
-- Line stuff
--

data LineCap
   = LineCap_Butt
   | LineCap_Round
   | LineCap_Square

class Val repr LineCap => LiftLineCap repr where
  linecap :: repr LineCap -> repr a -> repr a -> repr a -> repr a
  default linecap :: Monad repr => repr LineCap -> repr a -> repr a -> repr a -> repr a
  linecap lc b r s = join $ flip fmap lc \case
    LineCap_Butt -> b
    LineCap_Round -> r
    LineCap_Square -> s

class LiftLineCap repr => LineCaps repr style where
  linecap' :: repr LineCap -> repr style

data LineJoin
   = LineJoin_Miter
   | LineJoin_Round
   | LineJoin_Bevel

class Val repr LineJoin => LiftLineJoin repr where
  linejoin :: repr LineJoin -> repr a -> repr a -> repr a -> repr a
  default linejoin :: Monad repr => repr LineJoin -> repr a -> repr a -> repr a -> repr a
  linejoin lc m r b = join $ flip fmap lc \case
    LineJoin_Miter -> m
    LineJoin_Round -> r
    LineJoin_Bevel -> b

class LiftLineJoin repr => LineJoins repr style where
  linejoin' :: repr LineJoin -> repr style

class LineMiterLimit repr style where
  lineMiterLimit :: repr Scalar -> repr style

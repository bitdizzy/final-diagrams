module Diagrams.Final.Space.TwoD where

import Linear hiding (ex, ey)
import qualified Linear as L

import Diagrams.Final.Space.Primitive

ex :: E Vector
ex = L.ex

ey :: E Vector
ey = L.ey

unit_x :: Vector Scalar
unit_x = unit (el ex)

unit_y :: Vector Scalar
unit_y = unit (el ey)

-- | Counter-clockwise, in radians
rotation :: Scalar -> LinearTransform Scalar
rotation rad = LinearTransform $
  V2 (V2 (cos rad) (-(sin rad))) (V2 (sin rad) (cos rad))

-- | Horizontal shear preserves the x-axis
shearX :: Scalar -> LinearTransform Scalar
shearX s = LinearTransform $
  V2 (V2 1 s) (V2 0 1)

-- | Vertical shear preserves the y-axis
shearY :: Scalar -> LinearTransform Scalar
shearY s = LinearTransform $
  V2 (V2 1 0) (V2 s 1)

-- | Reflection around the x-axis preserves the x-axis
reflectX :: LinearTransform Scalar
reflectX = LinearTransform $
  V2 (V2 1 0) (V2 0 (-1))

-- | Reflection around the y-axis preserves the y-axis
reflectY :: LinearTransform Scalar
reflectY = LinearTransform $
  V2 (V2 (-1) 0) (V2 0 1)

scaleX :: Scalar -> LinearTransform Scalar
scaleX s = LinearTransform $
  V2 (V2 s 0) (V2 0 1)

scaleY :: Scalar -> LinearTransform Scalar
scaleY s = LinearTransform $
  V2 (V2 1 0) (V2 0 s)

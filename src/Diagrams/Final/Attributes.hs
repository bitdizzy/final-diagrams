module Diagrams.Final.Attributes where

import Diagrams.Final.Core

none :: Scales repr => repr (Scaled repr Scalar)
none = output 0

ultraThin :: Scales repr => repr (Scaled repr Scalar)
ultraThin = normalized 0.0005 `atLeast` output 0.5

veryThin :: Scales repr => repr (Scaled repr Scalar)
veryThin = normalized 0.001 `atLeast` output 0.5

thin :: Scales repr => repr (Scaled repr Scalar)
thin = normalized 0.002 `atLeast` output 0.5

medium :: Scales repr => repr (Scaled repr Scalar)
medium = normalized 0.004 `atLeast` output 0.5

thick :: Scales repr => repr (Scaled repr Scalar)
thick = normalized 0.0075 `atLeast` output 0.5

veryThick :: Scales repr => repr (Scaled repr Scalar)
veryThick = normalized 0.01 `atLeast` output 0.5

ultraThick :: Scales repr => repr (Scaled repr Scalar)
ultraThick = normalized 0.02 `atLeast` output 0.5

tiny :: Scales repr => repr (Scaled repr Scalar)
tiny = normalized 0.01

verySmall :: Scales repr => repr (Scaled repr Scalar)
verySmall = normalized 0.015

small :: Scales repr => repr (Scaled repr Scalar)
small = normalized 0.023

normal :: Scales repr => repr (Scaled repr Scalar)
normal = normalized 0.035

large :: Scales repr => repr (Scaled repr Scalar)
large = normalized 0.05

veryLarge :: Scales repr => repr (Scaled repr Scalar)
veryLarge = normalized 0.07

huge :: Scales repr => repr (Scaled repr Scalar)
huge = normalized 0.1

newtype LineWidth = LineWidth { unLineWidth :: Scalar }

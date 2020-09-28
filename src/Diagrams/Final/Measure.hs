{-# LANGUAGE MultiParamTypeClasses #-}
module Diagrams.Final.Measure where

newtype Scale n = Scale { getScale :: n }

class Measured repr n a where
  local :: repr (Scale n -> a) -> repr a
  normalized :: repr (Scale n -> a) -> repr a
  global :: repr (Scale n -> a) -> repr a

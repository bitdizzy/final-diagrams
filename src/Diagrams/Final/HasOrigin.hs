{-# LANGUAGE MultiParamTypeClasses #-}
module Diagrams.Final.HasOrigin where

class HasOrigin repr v n t where
  moveOriginBy :: repr (v n) -> repr t -> repr t

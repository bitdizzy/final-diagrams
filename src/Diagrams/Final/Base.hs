{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Diagrams.Final.Base where

class Lambda repr where
  lam :: (repr a -> repr b) -> repr (a -> b)

class Application repr where
  apply :: repr (a -> b) -> repr a -> repr b

class Monoidal repr a where
  unit :: repr a
  multiply :: [repr a] -> repr a

class Value repr a where
  val :: a -> repr a

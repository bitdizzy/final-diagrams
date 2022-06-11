{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Diagrams.Final.Tangent where

import Diagrams.Final.Core
import Diagrams.Final.Located
import Diagrams.Final.Parametric
import Diagrams.Final.Segment

newtype Tangent p = Tangent { unTangent :: p }

class Tangents repr where
  tangent :: repr p -> repr (Tangent p)
  untangent :: repr (Tangent p) -> repr p
  default tangent :: Functor repr => repr p -> repr (Tangent p)
  tangent = fmap Tangent
  default untangent :: Functor repr => repr (Tangent p) -> repr p
  untangent = fmap unTangent

instance (Tangents repr, DomainBounds repr p, PDom p ~ PDom (Tangent p), Parametric repr (Tangent p) (PDom (Tangent p)) (PCod (Tangent p)))
  => DomainBounds repr (Tangent p) where
  domainLower = domainLower . untangent
  domainUpper = domainUpper . untangent

instance (LiftLocated repr, Tangents repr, Parametric repr (Tangent p) d r)
  => Parametric repr (Tangent (Located repr p)) d r where
  type PDom (Tangent (Located repr p)) = PDom (Tangent p)
  type PCod (Tangent (Located repr p)) = PCod (Tangent p)
  atParam t p = located' (untangent t) \l _ -> tangent l `atParam` p

instance (LiftLocated repr, Tangents repr, PDom p ~ PDom (Tangent p), DomainBounds repr p, DomainBounds repr (Tangent p), EndValues repr (Tangent p), Parametric repr (Tangent p) (PDom (Tangent p)) (PCod (Tangent p)))
  => EndValues repr (Tangent (Located repr p)) where
  evalAtLower t = located' (untangent t) \l _ -> evalAtLower (tangent l)
  evalAtUpper t = located' (untangent t) \l _ -> evalAtUpper (tangent l)

instance (Tangents repr, Segments repr) => Parametric repr (Tangent (Segment repr 'Closed)) Scalar (Vector repr Scalar) where
  type PDom (Tangent (Segment repr 'Closed)) = Scalar
  type PCod (Tangent (Segment repr 'Closed)) = Vector repr Scalar
  atParam s p = segment' (untangent s) \case
    Linear o -> offset' o \case
      Offset_Closed v -> v
    Cubic c1 c2 o -> offset' o \case
      Offset_Closed v ->
        let_ (val 3 %* p %* p) \p' ->
          val 3 %* (p' %- val 4 %* p%+ val 1) %*^ c1 %^+^ val 3 %* (val 2 %- val 3 %* p) %* p %*^ c2 %^+^ p' %*^ v

tangentAtParam
  :: (Tangents repr, Parametric repr (Tangent p) (PDom (Tangent p)) (PCod (Tangent p)))
  => repr p
  -> repr (PDom (Tangent p))
  -> repr (PCod (Tangent p))
tangentAtParam t p = tangent t `atParam` p

tangentAtLower :: (Tangents repr, EndValues repr (Tangent p)) => repr p -> repr (PCod (Tangent p))
tangentAtLower = evalAtLower . tangent

tangentAtUpper :: (Tangents repr, EndValues repr (Tangent p)) => repr p -> repr (PCod (Tangent p))
tangentAtUpper = evalAtUpper . tangent

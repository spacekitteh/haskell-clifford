\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, DataKinds, KindSignatures, BangPatterns #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, InstanceSigs, ImplicitParams  #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, PolyKinds  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Numeric.Clifford.Manifold where
import NumericPrelude hiding ((++), map)
import Data.List.Stream
import GHC.TypeLits
import Algebra.Additive
import Algebra.Field
import Algebra.Module
import Numeric.Clifford.Multivector hiding (Symbol)
import Data.AdditiveGroup
import Data.AffineSpace
import Data.VectorSpace 
import Prelude.Unicode
import Control.Category
import Control.Arrow
import GHC.TypeLits
import Data.Proxy
import Algebra.Algebraic
import Data.Traversable
-- | Represents an arbitrary Cartesian product of Clifford spaces
newtype Manifold p q f = Manifold {unManifold ∷ [Multivector p q f]} deriving (Eq)


class Metric v f a where
     measure ∷(?metricChoice ∷ MetricName a, Algebra.Algebraic.C f) ⇒ v → v → f

data MetricName (name∷Symbol) = ChosenMetric

instance ∀ p q f f1. f~f1 ⇒ Metric (Multivector p q f) f1 ("Euclidean") where
         measure a b = Numeric.Clifford.Multivector.magnitude $ dot a b

instance ∀ p q f f1. (Ord f, KnownNat p, KnownNat q, f~f1) ⇒ Metric (Multivector p q f) f1 ("L₁") where
         measure a b = Numeric.Clifford.Multivector.magnitude $ a - b

data ManifoldName (name∷Symbol) = ChosenManifold
class (Traversable f) ⇒ Manifold' f obj a where
    --data CoordinatePatch a = CoordinatePatch {toPatch ∷ obj → Patch a, fromPatch ∷ Patch a → obj, toCoordinates ∷ Patch a → f (Field a), fromCoordinates ∷ f (Field a) → Patch a  }
    type Field a
    type Patch a
    type Tangent a
    type TangentBundle a
    type Dimension a∷  Nat
    type UsesMetric a∷ Symbol
    atlas ∷ (?manifoldChoice ∷ ManifoldName a) ⇒ f (CoordinatePatch f obj a)
--    project ∷ (?manifoldChoice ∷ ManifoldName a) ⇒  Base a
--    unproject ∷ Base a→ a
    tangent ∷ Patch a → TangentBundle a
    cotangent ∷ Patch a → (TangentBundle a→ Field a)

data CoordinatePatch f obj a  = CoordinatePatch {toPatch ∷ obj → Patch a, fromPatch ∷ Patch a → obj, toCoordinates ∷ Patch a → f (Field a), fromCoordinates ∷ f (Field a) → Patch a  }

data E3 = E3
instance Manifold' [] (Multivector 3 0 Double) "E3" where 
--    type Base E3= (Multivector 3 0 Double)
    type Dimension "E3"= 3
    type UsesMetric "E3"= "Euclidean"

newtype ManifoldTangent p q f = ManifoldTangent {unManifoldTangent ∷ (Manifold p q f, [Multivector p q f])}
newtype ManifoldCoTangent p q f = ManifoldCoTangent {unManifoldCoTangent ∷ ManifoldTangent p q f → f }

instance (Algebra.Field.C f, Ord f, KnownNat p, KnownNat q) ⇒ AdditiveGroup (ManifoldTangent p q f) where
         zeroV = ManifoldTangent ((Manifold undefined), zero)
         (^+^) (ManifoldTangent (x,a)) (ManifoldTangent (y,b)) = if x≡y
                                                                    then ManifoldTangent (x,a+b)
                                                                    else undefined 
         negateV (ManifoldTangent (x,t)) = ManifoldTangent (x,negate t) 

instance (Algebra.Field.C f, Ord f, KnownNat p, KnownNat q) ⇒ AffineSpace (Manifold p q f) where
         type Diff (Manifold p q f) = ManifoldTangent p q f
         (.-.) (Manifold a) (Manifold b) = ManifoldTangent (Manifold b, a-b)
         (.+^) (Manifold m) (ManifoldTangent (Manifold x,t)) = if m ≡ x
                                                                  then Manifold (m+t)
                                                                  else undefined

instance (Algebra.Field.C f, Ord f, KnownNat p, KnownNat q, (Algebra.Module.C f (Multivector p q f))) ⇒VectorSpace (ManifoldTangent p q f) where
         type Scalar (ManifoldTangent p q f) = f
         (*^) scalar (ManifoldTangent (x,t)) = ManifoldTangent (x, scalar *> t)

type DerivativeFunction p q f = Manifold p q f → ManifoldTangent p q f

newtype Chart p q f a = Chart {unChart :: a → Manifold p q f}
newtype Atlas p q f a = Atlas {unAtlas ∷ [Chart p q f a]}




\end{code}
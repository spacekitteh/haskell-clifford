\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, DataKinds, KindSignatures, BangPatterns #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, InstanceSigs, ImplicitParams  #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, PolyKinds, TypeOperators, FunctionalDependencies  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Numeric.Clifford.Manifold where
import NumericPrelude hiding ((++), map, (.))
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
import Algebra.VectorSpace
-- | Represents an arbitrary Cartesian product of Clifford spaces
newtype Manifold p q f = Manifold {unManifold ∷ [Multivector p q f]} deriving (Eq)

data Eigenvalues = Eigenvalues {positives ∷ Integer, negatives ∷ Integer, zeros ∷ Integer} deriving (Eq, Show, Ord)
class Metric v f a where
     measure ∷(?metricChoice ∷ MetricName a, Algebra.Algebraic.C f) ⇒ v → v → f


data MetricName (name∷Symbol) = ChosenMetric

instance forall p q f f1. f~f1 => Metric (Multivector p q f) f1 ("Euclidean") where
         measure a b = Numeric.Clifford.Multivector.magnitude $ dot a b


instance forall p q f f1. (Ord f, KnownNat p, KnownNat q, f ~ f1) => Metric (Multivector p q f) f1 ("L₁") where
         measure a b = Numeric.Clifford.Multivector.magnitude $ a - b

data ManifoldName (name∷Symbol) = ChosenManifold
class (Traversable f, Algebra.VectorSpace.C (Field a) (Tangent a), Algebra.VectorSpace.C (Field a) (Patch a)) ⇒ Manifold' f obj a | a → f obj where
    type Coordinates a
    type Field a
    type Patch a
    type Tangent a
    type Dimension a∷  Nat
    type UsesMetric a∷ Symbol
    atlas ∷ (?manifoldChoice ∷ ManifoldName a) ⇒ f (Chart obj a)
    eigenvalues ∷ (?manifoldChoice ∷ ManifoldName a) ⇒ Eigenvalues
    tangent ∷ Patch a → Tangent a
    cotangent ∷ Patch a → (Tangent a→ Field a)


funcOnCoordinates ∷ (?manifoldChoice ∷ ManifoldName a, ?metricChoice ∷ MetricName a) ⇒ (Coordinates a → out) → Chart obj a  → (Patch a → out)
funcOnCoordinates f patch = f . (χ patch)

 
data Chart obj a  = Chart {toPatch ∷ obj → Patch a, fromPatch ∷ Patch a → obj, χ ∷ Patch a → Coordinates a, invχ ∷ Coordinates a → Patch a  }

data E3 = E3
instance Manifold' [] (Multivector 3 0 Double) "E3" where 
    type Patch "E3" = Multivector 3 0 Double
    type Tangent "E3" = Multivector 3 0 Double
    type Field "E3"= Double
    type Dimension "E3"= 3
    type UsesMetric "E3"= "Euclidean"
    eigenvalues = Eigenvalues 3 0 0

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

--newtype Chart p q f a = Chart {unChart :: a → Manifold p q f}
--newtype Atlas p q f a = Atlas {unAtlas ∷ [Chart p q f a]}




\end{code}

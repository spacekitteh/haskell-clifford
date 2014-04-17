\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, DataKinds, KindSignatures, BangPatterns #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Numeric.Clifford.Manifold where
import NumericPrelude hiding ((++), map)
import Data.List.Stream
import GHC.TypeLits
import Algebra.Additive
import Algebra.Field
import Algebra.Module
import Numeric.Clifford.Multivector
import Data.AdditiveGroup
import Data.AffineSpace
import Data.VectorSpace 
import Prelude.Unicode

-- | Represents an arbitrary Cartesian product of Clifford spaces
newtype Manifold p q f = Manifold {unManifold ∷ [Multivector p q f]} deriving (Eq)

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
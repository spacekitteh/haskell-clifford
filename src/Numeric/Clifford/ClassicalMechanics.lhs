\documentclass{article}
%include polycode.fmt
\usepackage{fontspec}
\usepackage{amsmath}
\usepackage{unicode-math}
\usepackage{lualatex-math}
\setmainfont{latinmodern-math.otf}
\setmathfont{latinmodern-math.otf}
\usepackage{verbatim}
\author{Sophie Taylor}
\title{haskell-clifford: A Haskell Clifford algebra dynamics library}
\begin{document}

This is the classical mechanics portion of the library. 

\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, KindSignatures, DataKinds #-}
{-# LANGUAGE FlexibleInstances, TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK show-extensions #-}
\end{code}
%if False
\begin{code}
\end{code}
%endif

\begin{code}
module Numeric.Clifford.ClassicalMechanics where
import Numeric.Clifford.Multivector as MV
import Numeric.Clifford.Blade
import GHC.TypeLits
import Data.Proxy
import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate, all, (.) )
import Algebra.Absolute
import Algebra.Algebraic
import Algebra.Additive
import Algebra.Ring
import Algebra.ToInteger
import Algebra.Module
import Algebra.Field
import Data.List.Stream
import Numeric.Natural
import qualified Data.Vector as V
import NumericPrelude.Numeric (sum)
import qualified NumericPrelude.Numeric as NPN 
import Test.QuickCheck
import Math.Sequence.Converge (convergeBy)
import Number.Ratio hiding (scale)
import Algebra.ToRational
import Control.Lens hiding (indices)
import Control.Exception (assert)
import Data.Maybe
import Data.DeriveTH
import Data.Word
import Numeric.Clifford.Internal
import Numeric.Clifford.LinearOperators
import Control.Applicative
import Data.Monoid
import Control.Category

nonEqualFrames = "Non-equal reference frames! Insert code here to translate between them! :) Should really make reference frames as types and then have type families to convert between them :v :v :v"


data EnergyMethod (p::Nat) (q::Nat) f = Hamiltonian{ _dqs :: [DynamicSystem p q f -> Multivector p q f], _dps :: [DynamicSystem p q f -> Multivector p q f]}

data DynamicSystem (p::Nat) (q::Nat) f = DynamicSystem {_time :: f, coordinates :: [Multivector p q f], _momenta :: [Multivector p q f], _energyFunction :: EnergyMethod p q f, _projector :: DynamicSystem p q f -> DynamicSystem p q f}

makeLenses ''EnergyMethod
makeLenses ''DynamicSystem

--evaluateDerivative s = dq++ dp where
--    dq = (s&energyFunction.dqs) -- s
--    dp = (s&energyFunction.dps) -- s
--    dq = map ($ s) ((dqs $ energyFunction) s) --s&energyFunction.dqs.traverse--map ($ s) ((dqs . energyFunction) s)
--    dp = map ($ s) ((dps $ energyFunction) s)





\end{code}

Now to make a physical object.
\begin{code}
data ReferenceFrame (p::Nat) (q::Nat) t = RelativeFrame {frameName :: String, euclideanMove :: EuclideanMove p q t, velocityRelToParentFrame :: Multivector p q t, angularVelocityRelToParentFrame :: Multivector p q t, parent :: ReferenceFrame p q t}
                                        |GlobalAbsoluteFrame deriving (Eq, Show)


getRigidDisplacementRelToInertial :: (Algebra.Field.C t, Ord t, SingI p, SingI q) =>  ReferenceFrame p q t -> EuclideanMove   p q t
getRigidDisplacementRelToInertial GlobalAbsoluteFrame = mempty
--getRigidDisplacementRelToInertial (RelativeFrame _ displacement mother) = displacement <> (getRigidDisplacementRelToInertial mother)

getFrameTransformation :: forall (p::Nat) (q::Nat) t . (Algebra.Field.C t, Ord t, SingI p, SingI q) =>  ReferenceFrame p q t -> ReferenceFrame p q t -> EuclideanMove p q t
getFrameTransformation r' r = undefined

{-data InertialFrame (p::Nat) (q::Nat) f t = InertialFrame {objects :: t, changeFrame :: t -> EuclideanMove p q f -> t, frame :: ReferenceFrame p q f}


instance Functor (InertialFrame p q f) where
    fmap func (InertialFrame objs changeFrame frame) = InertialFrame (func objs) (changeFrame . func) frame

instance (SingI p, SingI q) => Applicative (InertialFrame p q f) where
    pure a = InertialFrame a GlobalAbsoluteFrame where 
    (<*>) (InertialFrame func trans1 frame1) (InertialFrame objs trans2 frame2) = if (name frame1)==(name frame2)
                                                                    then InertialFrame (func objs) frame1 
                                                                    else InertialFrame (trans2 (func objs) (getFrameTransformation frame2 frame1)) trans2 frame1


instance (SingI p, SingI q, Algebra.Field.C f, Ord f) => Monad (InertialFrame p q f) where
    return = pure
    (>>=) (InertialFrame objA changeFrameA frameA)  func = undefined where
        (InertialFrame objB changeFrameB frameB) = func objA
        
-}

a `cross` b = (negate psuedoScalar) * (a `wedge` b)



data PhysicalVector (p::Nat) (q::Nat) t = PhysicalVector {r :: Multivector p q t, referenceFrame :: ReferenceFrame p q t}





data RigidBody (p::Nat) (q::Nat) f where
 RigidBody:: (Algebra.Field.C f, Algebra.Module.C f (Multivector p q f)) =>  {bodyName::String, frame::ReferenceFrame p q f, mass :: f, inertia :: Multivector p q f, position :: Multivector p q f, attitude :: Multivector p q f, velocity :: Multivector p q f, angularVelocity :: Multivector p q f
                             } -> RigidBody p q f

--makeLenses ''RigidBody doesn't actually work
{- Things to do: 
4. create a 1-form type 
5. figure a way to take exterior product of 1 forms at a type level so i can just go like: omega = df1 ^ df2 ^ df ; omega a b c
-}



\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

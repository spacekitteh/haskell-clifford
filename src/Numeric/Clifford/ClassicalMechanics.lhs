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
import Data.Dynamic
import Data.Data
import Control.Category

class Energy t a where

class Hamiltonian x p t a where
 
type Hamil x p t = (PhaseSpace x p a, Energy t b) ⇒ a → b
class PhaseSpace x p a where

class StateSpace x v a where

class ConfigurationSpace q qdot a where

class PhaseSpacePath t x p a where
    
instance (PhaseSpace x p a) ⇒ PhaseSpacePath t x p  (t → a) where










nonEqualFrames = "Non-equal reference frames! Insert code here to translate between them! :) Should really make reference frames as types and then have type families to convert between them :v :v :v"



\end{code}

Now to make a physical object.
\begin{code}
data ReferenceFrame (p::Nat) (q::Nat) t = RelativeFrame {  frameName :: String
                                                       , euclideanMove :: EuclideanMove p q t
                                                       , velocityRelToParentFrame :: Multivector p q t
                                                       , angularVelocityRelToParentFrame :: Multivector p q t
                                                       , parent :: ReferenceFrame p q t
                                                       }
                                        | GlobalAbsoluteFrame deriving (Eq, Show)


getRigidDisplacementRelToInertial :: (Algebra.Field.C t, Ord t, KnownNat p, KnownNat q) =>  ReferenceFrame p q t -> EuclideanMove   p q t
getRigidDisplacementRelToInertial GlobalAbsoluteFrame = mempty
--getRigidDisplacementRelToInertial (RelativeFrame _ displacement mother) = displacement <> (getRigidDisplacementRelToInertial mother)

getFrameTransformation :: forall (p::Nat) (q::Nat) t . (Algebra.Field.C t, Ord t, KnownNat p, KnownNat q) =>  ReferenceFrame p q t -> ReferenceFrame p q t -> EuclideanMove p q t
getFrameTransformation r' r = undefined

{-data InertialFrame (p::Nat) (q::Nat) f t = InertialFrame {objects :: t, changeFrame :: t -> EuclideanMove p q f -> t, frame :: ReferenceFrame p q f}


instance Functor (InertialFrame p q f) where
    fmap func (InertialFrame objs changeFrame frame) = InertialFrame (func objs) (changeFrame . func) frame

instance (KnownNat p, KnownNat q) => Applicative (InertialFrame p q f) where
    pure a = InertialFrame a GlobalAbsoluteFrame where 
    (<*>) (InertialFrame func trans1 frame1) (InertialFrame objs trans2 frame2) = if (name frame1)==(name frame2)
                                                                    then InertialFrame (func objs) frame1 
                                                                    else InertialFrame (trans2 (func objs) (getFrameTransformation frame2 frame1)) trans2 frame1


instance (KnownNat p, KnownNat q, Algebra.Field.C f, Ord f) => Monad (InertialFrame p q f) where
    return = pure
    (>>=) (InertialFrame objA changeFrameA frameA)  func = undefined where
        (InertialFrame objB changeFrameB frameB) = func objA
        
-}

a `cross` b = (negate psuedoScalar) * (a `wedge` b)



data PhysicalVector (p::Nat) (q::Nat) t = PhysicalVector {radius :: Multivector p q t, referenceFrame :: ReferenceFrame p q t}





{-data RigidBody (p::Nat) (q::Nat) f where
 RigidBody:: (Algebra.Field.C f, Algebra.Module.C f (Multivector p q f)) =>  {bodyName::String, frame::ReferenceFrame p q f, mass :: f, inertia :: Multivector p q f, position :: Multivector p q f, attitude :: Multivector p q f, velocity :: Multivector p q f, angularVelocity :: Multivector p q f
                             } -> RigidBody p q f
-}
--makeLenses ''RigidBody doesn't actually work
{- Things to do: 
4. create a 1-form type 
5. figure a way to take exterior product of 1 forms at a type level so i can just go like: omega = df1 ^ df2 ^ df ; omega a b c
-}





data Variable f a = Variable{symbol ∷ String, access ∷ Lens' f a }


newtype Position p q f = Position {unPosition ∷ Multivector p q f}
newtype Velocity p q f = Velocity {unVelocity ∷ Multivector p q f}
newtype Force p q f = Force {unForce ∷ Multivector p q f}
newtype Mass p q f = Mass {unMass :: Multivector p q f}
newtype Time f = Time {unTime ∷  f}
newtype Momentum p q f = Momentum {unMomentum ∷ Multivector p q f}
newtype Charge p q f = Charge {unCharge ∷ Multivector p q f}
newtype Spinor p q f = Spinor {unSpinor ∷ Multivector p q f}
newtype Inertia p q f = Inertia {unInertia :: Multivector p q f}
newtype AngularVelocity p q f = AngularVelocity {unAngularVelocity :: Multivector p q f}
newtype AngularMomentum p q f = AngularMomentum {unAngularMomentum :: Multivector p q f}
class Entity a where
      name  ∷ Lens' a String


class Entity a ⇒ Body  (p∷Nat) (q∷Nat) f a where
    frame :: Lens' a (ReferenceFrame p q f)
    position :: Lens' a (Position p q f) 
    velocity :: Lens' a (Velocity p q f) 
    momentum :: Lens' a (Momentum p q f) 

class (Algebra.Field.C f, Ord f, KnownNat p, KnownNat q, Body p q f a) => MassiveBody p q f a where
    mass :: Lens' a (Mass p q f)
    



data PointMass p q f = PointMass { _PointMassName ∷ String, _PointMassFrame ∷ ReferenceFrame p q f, _PointMassPosition ∷ Position p q f, _PointMassVelocity ∷ Velocity p q f, _PointMassMass ∷ Mass p q f, _PointMassMomentum ∷ Momentum p q f}

instance Entity (PointMass p q f) where
    name = lens _PointMassName (\p n → p {_PointMassName = n})

instance Body p q f (PointMass p q f) where
    frame = lens _PointMassFrame (\p f → p {_PointMassFrame = f})
    position = lens _PointMassPosition (\p pos → p {_PointMassPosition = pos})
    velocity = lens _PointMassVelocity (\p v → p {_PointMassVelocity = v})
    momentum = lens _PointMassMomentum (\p mom → p {_PointMassMomentum = mom})
    


instance (Algebra.Field.C f, Ord f, KnownNat p, KnownNat q) ⇒ MassiveBody p q f (PointMass p q f) where
    mass = lens _PointMassMass (\p m → p {_PointMassMass = m})


class (Algebra.Field.C f, KnownNat p, KnownNat q, Ord f, MassiveBody p q f a) ⇒ ChargedBody p q f a where
    electricCharge ∷ Lens' a (Charge p q f)
    magneticCharge ∷ Lens' a (Charge p q f)
    
class (MassiveBody p q f a) ⇒ RigidBody p q f a where
    attitude ∷ Lens' a (Spinor p q f) 
    angularVelocity ∷ Lens' a (AngularVelocity p q f)
    angularMomentum ∷ Lens' a (AngularMomentum p q f)
    inertia ∷ Lens' a (Inertia p q f)

class (Algebra.Field.C f, Ord f, MassiveBody p q f a) ⇒ AerodynamicBody p q f a where
    liftCoefficient ∷ a → Velocity p q f → Multivector p q f
    dragCoefficient ∷ a → Velocity p q f → Multivector p q f
    shearCoefficient ∷ a → Velocity p q f → Multivector p q f
    shearCoefficient a = const zero 


class (Entity a) ⇒ Region p q f a where
    isInside :: forall b . Body p q f b =>  a -> b -> Bool

-- | Time -> Item -> Force
type ForceFunction p q f a = Time f → a → Force p q f

class Region p q f a ⇒ ForceField p q f a where
    actOn :: ForceFunction p q f a
    



-- perhaps an array of getters on objects?



data Inhabitant = ABody {b∷Dynamic}
                | ARegion {r∷Dynamic} deriving ( Show, Typeable)


class (Functor funct) ⇒  World (p∷Nat) (q∷Nat) fieldType funct a where 
    asFunctor ∷ a → funct Inhabitant 
    time ∷ Lens' a (Time fieldType)

data EuclideanWorld fieldType

instance World 3 0 fieldType [] (EuclideanWorld fieldType) where
    asFunctor w = []




\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
\end{code}
%if False
\begin{code}
{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -O3 -optlc-O=3 -Wall #-}
-- OPTIONS_GHC -Odph -fvectorise -package dph-lifted-vseg 
--  LANGUAGE ParallelArrays
\end{code}
%endif

\begin{code}
module Numeric.Clifford.ClassicalMechanics where
import Numeric.Clifford.Multivector as MV
import Numeric.Clifford.Blade
import GHC.TypeLits
import Data.Proxy
import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate, all)
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
import Debug.Trace
--trace _ a = a

data EnergyMethod f = Hamiltonian{ _dqs :: [DynamicSystem f -> Multivector f], _dps :: [DynamicSystem f -> Multivector f]}

data DynamicSystem f = DynamicSystem {_time :: f, coordinates :: [Multivector f], _momenta :: [Multivector f], _energyFunction :: EnergyMethod f, _projector :: DynamicSystem f -> DynamicSystem f}

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
data ReferenceFrame t = ReferenceFrame {basisVectors :: [Multivector t]}
psuedoScalar' :: forall f. (Ord f, Algebra.Ring.C f) => ReferenceFrame f -> Multivector f
psuedoScalar'  = multiplyList . basisVectors
psuedoScalar :: forall f. (Ord f, Algebra.Ring.C f) => Natural -> Multivector f
psuedoScalar n = one `e` [1..n]
a `cross` b = (negate $ one)`e`[1,2,3] * (a ∧ b)
data PhysicalVector t = PhysicalVector {dimension :: Natural, r :: Multivector t, referenceFrame :: ReferenceFrame t}
squishToDimension (PhysicalVector d (BladeSum terms) f) = PhysicalVector d r' f where
    r' = BladeSum terms' where
        terms' = terms & filter (\(Blade _ ind) -> all (\k -> k <= d) ind)
squishToDimension' d (BladeSum terms) = r' where
    r' = BladeSum terms' where
        terms' = terms & filter (\(Blade _ ind) -> all (\k -> k <= d) ind)

data RigidBody f where
 RigidBody:: (Algebra.Field.C f, Algebra.Module.C f (Multivector f)) =>  {position :: PhysicalVector f,
                              _momentum :: PhysicalVector f,
                              _mass :: f,
                              _attitude :: PhysicalVector f,
                              _angularMomentum :: PhysicalVector f,
                              _inertia :: PhysicalVector f
                             } -> RigidBody f

--makeLenses ''RigidBody doesn't actually work
{- Things to do Monday: 
2. Create a n-dimensional vector type where n is a type nat
3. compose in squishToDimension to mvNormalForm
4. create a 1-form type 
5. figure a way to take exterior product of 1 forms at a type level so i can just go like: omega = df1 ^ df2 ^ df ; omega a b c
-}

data NDVector (n :: Nat) f where
 NDVector :: (Algebra.Field.C f, Algebra.Module.C f (Multivector f)) => {value :: Multivector f} -> NDVector n f

{-ndVector :: forall n.(n ~ Nat) => Proxy n -> (forall f.
                  (Algebra.Field.C f, Algebra.Module.C f (Multivector f)) =>
                  Multivector f -> NDVector (n) f)
ndVector _ value = NDVector $ squishToDimension' (toNatural nummed) value where
    nummed :: Word32
    nummed = fromIntegral $ fromSing (sing :: Sing n)-}
\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

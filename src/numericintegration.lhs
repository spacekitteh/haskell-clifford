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

This is the numeric integration portion of the library. 

\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs #-}
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
module Numeric.Clifford.NumericIntegration where
import Numeric.Clifford.Multivector as MV
import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate)
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
import Debug.Trace
--trace _ a = a
rk4Classical :: (Ord a, Algebra.Algebraic.C a) =>  stateType -> a -> (stateType->stateType) -> ([Multivector a] -> stateType) -> (stateType -> [Multivector a]) -> stateType
rk4Classical state h f project unproject = project newState where
    update = map (\(k1', k2', k3', k4') -> sumList [k1',2*k2',2*k3',k4'] MV./ Algebra.Ring.fromInteger 6) $ zip4 k1 k2 k3 k4
    newState = zipWith (+) state' update
    state' = unproject state
    evalDerivatives x = unproject $ f $ project x
    k1 = map (h*>) $ evalDerivatives state'
    k2 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (MV./ two) k1)
    k3 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (MV./ two) k2)
    k4 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' k3

rk4ClassicalList state h f = rk4Classical state h f id id


elementAdd = zipWith (+)
elementScale = zipWith (*>) 
a `elementSub` b = zipWith (-) a b
a `elementMul` b = zipWith (*) a b
data ButcherTableau f = ButcherTableau {_tableauA :: [[f]], _tableauB :: [f], _tableauC :: [f]}
makeLenses ''ButcherTableau


type ConvergerFunction f = [[Multivector f]] -> [Multivector f]
type AdaptiveStepSizeFunction f state = f -> state -> f 

data RKAttribute f state = Explicit
                 | HamiltonianFunction
                 | AdaptiveStepSize {sigma :: AdaptiveStepSizeFunction f state}
                 | ConvergenceTolerance {epsilon :: f}
                 | ConvergenceFunction {converger :: ConvergerFunction f } 
                 | RootSolver 
                 | UseAutomaticDifferentiationForRootSolver
                 | StartingGuessMethod 


$( derive makeIs ''RKAttribute)

--rk4ClassicalTableau :: ButcherTableau NPN.Double
rk4ClassicalTableau = ButcherTableau [[0,0,0,0],[0.5,0,0,0],[0,0.5,0,0],[0,0,1,0]] [1.0 NPN./6,1.0 NPN./3, 1.0 NPN./3, 1.0 NPN./6] [0, 0.5, 0.5, 1]
implicitEulerTableau = ButcherTableau [[1.0::NPN.Double]] [1] [1]



sumVector = sumList . V.toList 

--systemRootSolver :: [Multivector f] -> [Multivector f] -> ratio -> [Multivector f] -> [Multivector f] -> [Multivector f]

--This will stop as soon as one of the elements converges. This is bad. Need to make it skip convergent ones and focus on the remainig.
systemBroydensMethod f x0 x1 = map fst $ update (x1,ident) x0  where
    update (xm1,jm1) xm2 | zero `elem` dx =  [(xm1,undefined)]
                   | otherwise = if x == xm1 then [(x,undefined)] else (x,j) : update (x,j) xm1 where
      x = xm1 `elementSub` ( (fm1 `elementMul` dx) `elementMul` ody)
      j = undefined
      fm1 = f xm1
      fm2 = f xm2
      dx = elementSub xm1 xm2
      dy = elementSub fm1 fm2
      ody = map inverse dy
    ident = undefined

--TODO: implement Broyden-Fletcher-Goldfarb-Shanno method

rk4ClassicalFromTableau (t,state) h f = impl (t, state) h f id id where
    impl = genericRKMethod rk4ClassicalTableau []
implicitEulerMethod (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod implicitEulerTableau []

lobattoIIIASecondOrderTableau = ButcherTableau [[0,0],[0.5::NPN.Double,0.5]] [0.5,0.5] [0,1]
lobattoIIIASecondOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIASecondOrderTableau []

lobattoIIIAFourthOrderWithTol (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIAFourthOrderTableau [ConvergenceTolerance 1.0e-8]
lobattoIIIAFourthOrderTableau = ButcherTableau [[0,0,0],[((5 NPN./24)::NPN.Double),1 NPN./3,-1 NPN./24],[1 NPN./6,2 NPN./3,1 NPN./6]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIAFourthOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIAFourthOrderTableau []

lobattoIIIBFourthOrderTableau = ButcherTableau [[1 NPN./6,(-1) NPN./6,0],[((1 NPN./6)::NPN.Double),1 NPN./3,0],[1 NPN./6,5 NPN./6, 0]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIBFourthOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIBFourthOrderTableau []

convergeList ::(Show f, Ord f) => [[f]] -> [f]
convergeList = converge

type RKStepper t stateType = 
    (Ord t, Show t, Algebra.Module.C t (Multivector t), Algebra.Additive.C t) => 
    (t, stateType) -> t -> 
    (t -> stateType -> stateType) -> 
    ([Multivector t] -> stateType) -> 
    (stateType ->[Multivector t]) -> 
    (t,stateType)
showOutput name x = trace ("output of " ++ name ++" is " ++ show x) x

convergeTolLists :: (Ord f, Eq f, Algebra.Absolute.C f, Algebra.Algebraic.C f, Show f) 
                   => f ->  [[Multivector f]] -> [Multivector f]
convergeTolLists t [] = error "converge: empty list"
convergeTolLists t xs = fromMaybe empty (convergeBy check Just xs)
    where
      empty = error "converge: error in impl"
      check (a:b:c:_)
          | (trace ("Converging at " ++ show a) a) == b = Just b
          | a == c = Just c
          | ((showOutput ("convergence check with tolerance " ++ show t) $ 
              magnitude (sumList $ (zipWith (\x y -> NPN.abs (x-y)) b c))) <= t) = showOutput ("convergence with tolerance "++ show t )$ Just c
      check _ = Nothing

genericRKMethod :: forall t stateType . 
                  ( Ord t, Show t, Algebra.Module.C t (Multivector t), Algebra.Additive.C t,
                        Algebra.Absolute.C t, Algebra.Algebraic.C t)
                  =>  ButcherTableau t -> [RKAttribute t stateType] -> RKStepper t stateType
genericRKMethod tableau attributes = rkMethodImplicitFixedPoint where
    s =  length (_tableauC tableau)
    c n = l !!  (n-1) where
        l = _tableauC tableau
    a n = (l !! (n-1)) & filter (/= zero) where
        l = _tableauA tableau
    b i = l !! (i - 1) where
        l = _tableauB tableau
    sumListOfLists = map sumList . transpose 

    converger :: (Ord t, Algebra.Algebraic.C t, Algebra.Absolute.C t) =>
                [[Multivector t]] -> [Multivector t]
    converger = case  find (\x -> isConvergenceTolerance x || isConvergenceFunction x) attributes of
                  Just (ConvergenceFunction conv) -> conv
                  Just (ConvergenceTolerance tol) -> convergeTolLists (trace ("Convergence tolerance set to " ++ show tol)tol)
                  Nothing -> trace "No convergence tolerance specified, defaulting to equality" convergeList
    
    

    rkMethodImplicitFixedPoint :: RKStepper t stateType
    rkMethodImplicitFixedPoint (time, state) h f project unproject =
        (time + h*c s, project newState) where
        zi i = (\out -> trace ("initialGuess is " ++ show initialGuess++" whereas the final one is " ++ show out) out) $
               assert (i <= s && i>= 1) $ converger $ iterate (zkp1 i) initialGuess where
            initialGuess = if i == 1 || null (zi (i-1)) then map (h'*>) $ unproject $ f guessTime state else zi (i-1)
            h' = h * c i
            guessTime = time + h'
            zkp1 :: NPN.Int -> [Multivector t] -> [Multivector t]
            zkp1 i zk = map (h*>) (sumOfJs i zk) where
                sumOfJs i zk =  sumListOfLists $ map (scaledByAij zk) (a i) where 
                    scaledByAij guess a = map (a*>) $ evalDerivatives guessTime $ elementAdd state' guess
        state' = unproject state
        newState = elementAdd state' (assert (not $  null dy) dy)
        dy :: [Multivector t]
        dy = sumListOfLists  [map (b i *>) (zi i) | i <- [1..s]] 
        evalDerivatives :: t -> [Multivector t] -> [Multivector t]
        evalDerivatives time = unproject . (f time) . project 

\end{code}






Look at creating an exponential integrator: https://en.wikipedia.org/wiki/Exponential_integrators







\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

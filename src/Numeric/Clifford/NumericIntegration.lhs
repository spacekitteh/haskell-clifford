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
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, DataKinds, KindSignatures, BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Numeric.Clifford.NumericIntegration where
import Numeric.Clifford.Multivector as MV
import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate)
import Algebra.Absolute
import Algebra.Algebraic
import Algebra.Additive hiding (elementAdd, elementSub)
import Algebra.Ring
import Data.Monoid
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
import GHC.TypeLits
import Numeric.Clifford.Internal
import Data.DeriveTH
import Numeric.Compensated
import MathObj.Wrapper.Haskell98

import qualified Debug.Trace

elementAdd = zipWith (+)
elementScale = zipWith (*>) 
a `elementSub` b = zipWith (-) a b
a `elementMul` b = zipWith (*) a b

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

convergeList ::(Show f, Ord f) => [[f]] -> [f]
convergeList = converge


{-#INLINE sumListOfLists #-}

sumListOfLists = map sumList . transpose 

stateConvergeTolLists :: (Ord f, Algebra.Absolute.C f, Algebra.Algebraic.C f, Show f, SingI p, SingI q) 
                   => f ->  [[Multivector p q f]] -> [Multivector p q f]
stateConvergeTolLists t [] = error "converge: empty list"
stateConvergeTolLists t xs = fromMaybe empty (convergeBy check Just xs)
    where
      empty = error "converge: error in impl"
      check (a:b:c:_)
          | (myTrace ("Converging at " ++ show a) a) == b = Just b
          | a == c = Just c
          | (compensatedSum' (map magnitude diffBetweenElements)) <= t = showOutput ("state convergence with tolerance "++ show t )$ Just c where
            diffBetweenElements = zipWith (\x y -> NPN.abs (x-y)) b c
      check _ = Nothing
guessConvergeTolLists :: forall (p::Nat) (q::Nat) f. (Ord f, Algebra.Absolute.C f, Algebra.Algebraic.C f, Show f, SingI p, SingI q) 
                   => f ->  [[[Multivector p q f]]] -> [[Multivector p q f]]
guessConvergeTolLists _ [] = error "converge: empty list"
guessConvergeTolLists t xs = fromMaybe empty (convergeBy check Just xs)
    where
      empty = error "converge: error in impl"
      check :: [[[Multivector p q f]]] -> Maybe [[Multivector p q f]]
      check (a:b:c:_)
          | (myTrace ("Converging at " ++ show a) a) == b = Just b
          | a == c = Just c
          | totalDifference <= t = showOutput ("guess convergence with tolerance "++ show t )$ Just c where
            totalDifference =  compensatedSum' $ zipWith (\x y -> absDiffBetweenLists x y) b c
            absDiffBetweenLists :: [Multivector p q f] -> [Multivector p q f] -> f
            absDiffBetweenLists x' y' = compensatedSum' $ map magnitude $ zipWith (\x y -> NPN.abs (x-y)) x' y'
      check _ = Nothing

type ProjectionToManifold p q t stateType = stateType -> [Multivector p q t]
type DeprojectorFromManifold p q t stateType = [Multivector p q t] -> stateType
type RKStepper (p::Nat) (q::Nat) t stateType = 
    (Ord t, Show t, Algebra.Module.C t (Multivector p q t), Algebra.Field.C t) => 
     t -> (t -> stateType -> stateType) -> 
    DeprojectorFromManifold p q t stateType -> 
    ProjectionToManifold p q t stateType ->
    (t,stateType) -> (t,stateType)
data ButcherTableau f = ButcherTableau {_tableauA :: [[f]], _tableauB :: [f], _tableauC :: [f]} deriving (Eq, Show)
makeLenses ''ButcherTableau

type StateConvergerFunction f = forall (p::Nat) (q::Nat) f . [[Multivector p q f]] -> [Multivector p q f]
type GuessConvergerFunction f = forall (p::Nat) (q::Nat) f . [[[Multivector p q f]]] -> [[Multivector p q f]]
type AdaptiveStepSizeFunction f state = f -> state -> f 

data RKAttribute f state = Explicit
                 | HamiltonianFunction {totalEnergy :: state -> f}
                 | AdaptiveStepSize {sigma :: AdaptiveStepSizeFunction f state}
                 | ConvergenceTolerance {epsilon :: f}
                 | StateConvergenceFunction {stateConverger :: StateConvergerFunction f } 
                 | GuessConvergenceFunction {guessConverger :: GuessConvergerFunction f }
                 | RootSolver 
                 | UseAutomaticDifferentiationForRootSolver
                 | Seperable
                 | StartingGuessMethod 


$( derive makeIs ''RKAttribute)

{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double stateType] -> RKStepper 3 0 Double stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double [E3Vector]] -> RKStepper 3 0 Double [E3Vector]#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double stateType] -> RKStepper 3 1 Double stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double [STVector]] -> RKStepper 3 1 Double [STVector]#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau (MathObj.Wrapper.Haskell98.T (Compensated Double)) -> [RKAttribute (MathObj.Wrapper.Haskell98.T (Compensated Double)) stateType] -> RKStepper 3 0 (MathObj.Wrapper.Haskell98.T (Compensated Double)) stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau (MathObj.Wrapper.Haskell98.T (Compensated Double)) -> [RKAttribute (MathObj.Wrapper.Haskell98.T (Compensated Double)) [E3VectorComp]] -> RKStepper 3 0 (MathObj.Wrapper.Haskell98.T (Compensated Double)) [E3VectorComp]#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau (MathObj.Wrapper.Haskell98.T (Compensated Double)) -> [RKAttribute (MathObj.Wrapper.Haskell98.T (Compensated Double)) stateType] -> RKStepper 3 1 (MathObj.Wrapper.Haskell98.T (Compensated Double)) stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau (MathObj.Wrapper.Haskell98.T (Compensated Double)) -> [RKAttribute (MathObj.Wrapper.Haskell98.T (Compensated Double)) [STVectorComp]] -> RKStepper 3 1 (MathObj.Wrapper.Haskell98.T (Compensated Double)) [STVectorComp]#-}
genericRKMethod :: forall (p::Nat) (q::Nat) t stateType . 
                  ( Ord t, Show t, Algebra.Module.C t (Multivector p q t),Algebra.Absolute.C t, Algebra.Algebraic.C t, SingI p, SingI q)
                  =>  ButcherTableau t -> [RKAttribute t stateType] -> RKStepper p q t stateType
genericRKMethod tableau attributes = rkMethodImplicitFixedPoint where
    s :: Int
    s =  length (_tableauC tableau)
    c :: Int -> t
    c n = l !!  (n-1) where
        l = _tableauC tableau
    a :: Int -> [t]
    a n = (l !! (n-1)) where
        l = _tableauA tableau
    b :: Int -> t
    b i = l !! (i - 1) where
        l = _tableauB tableau
    b' = _tableauB tableau

    --TODO: Use hamiltonian to tell it to only stop converging once it is within an acceptable range of energy!!! Otherwise the tolerances will lead to an exponential decay/growth due to approaching from below/above! 
    stateConverger :: [[Multivector p q t]] -> [Multivector p q t]
    stateConverger = case  find (\x -> isConvergenceTolerance x || isStateConvergenceFunction x) attributes of
                  Just (StateConvergenceFunction conv) -> conv
                  Just (ConvergenceTolerance tol) -> stateConvergeTolLists (myTrace ("Convergence tolerance set to " ++ show tol)tol)
                  Nothing -> myTrace "No convergence tolerance specified, defaulting to equality" convergeList 
    guessConverger :: [[[Multivector p q t]]] -> [[Multivector p q t]]
    guessConverger = case  find (\x -> isConvergenceTolerance x || isGuessConvergenceFunction x) attributes of
                  Just (GuessConvergenceFunction conv) -> conv
                  Just (ConvergenceTolerance tol) -> guessConvergeTolLists (myTrace ("Convergence tolerance set to " ++ show tol)tol)
                  Nothing -> myTrace "No convergence tolerance specified, defaulting to equality" converge 
    stepSizeAdapter :: AdaptiveStepSizeFunction t stateType
    stepSizeAdapter = case find isAdaptiveStepSize attributes of
                        Just (AdaptiveStepSize sigma) -> sigma
                        Nothing -> (\_ _ -> one)

    (hamiltonian, hamiltonianExists) = case find isHamiltonianFunction attributes of
                    Just (HamiltonianFunction hamil) -> (hamil,True)
                    Nothing -> (undefined,False)
    
    rkMethodImplicitFixedPoint :: RKStepper p q t stateType
    rkMethodImplicitFixedPoint h f deproject project (time, state) =
      (time + adaptiveStepSizeFraction*(c s), newState) where
        adaptiveStepSizeFraction = (stepSizeAdapter time state)*h
        newState = deproject $ elementAdd state' dy'
        state' = project state 
        lengthOfState = length state'

        dy' = sumListOfLists  $ zipWith (\b zi -> map (b *>) zi) b' z

        --set the initial guess as the derivatives evaluated at appropriate times through the timestep
        initialGuess = unfoldr (\(i,st) -> if i>s 
                                           then 
                                               Nothing 
                                           else 
                                               let st' = evalDerivatives (time + adaptiveStepSizeFraction * (c i)) st 
                                               in Just (st',(i+1,st'))) (1,state')
        z = guessConverger $ iterate systemOfZiGuesses initialGuess
        systemOfZiGuesses :: [[Multivector p q t]] -> [[Multivector p q t]]
        systemOfZiGuesses !zk = [zi_plus1 i | i <- [1..s]] where
            atYn =  map (elementAdd state') zk
            zi_plus1 i =  map ((adaptiveStepSizeFraction * (c i))*>) $ sumListOfLists scaledByAi where
                h' = adaptiveStepSizeFraction * (c i)
                guessTime = time + h'
                scaledByAi = zipWith (\a evalled-> map (a*>) evalled) (a i) $ map (evalDerivatives guessTime) atYn
        evalDerivatives :: t -> [Multivector p q t] -> [Multivector p q t]
        --basically a wrapper for f
        evalDerivatives time stateAtTime= project $ (f time) $ deproject stateAtTime


\end{code}

Look at creating an exponential integrator: https://en.wikipedia.org/wiki/Exponential_integrators

\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

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
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, DataKinds, KindSignatures #-}
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


elementAdd = zipWith (+)
elementScale = zipWith (*>) 
a `elementSub` b = zipWith (-) a b
a `elementMul` b = zipWith (*) a b


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


convergeList ::(Show f, Ord f) => [[f]] -> [f]
convergeList = converge


showOutput name x = myTrace ("output of " ++ name ++" is " ++ show x) x

convergeTolLists :: (Ord f, Algebra.Absolute.C f, Algebra.Algebraic.C f, Show f, SingI p, SingI q) 
                   => f ->  [[Multivector p q f]] -> [Multivector p q f]
convergeTolLists t [] = error "converge: empty list"
convergeTolLists t xs = fromMaybe empty (convergeBy check Just xs)
    where
      empty = error "converge: error in impl"
      check (a:b:c:_)
          | (myTrace ("Converging at " ++ show a) a) == b = Just b
          | a == c = Just c
          | ((showOutput ("convergence check with tolerance " ++ show t) $ 
              magnitude (sumList $ (zipWith (\x y -> NPN.abs (x-y)) b c))) <= t) = showOutput ("convergence with tolerance "++ show t )$ Just c
      check _ = Nothing

type RKStepper (p::Nat) (q::Nat) t stateType = 
    (Ord t, Show t, Algebra.Module.C t (Multivector p q t), Algebra.Field.C t) => 
     t -> (t -> stateType -> stateType) -> 
    ([Multivector p q t] -> stateType) -> 
    (stateType ->[Multivector p q t]) ->
    (t,stateType) -> (t,stateType)
data ButcherTableau f = ButcherTableau {_tableauA :: [[f]], _tableauB :: [f], _tableauC :: [f]}
makeLenses ''ButcherTableau


type ConvergerFunction f = forall (p::Nat) (q::Nat) f . [[Multivector p q f]] -> [Multivector p q f]
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

{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double stateType] -> RKStepper 3 0 Double stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double [E3Vector]] -> RKStepper 3 0 Double [E3Vector]#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double stateType] -> RKStepper 3 1 Double stateType#-}
{-#SPECIALISE genericRKMethod :: ButcherTableau Double -> [RKAttribute Double [STVector]] -> RKStepper 3 1 Double [STVector]#-}
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
    {-#INLINE a#-}
    a n = (l !! (n-1)) & filter (/= zero) where
        l = _tableauA tableau
    b :: Int -> t
    b i = l !! (i - 1) where
        l = _tableauB tableau
    
    {-#INLINE sumListOfLists #-}
--    {-#SPECIALISE INLINE sumListOfLists :: [[STVector]]->[STVector]#-}
--    {-#SPECIALISE INLINE sumListOfLists :: [[Vector]]->[E3Vector]#-}
    sumListOfLists :: [[Multivector p q t]] -> [Multivector p q t]
    sumListOfLists = map sumList . transpose 

    converger :: [[Multivector p q t]] -> [Multivector p q t]
    converger = case  find (\x -> isConvergenceTolerance x || isConvergenceFunction x) attributes of
                  Just (ConvergenceFunction conv) -> conv
                  Just (ConvergenceTolerance tol) -> convergeTolLists (myTrace ("Convergence tolerance set to " ++ show tol)tol)
                  Nothing -> myTrace "No convergence tolerance specified, defaulting to equality" convergeList 

    stepSizeAdapter :: AdaptiveStepSizeFunction t stateType
    stepSizeAdapter = case find isAdaptiveStepSize attributes of
                        Just (AdaptiveStepSize sigma) -> sigma
                        Nothing -> (\_ _ -> one)

    {-#INLINE rkMethodImplicitFixedPoint#-}
--    {-#SPECIALISE rkMethodImplicitFixedPoint :: RKStepper 3 0 Double stateType #-}
--    {-#SPECIALISE rkMethodImplicitFixedPoint :: RKStepper 3 0 Double [E3Vector] #-}
--    {-#SPECIALISE rkMethodImplicitFixedPoint :: RKStepper 3 1 Double stateType #-}
--    {-#SPECIALISE rkMethodImplicitFixedPoint :: RKStepper 3 1 Double [STVector] #-}        
    rkMethodImplicitFixedPoint :: RKStepper p q t stateType
    rkMethodImplicitFixedPoint h f project unproject (time, state) =
        (time + (stepSizeAdapter time state)*h*(c s), newState) where
        zi :: Int -> [Multivector p q t]
        zi i = (\out -> myTrace ("initialGuess is " ++ show initialGuess++" whereas the final one is " ++ show out) out) $
                converger $ iterate (zkp1 i) initialGuess where
            initialGuess :: [Multivector p q t]
            initialGuess = if i == 1 || null (zi (i-1)) then map (h'*>) $ unproject $ f guessTime state else zi (i-1)
            adaptiveStepSizeFraction :: t
            adaptiveStepSizeFraction = stepSizeAdapter time state
            h' :: t
            h' = adaptiveStepSizeFraction *  h * (c i)
            guessTime :: t
            guessTime = time + h'
            zkp1 :: NPN.Int -> [Multivector p q t] -> [Multivector p q t]
            zkp1 i zk = map (h*>) (sumOfJs i zk) where
                {-#INLINE sumOfJs#-}
                sumOfJs :: Int -> [Multivector p q t] -> [Multivector p q t]
                sumOfJs i zk =  sumListOfLists $ map (scaledByAij zk) (a i) where 
                    {-# INLINE scaledByAij #-}
                    scaledByAij :: [Multivector p q t] -> t -> [Multivector p q t]
                    scaledByAij guess a = map (a*>) $ evalDerivatives guessTime $ elementAdd state' guess

        state' = unproject state :: [Multivector p q t]
        newState :: stateType
        newState = project $ elementAdd state' (assert (not $  null dy) dy)
        dy = sumListOfLists  [map ((b i) *>) (zi i) | i <- [1..s]] :: [Multivector p q t]
        {-#INLINE evalDerivatives #-}
        evalDerivatives :: t -> [Multivector p q t] -> [Multivector p q t]
        evalDerivatives time stateAtTime= unproject $ (f time) $ project stateAtTime


\end{code}






Look at creating an exponential integrator: https://en.wikipedia.org/wiki/Exponential_integrators





\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

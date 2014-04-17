\begin{code}
{-# LANGUAGE NoImplicitPrelude, UnicodeSyntax, NPlusKPatterns #-}
module Numeric.Clifford.Systems.Control where

import NumericPrelude hiding (foldl, map, take, (!!), foldl1)
--import Numeric.Clifford.Multivector
--import Numeric.Clifford.LinearOperators
--import Numeric.Clifford.Manifold
import Control.Wire
import Data.List.Stream
import Prelude.Unicode
import Algebra.Field
import Number.Ratio
import Data.MemoTrie

--makeDerivative order = makeNthDerivative 1 order


makeNthDerivative n order = 0 where


nthOrderCoefficients n order = map fromRational' $ map (δ n order )  [0 .. (order+n-1)] where
                     δ = generateFiniteDifferenceCoefficients [0,-1.. - (order+n)] 0

\end{code}
Finite difference coefficients generated from the algorithm in \cite {GenerationOfFiniteDifferenceFormulasOnArbitrarilySpacedGrids}
\begin{code}

--generateFiniteDifferenceCoefficients ∷ (Algebra.ToRational.C f) ⇒ [f] → [[[f]]]
generateFiniteDifferenceCoefficients gridPoints x₀= result where
        ω ∷ Integer → Rational → Rational
        ω n x |n ≤ 0 = one
              |otherwise =  foldl1 (*) $ map (\a → x-a) $ take (fromIntegral n)   $ map (fromValue) gridPoints 

        α∷ Integer → Rational
        α n = fromValue $ gridPoints !! (fromIntegral n)
        δ ∷ Integer → Integer → Integer → Rational
        δ = memo δ'
        δ' 0 0 0 = fromValue 1
        δ' m n ν | m < 0 = fromValue 0
                 | m ≡ n+1 = fromValue 0
                 | ν < n ∧ m ≤ n = (((α n) - x₀) *  (δ m (n-1) ν) - m `scale` δ (m-1) (n-1) ν ) / ((α  n) - α  ν)
                 | ν ≡ n ∧ m ≤ n = ((ω (n - 2) (α  (n-1))) / (ω (n-1) (α  n)))  * (m `scale` δ (m-1) (n-1) (n-1) - (α (n-1)- x₀) * δ m (n-1) (n-1))

        result = (\ m approxOrder ν → δ m (m + approxOrder - 1 ) ν )

\end{code}
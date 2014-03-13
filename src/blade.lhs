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

So yeah. This is a Clifford number representation. I will fill out the documentation more fully and stuff once the design has stabilised.

I am basing the design of this on Issac Trotts' geometric algebra library.\cite{hga}

Let us  begin. We are going to use the Numeric Prelude because it is (shockingly) nicer for numeric stuff.

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
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Numeric.Clifford.Blade where

import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate)
import Algebra.Laws
import Algebra.Absolute
import Algebra.Algebraic
import Algebra.Additive
import Algebra.Ring
import Algebra.OccasionallyScalar
import Algebra.ToInteger
import Algebra.Transcendental
import Algebra.ZeroTestable
import Algebra.Module
import Algebra.Field
import Data.Serialize
import Data.Word
import MathObj.Polynomial.Core (progression)
import System.IO
import Data.List.Stream
import Data.Permute (sort, isEven)
import Data.List.Ordered
import Data.Ord
import Data.Maybe
--import Number.NonNegative
import Numeric.Natural
import qualified Data.Vector as V
import NumericPrelude.Numeric (sum)
import qualified NumericPrelude.Numeric as NPN
import Test.QuickCheck
import Math.Sequence.Converge (convergeBy)
import Control.DeepSeq 
import Number.Ratio hiding (scale)
import Algebra.ToRational
import qualified GHC.Num as PNum
import Control.Lens hiding (indices)
import Control.Exception (assert)
import Data.Maybe
import Data.Data
import Data.DeriveTH
import Debug.Trace
--trace _ a = a

\end{code}


The first problem: How to represent basis blades. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}

data Blade f where
    Blade :: {-(Algebra.Field.C f) =>-} {_scale :: f, _indices :: [Natural]} -> Blade f

-- makeLenses ''Blade
scale :: Lens' (Blade f) f
scale = lens _scale (\blade v -> blade {_scale = v})
indices :: Lens' (Blade f) [Natural]
indices = lens _indices (\blade v -> blade {_indices = v})
bScale b =  b^.scale
bIndices b = b^.indices
instance(Show f) =>  Show (Blade f) where
    --TODO: Do this with HaTeX
    show  (Blade scale indices) = pref ++  if null indices then "" else basis where
                        pref = show scale
                        basis =  foldr (++) "" textIndices
                        textIndices = map vecced indices
                        vecced index = "\\vec{e_{" ++ show index ++ "}}"
                                                
                        
instance (Algebra.Additive.C f, Eq f) => Eq (Blade f) where
   a == b = aScale == bScale && aIndices == bIndices where
                 (Blade aScale aIndices) = bladeNormalForm a
                 (Blade bScale bIndices) = bladeNormalForm b

\end{code}

For example, a scalar could be constructed like so: \texttt{Blade s []}
\begin{code}
scalarBlade :: f -> Blade f
scalarBlade d = Blade d []

zeroBlade :: (Algebra.Additive.C f) => Blade f
zeroBlade = scalarBlade Algebra.Additive.zero

bladeNonZero b = b^.scale /= Algebra.Additive.zero

bladeNegate b = b&scale%~negate --Blade (Algebra.Additive.negate$ b^.scale) (b^.indices)

bladeScaleLeft s (Blade f ind) = Blade (s * f) ind
bladeScaleRight s (Blade f ind) = Blade (f * s) ind
\end{code}

However, the plain data constructor should never be used, for it doesn't order them by default. It also needs to represent the vectors in an ordered form for efficiency and niceness. Further, due to skew-symmetry, if the vectors are in an odd permutation compared to the normal form, then the scale is negative. Additionally, since $\vec{e}_k^2 = 1$, pairs of them should be removed.

\begin{align}
\vec{e}_1∧...∧\vec{e}_k∧...∧\vec{e}_k∧... = 0\\
\vec{e}_2∧\vec{e}_1 = -\vec{e}_1∧\vec{e}_2\\
\vec{e}_k^2 = 1
\end{align}


\begin{code}
bladeNormalForm :: (Algebra.Additive.C f) =>  Blade f -> Blade f
bladeNormalForm (Blade scale indices)  = Blade scale' uniqueSorted
        where
             numOfIndices = length indices
             (sorted, perm) = Data.Permute.sort numOfIndices indices
             scale' = if isEven perm then scale else negate scale
             uniqueSorted = removeDupPairs sorted
                            where
                              removeDupPairs [] = []
                              removeDupPairs [x] = [x]
                              removeDupPairs (x:y:rest) | x == y = removeDupPairs rest
                                                        | otherwise = x : removeDupPairs (y:rest)
\end{code}

What is the grade of a blade? Just the number of indices.

\begin{code}
grade :: Blade f -> Integer
grade = toInteger . length . bIndices 

bladeIsOfGrade :: Blade f -> Integer -> Bool
blade `bladeIsOfGrade` k = grade blade == k

bladeGetGrade ::(Algebra.Additive.C f) =>  Integer -> Blade f -> Blade f
bladeGetGrade k blade =
    if blade `bladeIsOfGrade` k then blade else zeroBlade
\end{code}



First up for operations: Blade multiplication. This is no more than assembling orthogonal vectors into k-vectors. 

\begin{code}
bladeMul :: (Algebra.Ring.C f) => Blade f -> Blade f-> Blade f
bladeMul x y = bladeNormalForm $ Blade (bScale x Algebra.Ring.* bScale y) (bIndices x ++ bIndices y)
multiplyBladeList :: Algebra.Ring.C f => [Blade f] -> Blade f
multiplyBladeList [] = error "Empty blade list!"
multiplyBladeList (a:[]) = a
multiplyBladeList a = bladeNormalForm $ Blade scale indices where
    indices = concatMap bIndices a
    scale = foldl1 (*) (map bScale a)


\end{code}

Next up: The outer (wedge) product, denoted by $∧$ :3

\begin{code}
bWedge :: (Algebra.Ring.C f) => Blade f -> Blade f -> Blade f
bWedge x y = bladeNormalForm $ bladeGetGrade k xy
             where
               k = grade x + grade y
               xy = bladeMul x y

\end{code}

Now let's do the inner (dot) product, denoted by $⋅$ :D


\begin{code}
bDot :: (Algebra.Ring.C f) => Blade f -> Blade f -> Blade f
bDot x y = bladeNormalForm $ bladeGetGrade k xy
          where
            k = Algebra.Absolute.abs $ grade x - grade y
            xy = bladeMul x y

propBladeDotAssociative = Algebra.Laws.associative bDot

\end{code}

These are the three fundamental operations on basis blades.

Now for linear combinations of (possibly different basis) blades. To start with, let's order basis blades:

\begin{code}
instance (Algebra.Additive.C f, Ord f) => Ord (Blade f) where
    compare a b | bIndices a == bIndices b = compare (bScale a) (bScale b)
                | otherwise =  compare (bIndices a) (bIndices b)


instance Arbitrary Natural where
    arbitrary = sized $ \n ->
                let n' = NPN.abs n in
                 fmap (toNatural . (\x -> (fromIntegral x)::Word)) (choose (0, n'))
    shrink = shrinkIntegral
$(derive makeArbitrary ''Blade)
\end{code}

Now for some testing of algebraic laws.

\begin{code}

{- Note: Figure out what this is meant to be lol
skewcommutative op x y = x `op` y == (bladeScaleLeft (fromInteger (-1))$ y `op` x)

propAnticommutativeMultiplication :: (Eq f,Algebra.Ring.C f, Algebra.Additive.C f) => Blade f -> Blade f -> Bool
propAnticommutativeMultiplication = anticommutative bladeMul
-}
propCommutativeAddition = commutative (+)
\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

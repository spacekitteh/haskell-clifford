\documentclass{article}
%include polycode.fmt
\usepackage{fontspec}
\usepackage{amsmath}
\usepackage{unicode-math}
\usepackage{lualatex-math}
\setmainfont{latinmodern-math.otf}
\setmathfont{latinmodern-math.otf}
\usepackage{verbatim}
\begin{document}
So yeah. This is a Clifford number representation. I will fill out the documentation more fully and stuff as I myself understand what the fuck I'm doing. 

I am basing the design of this on Issac Trotts' geometric algebra library.\cite{hga}

Let us  begin. We are going to use the Numeric Prelude because it is (shockingly) nicer for numeric stuff.

\begin{code}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
\end{code}
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Clifford  where

import NumericPrelude
import Algebra.Laws
import Algebra.Absolute
import Algebra.Additive
import Algebra.Ring
import Algebra.OccasionallyScalar
import Algebra.Transcendental
import Algebra.ZeroTestable
import Algebra.Module
import Algebra.Field
import System.IO
import Data.List
import Data.Permute
import Data.List.Ordered

import qualified Test.QuickCheck as QC
\end{code}


The first problem: How to represent basis blades. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}
data Blade f = Blade {bScale :: f, bIndices :: [Int]} deriving Show

instance (Algebra.Additive.C f , Eq f) => Eq (Blade f) where
    (==) a b = aScale == bScale && aIndices == bIndices where
                 (Blade aScale aIndices) = bladeNormalForm a
                 (Blade bScale bIndices) = bladeNormalForm b

\end{code}

For example, a scalar could be constructed like so: \texttt{Blade s []}
\begin{code}
scalar :: f -> Blade f
scalar d = Blade d []

zeroBlade :: (Algebra.Additive.C f) => Blade f
zeroBlade = scalar Algebra.Additive.zero
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
             scale' = if isEven perm then scale else Algebra.Additive.negate scale
             uniqueSorted = removeDupPairs sorted
                            where
                              removeDupPairs [] = []
                              removeDupPairs [x] = [x]
                              removeDupPairs (x:y:rest) | x == y = removeDupPairs rest
                                                        | otherwise = x : removeDupPairs (y:rest)
\end{code}

What is the grade of a blade? Just the number of indices.

\begin{code}
grade :: Blade f -> Int
grade b = length $ bIndices b

bladeIsOfGrade :: Blade f -> Int -> Bool
blade `bladeIsOfGrade` k = grade blade == k

bladeGetGrade ::(Algebra.Additive.C f) =>  Int -> Blade f -> Blade f
bladeGetGrade k blade =
    if blade `bladeIsOfGrade` k then blade else zeroBlade
\end{code}


First up for operations: Blade multiplication. This is no more than assebling orthogonal vectors into k-vectors. 

\begin{code}
bladeMul :: (Algebra.Ring.C f) => Blade f -> Blade f-> Blade f
bladeMul x y = bladeNormalForm $ Blade (bScale x Algebra.Ring.* bScale y) (bIndices x ++ bIndices y)

(*) = bladeMul
\end{code}

Next up: The outer (wedge) product, denoted by $∧$ :3

\begin{code}
bWedge :: (Algebra.Ring.C f) => Blade f -> Blade f -> Blade f
bWedge x y = bladeNormalForm $ bladeGetGrade k xy
             where
               k = (grade x) + (grade y)
               xy = bladeMul x y

(^) = bWedge
\end{code}

Now let's do the inner (dot) product, denoted by $⋅$ :D


\begin{code}
bDot :: (Algebra.Ring.C f) => Blade f -> Blade f -> Blade f
bDot x y = bladeNormalForm $ bladeGetGrade k xy
          where
            k = Algebra.Absolute.abs $ (grade x) - (grade y)
            xy = bladeMul x y

(.) = bDot
propBladeDotAssociative = Algebra.Laws.associative bDot

\end{code}

These are the three fundamental operations on basis blades.

Since blades of the same grade form a vector space, they can be added and scaled!

\begin{code}
--perhaps i should use type arithmetic to represent the grade?

--instance (Algebra.Additive.C f) => Algebra.Additive.C (Blade f) where
--    zero = zeroScalar
--    (+) a b =
        
\end{code}

\begin{align}
∇ ≡ \vec{\mathbf{x}}\frac{∂}{∂x} + \vec{\mathbf{y}}\frac{∂}{∂y} + \vec{\mathbf{z}}\frac{∂}{∂z}
\end{align}
This is a simple Clifford algebra implentation. or it was the start of one before i started
trying to do fancy emacs/latex trickery.

To compile this to a pdf, run
\begin{verbatim}
lhs2TeX clifford.lhs | xelatex --job="clifford" && evince clifford.pdf
\end{verbatim}
$\vec{∀}x∈R$
\begin{code}
--and this a valid haskell file. compile and run $∃$ with ``ghc clifford.lhs \&\& ./clifford'' 
cliff = 10

greeting = "hi dora :3333 <3"

swedish  = intersperse 'f'

inswedish = swedish greeting

main :: IO ()

main = putStrLn inswedish
\end{code}
\begin{code}

\end{code}
\begin{align}
hi
\end{align}
%this is actually a haskell file so yeah. the next page is the soruce code :v!!! :
%\newpage
%\verbatiminput{clifford.lhs}

\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

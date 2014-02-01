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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
\end{code}
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Clifford  where

import NumericPrelude hiding (Integer)
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
import MathObj.Polynomial.Core
import System.IO
import Data.List
import Data.Permute
import Data.List.Ordered
import Data.Ord
import Number.NonNegative
import NumericPrelude.Numeric (sum)
import qualified NumericPrelude.Numeric as NPN
import qualified Test.QuickCheck as QC
import Math.Sequence.Converge
\end{code}


The first problem: How to represent basis blades. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}
data Blade f = Blade {bScale :: f, bIndices :: [Integer]} 
instance(Show f) =>  Show (Blade f) where
    --TODO: Do this with HaTeX
    show  (Blade scale indices) = pref ++  if indices == [] then "" else basis where
                        pref = show scale
                        basis =  foldr (++) "" textIndices
                        textIndices = map vecced indices
                        vecced index = "\\vec{e_{" ++ (show index) ++ "}}"
                                                
                        
instance (Algebra.Additive.C f, Eq f) => Eq (Blade f) where
    (==) a b = aScale == bScale && aIndices == bIndices where
                 (Blade aScale aIndices) = bladeNormalForm a
                 (Blade bScale bIndices) = bladeNormalForm b

\end{code}

For example, a scalar could be constructed like so: \texttt{Blade s []}
\begin{code}
scalarBlade :: f -> Blade f
scalarBlade d = Blade d []

zeroBlade :: (Algebra.Additive.C f) => Blade f
zeroBlade = scalarBlade Algebra.Additive.zero

bladeNonZero b = bScale b /= Algebra.Additive.zero

bladeNegate b = Blade (Algebra.Additive.negate bScale b) (bIndices b)

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
grade :: Blade f -> Integer
grade b = fromNumber $ toInteger $ length $ bIndices b

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

Now for linear combinations of (possibly different basis) blades. To start with, let's order basis blades:

\begin{code}
instance (Algebra.Additive.C f, Ord f) => Ord (Blade f) where
    --compare :: Blade f -> Blade f -> Ordering
    compare a b  | bIndices a == bIndices b = compare (bScale a) (bScale b)
                 | otherwise = compare (bIndices a) (bIndices b)
\end{code}

A multivector is nothing but a linear combination of basis blades.

\begin{code}
data Multivector f = BladeSum { mvTerms :: [Blade f]} deriving (Show, Eq)

mvNormalForm mv = BladeSum $ if null resultant then [scalarBlade Algebra.Additive.zero] else resultant  where
    resultant = filter bladeNonZero $ addLikeTerms $ Data.List.Ordered.sortBy compare  $ map bladeNormalForm $ mvTerms mv

addLikeTerms :: (Algebra.Additive.C f) => [Blade f] -> [Blade f]
addLikeTerms [] = []
addLikeTerms [a] = [a]
addLikeTerms (x:y:rest) | bIndices x == bIndices y =
                            addLikeTerms $ (Blade (bScale x + bScale y) (bIndices x)) : rest
--                        | bIndices x 
                        | otherwise = x : addLikeTerms (y:rest)

--Constructs a multivector from a scaled blade.
e :: (Algebra.Additive.C f, Ord f) => f -> [Integer] -> Multivector f
s `e` indices = mvNormalForm $ BladeSum [Blade s indices]

scalar s = s `e` []


instance (Algebra.Additive.C f, Ord f) => Algebra.Additive.C (Multivector f) where
    a + b =  mvNormalForm $ BladeSum (mvTerms a ++ mvTerms b)
    a - b =  mvNormalForm $ BladeSum ((mvTerms a) ++ (map bladeNegate $ mvTerms b))
    zero = BladeSum $ [scalarBlade Algebra.Additive.zero]

\end{code}

Now it is time for the Clifford product. :3

\begin{code}

instance (Algebra.Ring.C f, Ord f) => Algebra.Ring.C (Multivector f) where
    a * b = mvNormalForm $ BladeSum [bladeMul x y | x <- mvTerms a, y <- mvTerms b]
    one = scalar Algebra.Ring.one
    fromInteger i = scalar $ Algebra.Ring.fromInteger i
\end{code}

Clifford numbers have a magnitude and absolute value:

\begin{code}

magnitude :: (Algebra.Algebraic.C f) => Multivector f -> f
magnitude mv = sqrt $ NumericPrelude.Numeric.sum $ map (\b -> (Algebra.Ring.^) (bScale b) 2) $ mvTerms mv

instance (Algebra.Absolute.C f, Algebra.Algebraic.C f, Ord f) => Algebra.Absolute.C (Multivector f) where
    abs v =  magnitude v `e` []
    signum (BladeSum [Blade scale []]) = scalar $ signum scale 
    signum (BladeSum []) = scalar Algebra.Additive.zero

instance (Algebra.Ring.C f, Ord f) => Algebra.Module.C f (Multivector f) where
  (*>) s v = (scalar s) * v

(/) :: (Algebra.Field.C f, Ord f) => Multivector f -> f -> Multivector f

(/) v d = (recip d) *> v


integratePoly c x = c : zipWith (Clifford./) x progression


exp ::(Algebra.Ring.C f, Eq f, Ord f, Algebra.Field.C f)=> Multivector f -> Multivector f
exp x = converge $ scanl (+) Algebra.Additive.zero $ expTerms x

takeEvery nth xs = case drop (nth-1) xs of
                     (y:ys) -> y : takeEvery nth ys
                     [] -> []

cosh x = converge $ scanl (+) Algebra.Additive.zero $ takeEvery 2 $ expTerms x

sinh x = converge $ scanl (+) Algebra.Additive.zero $ takeEvery 2 $ tail $ expTerms x

seriesPlusMinus (x:y:rest) = x:Algebra.Additive.negate y: seriesPlusMinus rest
seriesMinusPlus (x:y:rest) = Algebra.Additive.negate x : y : seriesMinusPlus rest


sin x = converge $ scanl (+) Algebra.Additive.zero $ sinTerms x
sinTerms x = seriesPlusMinus $ takeEvery 2 $ expTerms x
cos x = converge $ scanl (+) Algebra.Ring.one $ cosTerms x
cosTerms x = seriesMinusPlus $ takeEvery 2 $ tail $ expTerms x

expTerms x = [(Clifford./) (power k) (fromInteger $ factorial k) | k <- [(0::NPN.Integer)..]] where
        power k = (Algebra.Ring.^) x k
        factorial 0 = 1
        factorial 1 = 1
        factorial fac = fac * factorial (fac-1)

dot a b = mvNormalForm $ BladeSum [x `bDot` y | x <- mvTerms a, y <- mvTerms b]
wedge a b = mvNormalForm $ BladeSum [x `bWedge` y | x <- mvTerms a, y <- mvTerms b]
\end{code}

\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

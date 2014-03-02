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
\title{haskell-clifford: A Haskell Clifford algebra library}
\begin{document}

So yeah. This is a Clifford number representation. I will fill out the documentation more fully and stuff as I myself understand what the fuck I'm doing. 

I am basing the design of this on Issac Trotts' geometric algebra library.\cite{hga}

Let us  begin. We are going to use the Numeric Prelude because it is (shockingly) nicer for numeric stuff.

\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
\end{code}
%if False
\begin{code}
{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -O3 -optlc-O=3 #-}
--  OPTIONS_GHC -Odph -fvectorise
--  LANGUAGE ParallelArrays
\end{code}
%endif
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Clifford where

import NumericPrelude hiding (Integer, iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate)
--import Algebra.Laws
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
import MathObj.Polynomial.Core (progression)
import System.IO
import Data.List.Stream
import Data.Permute (sort, isEven)
import Data.List.Ordered
import Data.Ord
import Data.Maybe
import Number.NonNegative
import qualified Data.Vector as V
import NumericPrelude.Numeric (sum)
import Numeric.Compensated
import qualified NumericPrelude.Numeric as NPN
--import qualified Test.QuickCheck as QC
import Math.Sequence.Converge (convergeBy)
import Control.DeepSeq 
import Number.Ratio hiding (scale)
import Algebra.ToRational
import qualified GHC.Num as PNum
import Control.Lens hiding (indices)
import Control.Exception (assert)
--import Debug.Trace
trace _ a = a

\end{code}


The first problem: How to represent basis blades. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}
data Blade f = Blade {_scale :: f, _indices :: [Integer]} 
makeLenses ''Blade
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
grade = fromNumber.toInteger.length.bIndices 

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

--propBladeDotAssociative = Algebra.Laws.associative bDot

\end{code}

These are the three fundamental operations on basis blades.

Now for linear combinations of (possibly different basis) blades. To start with, let's order basis blades:

\begin{code}
instance (Algebra.Additive.C f, Ord f) => Ord (Blade f) where
    compare a b | bIndices a == bIndices b = compare (bScale a) (bScale b)
                | otherwise =  compare (bIndices a) (bIndices b)
\end{code}

A multivector is nothing but a linear combination of basis blades.

\begin{code}
data Multivector f = BladeSum { _terms :: [Blade f]} deriving (Show, Eq, Ord)

makeLenses ''Multivector
mvNormalForm mv = BladeSum $ if null resultant then [scalarBlade Algebra.Additive.zero] else resultant  where
    resultant = filter bladeNonZero $ addLikeTerms' $ Data.List.Ordered.sortBy compare $ mv^.terms & map bladeNormalForm
mvTerms m = m^.terms

addLikeTerms' = sumLikeTerms . groupLikeTerms

groupLikeTerms ::Eq f =>  [Blade f] -> [[Blade f]]
groupLikeTerms = groupBy (\a b -> a^.indices == b^.indices)

compensatedSum' :: (Algebra.Additive.C f) => [f] -> f
compensatedSum' xs = kahan zero zero xs where
    kahan s _ [] = s
    kahan s c (x:xs) = 
        let y = x - c
            t = s + y
        in kahan t ((t-s)-y) xs

--use this to sum taylor series et al with converge
--compensatedRunningSum :: (Algebra.Additive.C f) => [f] -> [f]
compensatedRunningSum xs=shanksTransformation . map fst $ scanl kahanSum (zero,zero) xs where
    kahanSum (s,c) b = (t,newc) where
        y = b - c
        t = s + y
        newc = (t - s) - y
            
--multiplyAdd a b c = a*b + c
--twoProduct a b = (x,y) where
--    x = a*b
--z    y = multiplyAdd a b (negate x)

--multiplyList [] = []
--multiplyList a@(x:[])=a
--multiplyList (a:b:xs) = loop a (b:xs) zero where
--  loop pm [] ei = pm+ei
--  loop pm1 (ai:remaining) eim1= loop pi remaining ei where
--      (pi, pii) = twoProduct pm1 ai
--      ei = multiplyAdd eim1 ai pii


multiplyOutBlades :: Algebra.Ring.C a => [Blade a] -> [Blade a] -> [Blade a]
multiplyOutBlades x y = [bladeMul l r | l <-x, r <- y]

--multiplyList :: Algebra.Ring.C t => [Multivector t] -> Multivector t
multiplyList [] = error "Empty list"
--multiplyList a@(x:[]) = x
multiplyList l = mvNormalForm $ BladeSum listOfBlades where
    expandedBlades :: Algebra.Ring.C a => [[Blade a]] -> [Blade a]
    expandedBlades a = foldl1 multiplyOutBlades a
    listOfBlades = expandedBlades $ map mvTerms l

--things to test: is 1. adding blades into a map based on indices 2. adding errything together 3. sort results quicker than
--                   1. sorting by indices 2. groupBy-ing on indices 3. adding the lists of identical indices

sumList xs = mvNormalForm $ BladeSum $ Data.List.Stream.concat $ map mvTerms xs

sumLikeTerms :: (Algebra.Additive.C f) => [[Blade f]] -> [Blade f]
sumLikeTerms blades = map (\sameIxs -> map bScale sameIxs & compensatedSum' & (\result -> Blade result ((head sameIxs) & bIndices))) blades



--Constructs a multivector from a scaled blade.
e :: (Algebra.Additive.C f, Ord f) => f -> [Integer] -> Multivector f
s `e` indices = mvNormalForm $ BladeSum [Blade s indices]
scalar s = s `e` []

instance (Control.DeepSeq.NFData f) => Control.DeepSeq.NFData (Multivector f)
instance (Control.DeepSeq.NFData f) => Control.DeepSeq.NFData (Blade f)
instance (Algebra.Additive.C f, Ord f) => Algebra.Additive.C (Multivector f) where
    a + b =  mvNormalForm $ BladeSum (mvTerms a ++ mvTerms b)
    a - b =  mvNormalForm $ BladeSum (mvTerms a ++ map bladeNegate (mvTerms b))
    zero = BladeSum [scalarBlade Algebra.Additive.zero]
\end{code}

Now it is time for the Clifford product. :3

\begin{code}

instance (Algebra.Ring.C f, Ord f) => Algebra.Ring.C (Multivector f) where
    BladeSum [Blade s []] * b = BladeSum $ map (bladeScaleLeft s) $ mvTerms b
    a * BladeSum [Blade s []] = BladeSum $ map (bladeScaleRight s) $ mvTerms a 
    a * b = mvNormalForm $ BladeSum [bladeMul x y | x <- mvTerms a, y <- mvTerms b]
    one = scalar Algebra.Ring.one
    fromInteger i = scalar $ Algebra.Ring.fromInteger i    

    a ^ 2 = a * a
    a ^ 0 = one
    a ^ 1 = a
    --a ^ n  --n < 0 = Clifford.recip $ a ^ (negate n)
    a ^ n  =  multiplyList (Data.List.Stream.replicate (NPN.fromInteger n) a)

two = fromInteger 2
mul = (Algebra.Ring.*)
\end{code}

Clifford numbers have a magnitude and absolute value:

\begin{code}

--magnitude :: (Algebra.Algebraic.C f) => Multivector f -> f
magnitude = sqrt . compensatedSum' . map (\b -> (bScale b)^ 2) . mvTerms

instance (Algebra.Absolute.C f, Algebra.Algebraic.C f, Ord f) => Algebra.Absolute.C (Multivector f) where
    abs v =  magnitude v `e` []
    signum (BladeSum [Blade scale []]) = scalar $ signum scale 
    signum (BladeSum []) = scalar Algebra.Additive.zero

instance (Algebra.Ring.C f, Ord f) => Algebra.Module.C f (Multivector f) where
--    (*>) zero v = Algebra.Additive.zero
    (*>) s v = v & mvTerms & map (bladeScaleLeft s) & BladeSum



(/) :: (Algebra.Field.C f, Ord f) => Multivector f -> f -> Multivector f
(/) v d = BladeSum $ map (bladeScaleLeft (NPN.recip d)) $ mvTerms v --Algebra.Field.recip d *> v

(</) n d = Clifford.inverse d * n
(/>) n d = n * Clifford.inverse d
(</>) n d = n /> d

integratePoly c x = c : zipWith (Clifford./) x progression

--converge :: (Eq f, Show f) => [f] -> f
converge [] = error "converge: empty list"
converge xs = fromMaybe empty (convergeBy checkPeriodic Just xs) 
    where
      empty = error "converge: error in implmentation"
      checkPeriodic (a:b:c:_)
          | (trace ("Converging at " ++ show a) a) == b = Just a
          | a == c = Just a
      checkPeriodic _ = Nothing

convergeTol t [] = error "converge: empty list"
convergeTol t xs = fromMaybe empty (convergeBy check Just xs)
    where
      empty = error "converge: error in impl"
      check (a:b:c:_)
          | (trace ("Converging at " ++ show a) a) == b = Just a
          | a == c = Just a
          | magnitude (a - b) <= t = Just b
      check _ = Nothing

aitkensAcceleration [] = []
aitkensAcceleration a@(xn:[]) = a
aitkensAcceleration a@(xn:xnp1:[]) = a
aitkensAcceleration a@(xn:xnp1:xnp2:[]) = a
aitkensAcceleration (xn:xnp1:xnp2:xs) | xn == xnp1 = [xnp1]
                                      | xn == xnp2 = [xnp2]
                                      | otherwise = xn - ((dxn ^ 2) /> ddxn) : aitkensAcceleration (xnp1:xnp2:xs) where
    dxn = sumList [xnp1,negate xn]
    ddxn = sumList [xn,  (-2) *  xnp1, xnp2]

shanksTransformation [] = []
shanksTransformation a@(xnm1:[]) = a
shanksTransformation a@(xnm1:xn:[]) = a
shanksTransformation (xnm1:xn:xnp1:xs) | xnm1 == xn = [xn]
                                       | xnm1 == xnp1 = [xnm1]
                                       | denominator == zero = [xnp1]
                                       | otherwise = trace ("Shanks transformation input = " ++ show xn ++ "\nShanks transformation output = " ++ show out) out:shanksTransformation (xn:xnp1:xs) where
                                       out = numerator />  denominator 
                                       numerator = sumList [xnp1*xnm1, negate (xn^2)]
                                       denominator = sumList [xnp1, (-2)*xn, xnm1] 


--exp ::(Ord f, Show f, Algebra.Transcendental.C f)=> Multivector f -> Multivector f
exp (BladeSum [ Blade s []]) = trace ("scalar exponential of " ++ show s) scalar $ Algebra.Transcendental.exp s
exp x = trace ("Computing exponential of " ++ show x) convergeTerms x where --(expMag ^ expScaled) where
    --todo: compute a ^ p via a^n where n = floor p then multiply remaining power
    expMag = Algebra.Transcendental.exp mag
    expScaled = converge $ shanksTransformation.shanksTransformation . compensatedRunningSum $ expTerms scaled 
    convergeTerms terms = converge $ shanksTransformation.shanksTransformation.compensatedRunningSum $ expTerms terms
    mag = trace ("In exponential, magnitude is " ++ show ( magnitude x)) magnitude x
    scaled = let val = (Clifford./) x mag in trace ("In exponential, scaled is" ++ show val) val





takeEvery nth xs = case drop (nth-1) xs of
                     (y:ys) -> y : takeEvery nth ys
                     [] -> []

cosh x = converge $ shanksTransformation.compensatedRunningSum $ takeEvery 2 $ expTerms x

sinh x = converge $ shanksTransformation.compensatedRunningSum $ takeEvery 2 $ tail $ expTerms x

seriesPlusMinus (x:y:rest) = x:Algebra.Additive.negate y: seriesPlusMinus rest
seriesMinusPlus (x:y:rest) = Algebra.Additive.negate x : y : seriesMinusPlus rest


sin x = converge $ shanksTransformation $ compensatedRunningSum $ sinTerms x
sinTerms x = seriesPlusMinus $ takeEvery 2 $ expTerms x
cos x = converge $ shanksTransformation $ compensatedRunningSum (Algebra.Ring.one : cosTerms x)
cosTerms x = seriesMinusPlus $ takeEvery 2 $ tail $ expTerms x

expTerms x = map snd $ iterate (\(n,b) -> (n + 1, (x*b) Clifford./ fromInteger n )) (1::NPN.Integer,one)

dot a b = mvNormalForm $ BladeSum [x `bDot` y | x <- mvTerms a, y <- mvTerms b]
wedge a b = mvNormalForm $ BladeSum [x `bWedge` y | x <- mvTerms a, y <- mvTerms b]
(∧) = wedge
(⋅) = dot

reverseBlade b = bladeNormalForm $ b & indices %~ reverse 
reverseMultivector v = mvNormalForm $ v & terms.traverse%~ reverseBlade

inverse a = assert (a /= zero) $ reverseMultivector a Clifford./ bScale (head $ mvTerms (a * reverseMultivector a))
recip=Clifford.inverse

instance (Algebra.Additive.C f, Ord f) => Algebra.OccasionallyScalar.C f (Multivector f) where
    toScalar = bScale . bladeGetGrade 0 . head . mvTerms
    toMaybeScalar (BladeSum [Blade s []]) = Just s
    toMaybeScalar (BladeSum []) = Just Algebra.Additive.zero
    toMaybeScalar _ = Nothing
    fromScalar = scalar
\end{code}

Also, we may as well implement the standard prelude Num interface.

\begin{code}
instance (Algebra.Ring.C f,Algebra.Algebraic.C f, Algebra.Additive.C f, Ord f) => PNum.Num (Multivector f) where
    (+) = (Algebra.Additive.+)
    (-) = (Algebra.Additive.-)
    (*) = (Algebra.Ring.*)
    negate = NPN.negate
    abs = scalar . magnitude 
    fromInteger = Algebra.Ring.fromInteger
    signum m = Clifford.inverse (scalar $ magnitude m) * m


\end{code}
 
Let's use Newton or Halley iteration to find the principal n-th root :3

\begin{code}
root ::(Show f, Eq f,Ord f, Algebra.Algebraic.C f) => NPN.Integer -> Multivector f -> Multivector f
root n (BladeSum [Blade s []]) = scalar $ Algebra.Algebraic.root n s
root n a = converge $ rootIterationsStart n a one

rootIterationsStart ::(Algebra.Field.C f, Ord f, Show f, Algebra.Algebraic.C f)=>  NPN.Integer -> Multivector f -> Multivector f -> [Multivector f]
rootIterationsStart n a@(BladeSum (Blade s [] :xs)) one = rootHalleysIterations n a g where
                     g = if s >= NPN.zero then one else Algebra.Ring.one `e` [1,2] --BladeSum[Blade Algebra.Ring.one [1,2]]
rootIterationsStart n a g = rootHalleysIterations n a g


rootNewtonIterations :: (Algebra.Field.C f, Ord f) => NPN.Integer -> Multivector f -> Multivector f -> [Multivector f]
rootNewtonIterations n a = iterate xkplus1 where
                     xkplus1 xk = xk + deltaxk xk
                     deltaxk xk = oneOverN * ((Clifford.inverse (xk ^ (n - one))* a)  - xk)
                     oneOverN = scalar $ NPN.recip $ fromInteger n

rootHalleysIterations :: (Algebra.Field.C a, Show a, Ord a, Algebra.Algebraic.C a) => NPN.Integer -> Multivector a -> Multivector a -> [Multivector a]
rootHalleysIterations n a = halleysMethod f f' f'' where
    f x = a - (x^n)
    f' x = fromInteger (-n) * (x^(n-1))
    f'' x = fromInteger (-(n*(n-1))) * (x^(n-2))


pow a p = (a ^ up) Clifford./> Clifford.root down a where
    ratio = toRational p
    up = numerator ratio
    down = denominator ratio


halleysMethod :: (Algebra.Field.C a, Show a, Ord a, Algebra.Algebraic.C a) => (Multivector a -> Multivector a) -> (Multivector a -> Multivector a) -> (Multivector a -> Multivector a) -> Multivector a -> [Multivector a]
halleysMethod f f' f'' = iterate update where
    update x = (trace ("Halley iteration at " ++ show x) x) - (numerator x * Clifford.inverse (denominator x)) where
        numerator x = multiplyList [2, fx, dfx]
        denominator x = multiplyList [2, dfx, dfx] - (fx * ddfx)
        fx = f x
        dfx = f' x
        ddfx = f'' x


secantMethod f x0 x1 = update x1 x0  where
    update xm1 xm2 | xm1 == xm2 = [xm1]
                   | otherwise = if x == xm1 then [x] else x : update x xm1 where
      x = xm1 - f xm1 * (xm1-xm2) * Clifford.inverse (f xm1 - f xm2)


\end{code}

Now let's try logarithms by fixed point iteration. It's gonna be slow, but whatever!

\begin{code}

normalised a = a * (scalar $ NPN.recip $ magnitude a)

log (BladeSum [Blade s []]) = scalar $ NPN.log s
log a = scalar (NPN.log mag) + log' scaled where
    scaled = normalised a
    mag = magnitude a
    log' a = converge $  halleysMethod f f' f'' (one `e` [1,2])  where
         f x = a - Clifford.exp x
         f' x = NPN.negate $ Clifford.exp x
         f'' = f'
\end{code}

Now let's do (slow as fuck probably) numerical integration! :D~! Since this is gonna be used for physical applications, it's we're gonna start off with a Hamiltonian structure and then a symplectic integrator.

\begin{code}

data EnergyMethod f = Hamiltonian{ _dqs :: [DynamicSystem f -> Multivector f], _dps :: [DynamicSystem f -> Multivector f]}

data DynamicSystem f = DynamicSystem {_time :: f, coordinates :: [Multivector f], _momenta :: [Multivector f], _energyFunction :: EnergyMethod f, _projector :: DynamicSystem f -> DynamicSystem f}

makeLenses ''EnergyMethod
makeLenses ''DynamicSystem

--evaluateDerivative s = (dq, dp) where
--    dq = (s&energyFunction.dqs) -- s
--    dp = (s&energyFunction.dps) -- s
--    dq = map ($ s) ((dqs $ energyFunction) s) --s&energyFunction.dqs.traverse--map ($ s) ((dqs . energyFunction) s)
--    dp = map ($ s) ((dps $ energyFunction) s)

--add function to project to allowable configuration space after each update step 
--use secant or whatever method for fixed point iteration for implicit parts of runge kutta


rk4Classical :: (Ord a, Algebra.Algebraic.C a) =>  stateType -> a -> (stateType->stateType) -> ([Multivector a] -> stateType) -> (stateType -> [Multivector a]) -> stateType
rk4Classical state h f project unproject = project newState where
    update = map (\(k1', k2', k3', k4') -> sumList [k1',2*k2',2*k3',k4'] / Algebra.Ring.fromInteger 6) $ zip4 k1 k2 k3 k4
    newState = map (uncurry (+)) $ Data.List.Stream.zip state' update
    state' = unproject state
    evalDerivatives x = unproject $ f $ project x
    k1 = map (h*>) $ evalDerivatives state'
    k2 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (/ two) k1)
    k3 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (/ two) k2)
    k4 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' k3

rk4ClassicalList state h f = rk4Classical state h f id id


elementAdd = zipWith (+)
elementScale = zipWith (*>) 
a `elementSub` b = zipWith (-) a b
a `elementMul` b = zipWith (*) a b
data ButcherTableau f = ButcherTableau {_tableauA :: [[f]], _tableauB :: [f], _tableauC :: [f]}
makeLenses ''ButcherTableau

--rk4ClassicalTableau :: ButcherTableau NPN.Double
rk4ClassicalTableau = ButcherTableau [[0,0,0,0],[0.5,0,0,0],[0,0.5,0,0],[0,0,1,0]] [1.0 NPN./6,1.0 NPN./3, 1.0 NPN./3, 1.0 NPN./6] [0, 0.5, 0.5, 1]
implicitEulerTableau = ButcherTableau [[1.0::NPN.Double]] [1] [1]
data RKAttribute f state = Explicit
                 | HamiltonianFunction
                 | AdaptiveStepSize {sigma :: f -> state -> f}
                 | ConvergenceTolerance {epsilon :: f}
                 | ConvergenceFunction {converger :: [Multivector f] -> Multivector f }
                 | RootSolver 
                 | UseAutomaticDifferentiationForRootSolver
                 | StartingGuessMethod

sumVector = sumList . V.toList 

--systemRootSolver :: [Multivector f] -> [Multivector f] -> ratio -> [Multivector f] -> [Multivector f] -> [Multivector f]

--This will stop as soon as one of the elements converges. This is bad. Need to make it skip convergent ones and focus on the remainig.
systemBroydensMethod f x0 x1 = map fst $ update (x1,ident) x0  where
    update (xm1,jm1) xm2 | any (== zero) dx =  [(xm1,undefined)]
                   | otherwise = if x == xm1 then [(x,undefined)] else (x,j) : update (x,j) xm1 where
      x = xm1 `elementSub` ( (fm1 `elementMul` dx) `elementMul` ody)
      j = undefined
      fm1 = f xm1
      fm2 = f xm2
      dx = elementSub xm1 xm2
      dy = elementSub fm1 fm2
      ody = map Clifford.inverse dy
    ident = undefined

--TODO: implement Broyden-Fletcher-Goldfarb-Shanno method

rk4ClassicalFromTableau (t,state) h f = impl (t, state) h f id id where
    impl = genericRKMethod rk4ClassicalTableau []
implicitEulerMethod (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod implicitEulerTableau []

lobattoIIIASecondOrderTableau = ButcherTableau [[0,0],[0.5::NPN.Double,0.5]] [0.5,0.5] [0,1]
lobattoIIIASecondOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIASecondOrderTableau []
lobattoIIIAFourthOrderTableau = ButcherTableau [[0,0,0],[((5 NPN./24)::NPN.Double),1 NPN./3,-1 NPN./24],[1 NPN./6,2 NPN./3,1 NPN./6]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIAFourthOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIAFourthOrderTableau []

lobattoIIIBFourthOrderTableau = ButcherTableau [[1 NPN./6,(-1) NPN./6,0],[((1 NPN./6)::NPN.Double),1 NPN./3,0],[1 NPN./6,5 NPN./6, 0]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIBFourthOrder (t, state) h f = impl (t, state) h f id id where
    impl = genericRKMethod lobattoIIIBFourthOrderTableau []

convergeList ::(Show f, Ord f) => [[f]] -> [f]
convergeList = converge

type RKStepper t stateType = (Ord t, Show t, Algebra.Module.C t (Multivector t), Algebra.Additive.C t) => 
    (t, stateType) -> t -> 
    (t -> stateType -> stateType) -> 
    ([Multivector t] -> stateType) -> 
    (stateType ->[Multivector t]) -> 
    (t,stateType)
showOutput name x = trace ("output of " ++ name ++" is " ++ show x) x
genericRKMethod :: forall t stateType . ( Ord t, Show t, Algebra.Module.C t (Multivector t), Algebra.Additive.C t) =>  ButcherTableau t -> [RKAttribute t stateType] -> RKStepper t stateType
genericRKMethod tableau attributes = rkMethodImplicitFixedPoint where
    s =  length (_tableauC tableau)
    c n = l !!  (n-1) where
        l = _tableauC tableau
    a n = (l !! (n-1)) & filter (/= zero) where
        l = _tableauA tableau
    b i = l !! (i - 1) where
        l = _tableauB tableau
    sumListOfLists = (map sumList) . transpose 
    rkMethodImplicitFixedPoint :: RKStepper t stateType
    rkMethodImplicitFixedPoint (time, state) h f project unproject = (time + h*c s, project newState) where
        zi i = assert (i <= s && i>= 1) $ convergeList $ iterate (zkp1 i) initialGuess where
            initialGuess = if i == 1 || null (zi (i-1)) then map (h'*>) $ unproject $ f guessTime state else zi (i-1)
            h' = h * c i
            guessTime = time + h'
            zkp1 :: NPN.Int -> [Multivector t] -> [Multivector t]
            zkp1 i zk= map (h*>) (sumOfJs i zk) where
                sumOfJs i zk =  sumListOfLists $ map (scaledByAij zk) (a i) where 
                    scaledByAij guess a = map (a*>) $ evalDerivatives guessTime $ elementAdd state' guess
        state' = unproject state
        newState = elementAdd state' dy
        dy :: [Multivector t]
        dy = sumListOfLists $ [map ((b i)*>) (zi i) | i <- [1..s]] 
        evalDerivatives :: t -> [Multivector t] -> [Multivector t]
        evalDerivatives time x = unproject $ f time $ project x


\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

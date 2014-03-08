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

So yeah. This is a Clifford number representation. I will fill out the documentation more fully and stuff as I myself understand what the fuck I'm doing. 

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
module Numeric.Clifford.Multivector where
import Numeric.Clifford.Blade
import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate, all)
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
import Data.Serialize
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

sumList xs = mvNormalForm $ BladeSum $ concat $ map mvTerms xs

sumLikeTerms :: (Algebra.Additive.C f) => [[Blade f]] -> [Blade f]
sumLikeTerms blades = map (\sameIxs -> map bScale sameIxs & compensatedSum' & (\result -> Blade result ((head sameIxs) & bIndices))) blades



--Constructs a multivector from a scaled blade.
e :: (Algebra.Additive.C f, Ord f) => f -> [Natural] -> Multivector f
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
    a ^ n  =  multiplyList (replicate (NPN.fromInteger n) a)

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

(</) n d = Numeric.Clifford.Multivector.inverse d * n
(/>) n d = n * Numeric.Clifford.Multivector.inverse d
(</>) n d = n /> d

integratePoly c x = c : zipWith (Numeric.Clifford.Multivector./) x progression

--converge :: (Eq f, Show f) => [f] -> f
converge [] = error "converge: empty list"
converge xs = fromMaybe empty (convergeBy checkPeriodic Just xs) 
    where
      empty = error "converge: error in implmentation"
      checkPeriodic (a:b:c:_)
          | (trace ("Converging at " ++ show a) a) == b = Just a
          | a == c = Just a
      checkPeriodic _ = Nothing



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
    scaled = let val = (Numeric.Clifford.Multivector./) x mag in trace ("In exponential, scaled is" ++ show val) val





takeEvery nth xs = case drop (nth-1) xs of
                     (y:ys) -> y : takeEvery nth ys
                     [] -> []

cosh x = converge $ shanksTransformation . compensatedRunningSum $ takeEvery 2 $ expTerms x

sinh x = converge $ shanksTransformation . compensatedRunningSum $ takeEvery 2 $ tail $ expTerms x

seriesPlusMinus (x:y:rest) = x:Algebra.Additive.negate y: seriesPlusMinus rest
seriesMinusPlus (x:y:rest) = Algebra.Additive.negate x : y : seriesMinusPlus rest


sin x = converge $ shanksTransformation $ compensatedRunningSum $ sinTerms x
sinTerms x = seriesPlusMinus $ takeEvery 2 $ expTerms x
cos x = converge $ shanksTransformation $ compensatedRunningSum (Algebra.Ring.one : cosTerms x)
cosTerms x = seriesMinusPlus $ takeEvery 2 $ tail $ expTerms x

expTerms x = map snd $ iterate (\(n,b) -> (n + 1, (x*b) Numeric.Clifford.Multivector./ fromInteger n )) (1::NPN.Integer,one)

dot a b = mvNormalForm $ BladeSum [x `bDot` y | x <- mvTerms a, y <- mvTerms b]
wedge a b = mvNormalForm $ BladeSum [x `bWedge` y | x <- mvTerms a, y <- mvTerms b]
(∧) = wedge
(⋅) = dot

reverseBlade b = bladeNormalForm $ b & indices %~ reverse 
reverseMultivector v = mvNormalForm $ v & terms.traverse%~ reverseBlade

inverse a = assert (a /= zero) $ reverseMultivector a Numeric.Clifford.Multivector./ bScale (head $ mvTerms (a * reverseMultivector a))
recip=Numeric.Clifford.Multivector.inverse

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
    signum m = Numeric.Clifford.Multivector.inverse (scalar $ magnitude m) * m


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
                     deltaxk xk = oneOverN * ((Numeric.Clifford.Multivector.inverse (xk ^ (n - one))* a)  - xk)
                     oneOverN = scalar $ NPN.recip $ fromInteger n

rootHalleysIterations :: (Algebra.Field.C a, Show a, Ord a, Algebra.Algebraic.C a) => NPN.Integer -> Multivector a -> Multivector a -> [Multivector a]
rootHalleysIterations n a = halleysMethod f f' f'' where
    f x = a - (x^n)
    f' x = fromInteger (-n) * (x^(n-1))
    f'' x = fromInteger (-(n*(n-1))) * (x^(n-2))


pow a p = (a ^ up) Numeric.Clifford.Multivector./> Numeric.Clifford.Multivector.root down a where
    ratio = toRational p
    up = numerator ratio
    down = denominator ratio


halleysMethod :: (Algebra.Field.C a, Show a, Ord a, Algebra.Algebraic.C a) => (Multivector a -> Multivector a) -> (Multivector a -> Multivector a) -> (Multivector a -> Multivector a) -> Multivector a -> [Multivector a]
halleysMethod f f' f'' = iterate update where
    update x = x - (numerator x * Numeric.Clifford.Multivector.inverse (denominator x)) where
        numerator x = multiplyList [2, fx, dfx]
        denominator x = multiplyList [2, dfx, dfx] - (fx * ddfx)
        fx = f x
        dfx = f' x
        ddfx = f'' x


secantMethod f x0 x1 = update x1 x0  where
    update xm1 xm2 | xm1 == xm2 = [xm1]
                   | otherwise = if x == xm1 then [x] else x : update x xm1 where
      x = xm1 - f xm1 * (xm1-xm2) * Numeric.Clifford.Multivector.inverse (f xm1 - f xm2)


\end{code}

Now let's try logarithms by fixed point iteration. It's gonna be slow, but whatever!

\begin{code}

normalised a = a * (scalar $ NPN.recip $ magnitude a)

log (BladeSum [Blade s []]) = scalar $ NPN.log s
log a = scalar (NPN.log mag) + log' scaled where
    scaled = normalised a
    mag = magnitude a
    log' a = converge $  halleysMethod f f' f'' (one `e` [1,2])  where
         f x = a - Numeric.Clifford.Multivector.exp x
         f' x = NPN.negate $ Numeric.Clifford.Multivector.exp x
         f'' = f'
\end{code}

Now let's do (slow as fuck probably) numerical integration! :D~! Since this is gonna be used for physical applications, it's we're gonna start off with a Hamiltonian structure and then a symplectic integrator.

\begin{code}

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


data RigidBody f where
 RigidBody:: (Algebra.Field.C f, Algebra.Module.C f (Multivector f)) =>  {position :: PhysicalVector f,
                              _momentum :: PhysicalVector f,
                              _mass :: f,
                              _attitude :: PhysicalVector f,
                              _angularMomentum :: PhysicalVector f,
                              _inertia :: PhysicalVector f
                             } -> RigidBody f




{- $(derive makeSerialize ''Blade)
$(derive makeSerialize ''Multivector)
$(derive makeData ''Blade)
$(derive makeTypeable ''Blade)
$(derive makeData ''Multivector)
$(derive makeTypeable ''Multivector)-}

$(derive makeArbitrary ''Multivector)
\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

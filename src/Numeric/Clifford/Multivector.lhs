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
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs#-}
{-# LANGUAGE FlexibleInstances, StandaloneDeriving, KindSignatures, DataKinds #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
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
import Number.Ratio hiding (scale, recip)
import Algebra.ToRational
import qualified GHC.Num as PNum
import Control.Lens hiding (indices)
import Control.Exception (assert)
import Data.Maybe
import Data.Monoid
import Data.Data
import Data.DeriveTH
import GHC.TypeLits
import Control.Lens.Lens
import Data.Word
import Control.Applicative ((<$>))
import Numeric.Clifford.Internal


\end{code}


A multivector is nothing but a linear combination of basis blades.

\begin{code}
data Multivector (p::Nat) (q::Nat) f where
    BladeSum :: forall (p::Nat) (q::Nat) f . (Ord f, Algebra.Field.C f,SingI p, SingI q) => { _terms :: [Blade p q f]} -> Multivector p q f

type STVector = Multivector 3 1 Double
type E3Vector = Multivector 3 0 Double

instance (SingI p, SingI q, Algebra.Field.C f, Arbitrary f, Ord f) => Arbitrary (Multivector p q f) where
    arbitrary = mvNormalForm <$> BladeSum <$> (vector d) where
       p' = (fromSing (sing :: Sing p)) :: Integer
       q' = (fromSing (sing :: Sing q)) 
       d = fromIntegral (p' + q')

deriving instance Eq (Multivector p q f)
--instance  (SingI p, SingI q) => Functor (Multivector p q) where
--    fmap func x =  func x--((terms x) & scale %~ func)
deriving instance Ord (Multivector p q f)
deriving instance (Show f) => Show (Multivector p q f)
--deriving instance (Read f) => Read (Multivector p q f)

signature :: forall (p::Nat) (q::Nat) f. (SingI p, SingI q) => Multivector p q f ->  (Natural,Natural)
signature _ = (toNatural  ((fromIntegral $ fromSing (sing :: Sing p))::Word),toNatural  ((fromIntegral $ fromSing (sing :: Sing q))::Word))

terms :: Lens' (Multivector p q f) [Blade p q f]
terms = lens _terms (\bladeSum v -> bladeSum {_terms = v})

{-# INLINE mvNormalForm #-}
mvNormalForm (BladeSum terms) = BladeSum $ if null resultant then [scalarBlade Algebra.Additive.zero] else resultant  where
    resultant = filter bladeNonZero $ addLikeTerms' $ Data.List.Ordered.sortBy compare $  map bladeNormalForm $ terms
{-#INLINE mvTerms #-}
mvTerms m = m^.terms

{-# INLINE addLikeTerms' #-}
addLikeTerms' = sumLikeTerms . groupLikeTerms

{-# INLINE groupLikeTerms #-}
groupLikeTerms ::Eq f =>  [Blade p q f] -> [[Blade p q f]]
groupLikeTerms = groupBy (\a b -> a^.indices == b^.indices)

compareTol :: (Algebra.Algebraic.C f, Algebra.Absolute.C f, Ord f, SingI p, SingI q) => Multivector p q f -> Multivector p q f -> f -> Bool
compareTol x y tol = ((NPN.abs $ magnitude (x-y) ) <= tol)

{-#INLINE compensatedSum' #-}
compensatedSum' :: (Algebra.Additive.C f) => [f] -> f
compensatedSum' xs = kahan zero zero xs where
    kahan s _ [] = s
    kahan s c (x:xs) = 
        let y = x - c
            t = s + y
        in kahan t ((t-s)-y) xs

--use this to sum taylor series et al with converge
{-#INLINE compensatedRunningSum#-}
{-#SPECIALISE INLINE compensatedRunningSum :: [STVector] -> [STVector] #-}
{-#SPECIALISE INLINE compensatedRunningSum :: [E3Vector] -> [E3Vector] #-}
compensatedRunningSum :: (Algebra.Algebraic.C f, Ord f, SingI p, SingI q, Show f) => [Multivector p q f] -> [Multivector p q f]
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


multiplyOutBlades :: (SingI p, SingI q, Algebra.Ring.C a) => [Blade p q a] -> [Blade p q a] -> [Blade p q a]
multiplyOutBlades x y = [bladeMul l r | l <-x, r <- y]

--multiplyList :: Algebra.Ring.C t => [Multivector t] -> Multivector t
multiplyList [] = error "Empty list"
--multiplyList a@(x:[]) = x
multiplyList l = mvNormalForm $ BladeSum listOfBlades where
    expandedBlades a = foldl1 multiplyOutBlades a
    listOfBlades = expandedBlades $ map mvTerms l
multiplyList1 l = mvNormalForm $ BladeSum listOfBlades where
    expandedBlades a = foldl1 multiplyOutBlades a
    listOfBlades = expandedBlades $ map mvTerms l
--things to test: is 1. adding blades into a map based on indices 2. adding errything together 3. sort results quicker than
--                   1. sorting by indices 2. groupBy-ing on indices 3. adding the lists of identical indices

{-#INLINE sumList #-}
sumList xs = mvNormalForm $ BladeSum $ concat $ map mvTerms xs

{-#INLINE sumLikeTerms #-}
{-#SPECIALISE INLINE sumLikeTerms :: [[STBlade]] -> [STBlade] #-}
{-#SPECIALISE INLINE sumLikeTerms :: [[E3Blade]] -> [E3Blade] #-}
sumLikeTerms :: (Algebra.Field.C f, SingI p, SingI q) => [[Blade p q f]] -> [Blade p q f]
sumLikeTerms blades = map (\sameIxs -> map bScale sameIxs & compensatedSum' & (\result -> Blade result ((head sameIxs) & bIndices))) blades


instance (Algebra.Field.C f, SingI p, SingI q, Ord f) => Data.Monoid.Monoid (Sum (Multivector p q f)) where
    mempty = Data.Monoid.Sum Algebra.Additive.zero
    mappend (Data.Monoid.Sum x) (Data.Monoid.Sum y)= Data.Monoid.Sum  (x + y)
    mconcat = Data.Monoid.Sum . sumList . map getSum

instance (Algebra.Field.C f, SingI p, SingI q, Ord f) => Data.Monoid.Monoid (Product (Multivector p q f)) where
    mempty = Product one
    mappend (Product x) (Product y) = Product (x * y)
    mconcat = Product . foldl (*) one . map getProduct

--Constructs a multivector from a scaled blade.
{-#INLINE e#-}
e :: (Algebra.Field.C f, Ord f, SingI p, SingI q) => f -> [Natural] -> Multivector p q f
s `e` indices = mvNormalForm $ BladeSum [Blade s indices]
{-#INLINE scalar#-}
scalar s = s `e` []


instance (Control.DeepSeq.NFData f) => Control.DeepSeq.NFData (Multivector p q f)


{-{-# RULES
 "turn multiple additions into sumList" forall (a::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) (b::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) (c::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) .  (+) a ((+) b c) = sumList [a,b,c]
 #-}-}
{-#RULES
 "sumList[..] + a = sumList [..,a]" forall  (a::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) xs. (+) (sumList xs) a = sumList (a:xs)
 #-}
{-# RULES
 "a+ sumList[..] = sumList [..,a]"  forall (a::Multivector p q (Algebra.Field.C f)) xs. (+) a (sumList xs) = sumList (a:xs)
 #-}
instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Algebra.Additive.C (Multivector p q f) where
    {-#INLINE (+)#-}
    {-#SPECIALISE (+)::STVector -> STVector -> STVector #-}
    {-#SPECIALISE (+)::E3Vector -> E3Vector -> E3Vector #-}
    a + b =  mvNormalForm $ BladeSum (mvTerms a ++ mvTerms b)
    {-#INLINE (-)#-}
    {-#SPECIALISE (-)::STVector -> STVector -> STVector #-}
    {-#SPECIALISE (-)::E3Vector -> E3Vector -> E3Vector #-}
    a - b =  mvNormalForm $ BladeSum (mvTerms a ++ map bladeNegate (mvTerms b))
    zero = BladeSum [scalarBlade Algebra.Additive.zero]

    
\end{code}

Now it is time for the Clifford product. :3

\begin{code}
{-{-# RULES
 "turn multiple multiplications into multiplyList1" forall (a::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) b c .  (*) ((*) a b) c = multiplyList1 [a,b,c]
 #-}-}
{-#RULES
 "multiplyList1[..] * a = multiplyList1 [..,a]" forall  (a::Multivector (p::Nat) (q::Nat) (Algebra.Field.C f)) xs. (*) (multiplyList1 xs) a = multiplyList1 (concat [xs,[a]])
 #-}
{-# RULES
 "a* multiplyList1[..] = multiplyList1 [..,a]"  forall (a::Multivector p q (Algebra.Field.C f)) xs. (*) a (multiplyList1 xs) = multiplyList1 (a:xs)
 #-}
instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Algebra.Ring.C (Multivector p q f) where
    {-#INLINE (*)#-}
    {-#SPECIALISE (*)::STVector ->STVector -> STVector#-}
    {-#SPECIALISE (*)::E3Vector ->E3Vector ->E3Vector #-}
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

psuedoScalar :: forall (p::Nat) (q::Nat) f. (Ord f, Algebra.Field.C f, SingI p, SingI q) =>  Multivector p q f
psuedoScalar = one `e` [0..(toNatural d)] where
    d = fromIntegral (p' + q' - 1 )::Word
    p'= fromSing (sing :: Sing p)
    q' = fromSing (sing :: Sing q)

\end{code}

Clifford numbers have a magnitude and absolute value:

\begin{code}


{-# INLINE magnitude #-}
{-# SPECIALISE INLINE magnitude:: Multivector 3 1 Double -> Double #-}
{-# SPECIALISE INLINE magnitude:: Multivector 3 0 Double -> Double #-}
magnitude :: (Algebra.Algebraic.C f) => Multivector p q f -> f
magnitude = sqrt . compensatedSum' . map (\b -> (bScale b)^ 2) . mvTerms

instance (Algebra.Absolute.C f, Algebra.Algebraic.C f, Ord f, SingI p, SingI q) => Algebra.Absolute.C (Multivector p q f) where
    abs v =  magnitude v `e` []
    signum (BladeSum [Blade scale []]) = scalar $ signum scale 
    signum (BladeSum []) = scalar Algebra.Additive.zero

instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Algebra.Module.C f (Multivector p q f) where
--    (*>) zero v = Algebra.Additive.zero
    {-#INLINE (*>) #-}
    {-#SPECIALISE INLINE (*>) :: Double -> STVector -> STVector #-}
    {-#SPECIALISE INLINE (*>) :: Double -> E3Vector -> E3Vector #-}
    (*>) s v = v & mvTerms & map (bladeScaleLeft s) & BladeSum



--(/) :: (Algebra.Field.C f, Ord f, SingI p, SingI q) => Multivector p q f -> f -> Multivector p q f
--(/) v d = BladeSum $ map (bladeScaleLeft (NPN.recip d)) $ mvTerms v --Algebra.Field.recip d *> v
{-#INLINE (</)#-}
(</) n d = Numeric.Clifford.Multivector.inverse d * n
{-#INLINE (/>)#-}
(/>) n d = n * Numeric.Clifford.Multivector.inverse d
(</>) n d = n /> d

{-#INLINE scaleLeft #-}
scaleLeft s v = BladeSum $ map (bladeScaleLeft s) $ mvTerms v
{-#INLINE scaleRight #-}
scaleRight v s = BladeSum $ map (bladeScaleRight s) $ mvTerms v
{-#INLINE divideRight #-}
divideRight v s = scaleRight v (recip s)
--integratePoly c x = c : zipWith (Numeric.Clifford.Multivector./) x progression

{-# INLINE converge#-}
converge [] = error "converge: empty list"
converge xs = fromMaybe empty (convergeBy checkPeriodic Just xs) 
    where
      empty = error "converge: error in implmentation"
      checkPeriodic (a:b:c:_)
          | (myTrace ("Converging at " ++ show a) a) == b = Just a
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

{-# INLINABLE shanksTransformation #-}
{-#SPECIALISE shanksTransformation :: [Multivector 3 0 Double] -> [Multivector 3 0 Double] #-}
{-#SPECIALISE shanksTransformation :: [Multivector 3 1 Double] -> [Multivector 3 1 Double] #-}
shanksTransformation :: (Algebra.Algebraic.C f, Ord f, Show f, SingI p, SingI q) =>  [Multivector p q f] -> [Multivector p q f]
shanksTransformation [] = []
shanksTransformation a@(xnm1:[]) = a
shanksTransformation a@(xnm1:xn:[]) = a
shanksTransformation (xnm1:xn:xnp1:xs) | xnm1 == xn = [xn]
                                       | xnm1 == xnp1 = [xnm1]
                                       | denominator == zero = [xnp1]
                                       | otherwise = myTrace ("Shanks transformation input = " ++ show xn ++ "\nShanks transformation output = " ++ show out) out:shanksTransformation (xn:xnp1:xs) where
                                       out = numerator />  denominator 
                                       numerator = sumList [xnp1*xnm1, negate (xn^2)]
                                       denominator = sumList [xnp1, (-2)*xn, xnm1] 




{-# INLINABLE takeEvery #-}
takeEvery nth xs = case drop (nth-1) xs of
                     (y:ys) -> y : takeEvery nth ys
                     [] -> []



seriesPlusMinus (x:y:rest) = x:Algebra.Additive.negate y: seriesPlusMinus rest
seriesMinusPlus (x:y:rest) = Algebra.Additive.negate x : y : seriesMinusPlus rest





{-#INLINE expTerms#-}
{-# SPECIALISE INLINE expTerms :: STVector -> [STVector]#-}
{-# SPECIALISE INLINE expTerms :: E3Vector -> [E3Vector]#-}
expTerms :: (Algebra.Algebraic.C f, SingI p, SingI q, Ord f) => Multivector p q f -> [Multivector p q f]
expTerms x = map snd $ iterate (\(n,b) -> (n + 1, (recip $ fromInteger n ) `scaleLeft` (x*b) )) (1::NPN.Integer,one)

instance (Algebra.Transcendental.C f, Ord f, SingI p, SingI q, Show f) => Algebra.Transcendental.C (Multivector p q f) where
    pi = scalar pi
    {-#INLINABLE exp#-}
    {-# SPECIALISE INLINE exp :: STVector -> STVector #-}
    {-# SPECIALISE INLINE exp :: E3Vector -> E3Vector #-}
    exp (BladeSum [ Blade s []]) = myTrace ("scalar exponential of " ++ show s) scalar $ exp s
    exp x = myTrace ("Computing exponential of " ++ show x) convergeTerms x where --(expMag ^ expScaled) where
        expMag = exp mag
        expScaled = converge $ shanksTransformation.shanksTransformation . compensatedRunningSum $ expTerms scaled 
        convergeTerms terms = converge $ shanksTransformation.shanksTransformation.compensatedRunningSum $ expTerms terms
        mag = myTrace ("In exponential, magnitude is " ++ show ( magnitude x)) magnitude x
        scaled = let val =  (recip mag) *> x in myTrace ("In exponential, scaled is" ++ show val) val
    {-#INLINE log#-}
    {-# SPECIALISE INLINE log :: STVector -> STVector #-}
    {-# SPECIALISE INLINE log :: E3Vector -> E3Vector #-}
    log (BladeSum [Blade s []]) = scalar $ NPN.log s
    log a = scalar (log mag) + log' scaled where
        (scaled,mag) = normalised a
        log' a = converge $  halleysMethod f f' f'' (one `e` [1,2])  where
         {-#INLINABLE f#-}
         f x = a - exp x
         {-#INLINABLE f'#-}
         f' x = NPN.negate $ exp x
         {-#INLINABLE f''#-}
         f'' = f'
    sin (BladeSum [Blade s []]) = scalar $ sin s
    sin x = converge $ shanksTransformation $ compensatedRunningSum $ sinTerms x where
      sinTerms x = seriesPlusMinus $ takeEvery 2 $ expTerms x
    cos (BladeSum [Blade s []]) = scalar $ cos s
    cos x = converge $ shanksTransformation $ compensatedRunningSum (one : cosTerms x) where
      cosTerms x = seriesMinusPlus $ takeEvery 2 $ tail $ expTerms x
    
    atan (BladeSum [Blade s []]) = scalar $ atan s
    atan z = (z/onePlusZSquared) * (one + (converge $ shanksTransformation $ compensatedRunningSum $ map lambda [1..])) where
      lambda :: Integer -> Multivector p q f
      lambda n = multiplyList1 $ map innerFraction [1..n]
      innerFraction :: Integer -> Multivector p q f
      innerFraction k = (tk*zSquared)/>((tk+one)*(onePlusZSquared)) where
        tk = fromInteger (2*k)        
      zSquared = z^2 :: Multivector p q f
      onePlusZSquared = one+z^2 :: Multivector p q f

    cosh x = converge $ shanksTransformation . compensatedRunningSum $ takeEvery 2 $ expTerms x
    sinh x = converge $ shanksTransformation . compensatedRunningSum $ takeEvery 2 $ tail $ expTerms x

dot :: Multivector p q f -> Multivector p q f -> Multivector p q f
dot a@(BladeSum _)  b@(BladeSum _) = mvNormalForm $ BladeSum [x `bDot` y | x <- mvTerms a, y <- mvTerms b]
wedge::Multivector p q f -> Multivector p q f->Multivector p q f
wedge a@(BladeSum _)  b@(BladeSum _) = mvNormalForm $ BladeSum [x `bWedge` y | x <- mvTerms a, y <- mvTerms b]

(∧) :: Multivector p q f -> Multivector p q f -> Multivector p q f
(∧) = wedge 
(⋅) :: Multivector p q f -> Multivector p q f -> Multivector p q f
(⋅) = dot 

{-# INLINE reverseBlade #-}
reverseBlade b = bladeNormalForm $ b & indices %~ reverse 
{-# INLINE reverseMultivector #-}
reverseMultivector v = mvNormalForm $ v & terms.traverse%~ reverseBlade

{-#INLINE inverse#-}
{-#SPECIALISE INLINE inverse :: STVector -> STVector #-}
{-# SPECIALISE INLINE inverse :: E3Vector -> E3Vector #-}
inverse a@(BladeSum _)  = assert (a /= zero) $ (recip scalarComponent) *> (reverseMultivector a)  where
    scalarComponent = bScale (head $ mvTerms (a * reverseMultivector a))


instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Algebra.Field.C (Multivector p q f) where
    recip = inverse

instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Algebra.OccasionallyScalar.C f (Multivector p q f) where
    toScalar = bScale . bladeGetGrade 0 . head . mvTerms
    toMaybeScalar (BladeSum [Blade s []]) = Just s
    toMaybeScalar (BladeSum []) = Just Algebra.Additive.zero
    toMaybeScalar _ = Nothing
    fromScalar = scalar
\end{code}

Also, we may as well implement the standard prelude Num interface.

\begin{code}
instance (Algebra.Algebraic.C f, SingI p, SingI q,  Ord f) => PNum.Num (Multivector p q f) where
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
instance (Algebra.Algebraic.C f, Show f, Ord f, SingI p, SingI q) =>  Algebra.Algebraic.C (Multivector p q f) where
    root 0 _ = error "Cannot take 0th root"
    root _ (BladeSum []) = error "Empty bladesum"
    root _ (BladeSum [Blade zero []]) = error "Cannot compute a root of zero"
    root n (BladeSum [Blade s []]) = scalar $ root n s
    root n a@(BladeSum _) = converge $ rootIterationsStart n a g where
      g = if q' <= 1 then  one`e`[q',succ q'] else one + one `e` [0,1]
      (p',q') = signature a

rootIterationsStart ::(Ord f, Show f, Algebra.Algebraic.C f)=>  NPN.Integer -> Multivector p q f -> Multivector p q f -> [Multivector p q f]
rootIterationsStart n a@(BladeSum (Blade s [] :_)) one = rootHalleysIterations n a g where
                     g = if s >= NPN.zero || q' == 1 then one else (Algebra.Ring.one `e` [0,1])
                     (p',q') = signature a
                     
rootIterationsStart n a@(BladeSum _) g = rootHalleysIterations n a g


rootNewtonIterations :: (Algebra.Field.C f, Ord f, SingI p, SingI q) => NPN.Integer -> Multivector p q f -> Multivector p q f -> [Multivector p q f]
rootNewtonIterations n a = iterate xkplus1 where
                     xkplus1 xk = xk + deltaxk xk
                     deltaxk xk = oneOverN * ((inverse (xk ^ (n - one))* a)  - xk)
                     oneOverN = scalar $ NPN.recip $ fromInteger n

rootHalleysIterations :: (Show a, Ord a, Algebra.Algebraic.C a, SingI p, SingI q) => NPN.Integer -> Multivector p q a -> Multivector p q a -> [Multivector p q a]
rootHalleysIterations n a = halleysMethod f f' f'' where
    f x = a - (x^n)
    f' x = fromInteger (-n) * (x^(n-1))
    f'' x = fromInteger (-(n*(n-1))) * (x^(n-2))


{-pow a p = (a ^ up) Numeric.Clifford.Multivector./> Numeric.Clifford.Multivector.root down a where
    ratio = toRational p
    up = numerator ratio
    down = denominator ratio-}

{-#INLINE halleysMethod #-}
{-#SPECIALISE halleysMethod :: (STVector->STVector)->(STVector->STVector)->(STVector->STVector)->STVector->[STVector]#-}
{-#SPECIALISE halleysMethod :: (E3Vector->E3Vector)->(E3Vector->E3Vector)->(E3Vector->E3Vector)->E3Vector->[E3Vector]#-}
halleysMethod :: (Show a, Ord a, Algebra.Algebraic.C a, SingI p, SingI q) => (Multivector p q a -> Multivector p q a) -> (Multivector p q a -> Multivector p q a) -> (Multivector p q a -> Multivector p q a) -> Multivector p q a -> [Multivector p q a]
halleysMethod f f' f'' = iterate update where
    update x = x - (numerator x * inverse (denominator x) ) where
        numerator x= multiplyList [2, fx, dfx]
        denominator x= multiplyList [2, dfx, dfx] - (fx * ddfx)
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
{-#INLINE normalised#-}
{-#SPECIALISE INLINE normalised :: STVector -> (STVector, Double) #-}
{-#SPECIALISE INLINE normalised :: E3Vector -> (E3Vector, Double) #-}
normalised :: (Ord f, Algebra.Algebraic.C f, SingI p, SingI q) => Multivector p q f -> (Multivector p q f,f)
normalised a = (a `scaleRight` ( recip $ mag),mag) where
    mag = magnitude a


\end{code}

Now let's do (slow as fuck probably) numerical integration! :D~! Since this is gonna be used for physical applications, it's we're gonna start off with a Hamiltonian structure and then a symplectic integrator.

\begin{code}



{- $(derive makeSerialize ''Blade)
$(derive makeSerialize ''Multivector)
$(derive makeData ''Blade)
$(derive makeTypeable ''Blade)
$(derive makeData ''Multivector)
$(derive makeTypeable ''Multivector)-}

-- $(derive makeArbitrary ''Multivector)

\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

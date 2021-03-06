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
{-# LANGUAGE FlexibleInstances,  UnicodeSyntax, GADTs, KindSignatures, DataKinds #-}
{-# LANGUAGE TemplateHaskell, StandaloneDeriving, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}
\end{code}
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Numeric.Clifford.Blade where

import NumericPrelude hiding (iterate, head, map, tail, reverse, scanl, zipWith, drop, (++), filter, null, length, foldr, foldl1, zip, foldl, concat, (!!), concatMap,any, repeat, replicate, elem, replicate, foldr1, abs)
import Algebra.Laws hiding (zero)
import Algebra.Absolute
import Algebra.Additive
import Control.DeepSeq
import Algebra.Ring
import Data.Serialize
import Data.Word
import Data.List.Stream
import Data.Permute (sort, isEven)
import Numeric.Natural
import qualified NumericPrelude.Numeric as NPN hiding (abs)
import Test.QuickCheck
import Control.Lens hiding (indices)
import Data.DeriveTH
import GHC.TypeLits hiding (isEven, isOdd)
import Data.Proxy
import GHC.Real (fromIntegral, toInteger)
import Algebra.Field
import Data.MemoTrie
import Numeric.Clifford.Internal
import Numeric.Compensated
import Prelude.Unicode
\end{code}


The first problem: How to represent basis blades. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}


data Blade (p ∷ Nat) (q ∷ Nat) f where
    Blade ∷ forall (p∷Nat) (q∷Nat) f . (KnownNat p, KnownNat q, Algebra.Field.C f) ⇒ {_scale ∷ f, _indices ∷ [Natural]} → Blade p q f

type STBlade = Blade 3 1 Double
type E3Blade = Blade 3 0 Double
--scale ∷ Lens (Blade p q f) (Blade p q g) f g
scale = lens _scale (\b@(Blade _ ind) v → Blade v ind)
indices ∷ Lens' (Blade p q f) [Natural]
indices = lens _indices (\blade v → blade {_indices = v})
dimension ∷ forall (p∷Nat) (q∷Nat) f. (KnownNat p, KnownNat q) ⇒ Blade p q f →  (Natural,Natural)
dimension _ = (toNatural  ((GHC.Real.fromIntegral $ natVal (Proxy∷Proxy p))∷Word),toNatural((GHC.Real.fromIntegral $ natVal (Proxy ∷ Proxy q))∷Word))

{-# INLINE bScale #-}
bScale ∷ Blade p q f → f
bScale b@(Blade _ _) =  b^.scale
{-# INLINE bIndices #-}
bIndices ∷ Blade p q f → [Natural]
bIndices b = b^.indices
instance (Control.DeepSeq.NFData f) ⇒ Control.DeepSeq.NFData (Blade p q f)
instance(Show f) ⇒  Show (Blade p q f) where
    --TODO: Do this with HaTeX
    show  (Blade scale indices) = pref ++  if null indices then "" else basis where
                        pref = show scale
                        basis =  foldr (++) "" textIndices
                        textIndices = map vecced indices
                        vecced index = "\\vec{e_{" ++ show index ++ "}}"
                                                
                        
instance (Algebra.Additive.C f, Eq f) ⇒ Eq (Blade p q f) where
   a == b = aScale ≡ bScale ∧ aIndices ≡ bIndices where
                 (Blade aScale aIndices) = bladeNormalForm a
                 (Blade bScale bIndices) = bladeNormalForm b

\end{code}

For example, a scalar could be constructed like so: \texttt{Blade s []}
\begin{code}
scalarBlade ∷ (Algebra.Field.C f, KnownNat p, KnownNat q) ⇒ f → Blade p q f
scalarBlade d = Blade d []

zeroBlade ∷ (Algebra.Field.C f, KnownNat p, KnownNat q ) ⇒ Blade p q f
zeroBlade = scalarBlade zero

bladeNonZero ∷ (Algebra.Additive.C f, Eq f) ⇒ Blade p q f → Bool
bladeNonZero (Blade s _) = s ≢ Algebra.Additive.zero

bladeNegate ∷ (Algebra.Additive.C f) ⇒  Blade p q f → Blade p q f
bladeNegate b@(Blade _ _) = b&scale%~negate 

{-# INLINE bladeScaleLeft #-}
{-# SPECIALISE bladeScaleLeft∷Double→STBlade → STBlade #-}
{-# SPECIALISE bladeScaleLeft∷Double→E3Blade → E3Blade #-}
bladeScaleLeft ∷ f → Blade p q f → Blade p q f
bladeScaleLeft s (Blade f ind) = Blade (s `mul` f) ind
bladeScaleRight ∷ f → Blade p q f → Blade p q f
{-# INLINE bladeScaleRight #-}
{-# SPECIALISE bladeScaleRight∷Double→STBlade → STBlade #-}
{-# SPECIALISE bladeScaleRight∷Double→E3Blade → E3Blade #-}
bladeScaleRight s (Blade f ind) = Blade (f `mul` s) ind
\end{code}

However, the plain data constructor should never be used, for it doesn't order them by default. It also needs to represent the vectors in an ordered form for efficiency and niceness. Further, due to skew-symmetry, if the vectors are in an odd permutation compared to the normal form, then the scale is negative. Additionally, since $\vec{e}_k^2 = 1$, pairs of them should be removed.

\begin{align}
\vec{e}_1∧...∧\vec{e}_k∧...∧\vec{e}_k∧... = 0\\
\vec{e}_2∧\vec{e}_1 = -\vec{e}_1∧\vec{e}_2\\
\vec{e}_k^2 = 1
\end{align}

\begin{code}

{-#INLINE bladeNormalForm#-}
{-#SPECIALISE INLINE bladeNormalForm∷E3Blade → E3Blade #-}
{-#SPECIALISE INLINE bladeNormalForm ∷ STBlade → STBlade #-}
bladeNormalForm ∷ ∀ (p∷Nat) (q∷Nat) f.  Blade p q f → Blade p q f
bladeNormalForm (Blade scale indices)  = result 
        where
             result = if (any (\i → (GHC.Real.toInteger i) ≥ d) indices) then zeroBlade else Blade scale' newIndices
             p' = (natVal (Proxy ∷ Proxy p)) ∷ Integer
             q' = (natVal (Proxy ∷ Proxy q)) ∷ Integer
             d = p' + q'             
             scale' = if doNotNegate  then scale else negate scale
             (newIndices, doNotNegate) = sortIndices (indices,q')

sortIndices ∷ ([Natural],Integer) → ([Natural],Bool)
sortIndices = memo sortIndices' where
sortIndices' ∷ ([Natural],Integer) → ([Natural],Bool) 
sortIndices' (indices,q') = (uniqueSorted, doNotNegate) where
    (sorted, perm) = Data.Permute.sort numOfIndices indices
    numOfIndices = length indices
    doNotNegate = (isEven perm) ≢ (negated)
    (uniqueSorted,negated) = removeDupPairs [] sorted False where
         removeDupPairs ∷ [Natural] → [Natural] → Bool → ([Natural],Bool)
         removeDupPairs accum [] negated = (accum,negated)
         removeDupPairs accum [x] negated = (accum++[x],negated)
         removeDupPairs accum (x:y:rest) negated  | x ≡ y  = 
                                                      if  GHC.Real.toInteger x <  q' 
                                                      then removeDupPairs accum rest (not negated)
                                                      else removeDupPairs accum rest negated
                                                  | otherwise = removeDupPairs (accum++[x]) (y:rest) negated
\end{code}

What is the grade of a blade? Just the number of indices.

\begin{code}
grade ∷ Blade p q f → Integer
grade = GHC.Real.toInteger . length . bIndices 

bladeIsOfGrade ∷ Blade p q f → Integer → Bool
blade `bladeIsOfGrade` k = grade blade ≡ k

bladeGetGrade ∷ Integer → Blade p q f → Blade p q f
bladeGetGrade k blade@(Blade _ _) =
    if blade `bladeIsOfGrade` k then blade else zeroBlade
\end{code}



First up for operations: Blade multiplication. This is no more than assembling orthogonal vectors into k-vectors. 

\begin{code}
{-#INLINE bladeMul #-}
{-#SPECIALISE INLINE bladeMul ∷ STBlade → STBlade → STBlade #-}
{-#SPECIALISE INLINE bladeMul ∷ E3Blade → E3Blade → E3Blade #-}
bladeMul ∷  Blade p q f → Blade p q f→ Blade p q f
bladeMul x@(Blade _ _) y@(Blade _ _)= bladeNormalForm $ Blade ((bScale x) `mul` (bScale y)) (bIndices x ++ bIndices y) 

{-# RULES
 "mulCompensable"  mul   = mulDouble
 #-}
mul ∷ Algebra.Ring.C f ⇒ f → f → f
mul x y = x*y

{-#SPECIALISE mulCompensable ∷ Double → Double → Double #-}
{-#SPECIALISE INLINE mulCompensable ∷ Float → Float → Float #-}
mulDouble ∷ Double → Double → Double
mulDouble = mulCompensable
mulCompensable ∷ (Algebra.Ring.C f, Compensable f) ⇒ f → f → f
mulCompensable x y = uncompensated (times x y compensated) 

multiplyBladeList ∷ (KnownNat p, KnownNat q, Algebra.Field.C f) ⇒ [Blade p q f] → Blade p q f
multiplyBladeList [] = error "Empty blade list!"
multiplyBladeList (a:[]) = a
multiplyBladeList a = bladeNormalForm (Blade scale indices) where
    indices = concatMap bIndices a
    scale = (foldl1' (*) (map bScale a)) 
{-# RULES
 "mulBladeListComp"  multiplyBladeList  = multiplyBladeListDouble 
 #-}
multiplyBladeListDouble ∷ (KnownNat p, KnownNat q) ⇒ [Blade p q Double] → Blade p q Double
multiplyBladeListDouble = multiplyBladeListCompensated
multiplyBladeListCompensated ∷ (KnownNat p, KnownNat q, Algebra.Field.C f, Compensable f) ⇒ [Blade p q f] → Blade p q f
multiplyBladeListCompensated [] = error "Empty blade list!"
multiplyBladeListCompensated (a:[]) = a
multiplyBladeListCompensated a = bladeNormalForm (Blade scale indices) where
    indices = concatMap bIndices a
    scale = (foldr (*^) (compensated one zero) (map bScale a))  & uncompensated


\end{code}

Next up: The outer (wedge) product, denoted by $∧$ :3

\begin{code}
bWedge ∷ Blade p q f → Blade p q f → Blade p q f
bWedge x y = bladeNormalForm $ bladeGetGrade k xy
             where
               k = grade x + grade y
               xy = bladeMul x y

\end{code}

Now let's do the inner (dot) product, denoted by $⋅$ :D


\begin{code}
bDot ∷Blade p q f → Blade p q f → Blade p q f
bDot x y = bladeNormalForm $ bladeGetGrade k xy
          where
            k = abs (grade x - grade y)
            xy = bladeMul x y

propBladeDotAssociative ∷ (Algebra.Additive.C f, Eq f) ⇒ Blade p q f → Blade p q f → Blade p q f → Bool
propBladeDotAssociative = Algebra.Laws.associative bDot

\end{code}

These are the three fundamental operations on basis blades.

Now for linear combinations of (possibly different basis) blades. To start with, let's order basis blades:

\begin{code}
instance (Algebra.Additive.C f, Ord f) ⇒ Ord (Blade p q f) where
    compare a b | bIndices a ≡ bIndices b = compare (bScale a) (bScale b)
                | otherwise = compareIndices (bIndices a) (bIndices b)

compareIndices ∷ [Natural] → [Natural] → Ordering
compareIndices = memo compareIndices' where
    compareIndices' a b =  case compare (length a) (length b) of
                                LT → LT
                                GT → GT
                                EQ → compare a b


instance (KnownNat p, KnownNat q, Algebra.Field.C f, Arbitrary f) ⇒ Arbitrary (Blade p q f) where
    arbitrary = do
      let p'' = (natVal (Proxy ∷ Proxy p)) ∷ Integer
      let q'' = (natVal (Proxy ∷ Proxy q)) 
      let d = p'' + q''
      let maxLength = (2^d - 1) ∷ Integer
      scale ← arbitrary
      listSize ← choose (0, maxLength)
      indices ← vectorOf (NPN.fromIntegral listSize) (resize (NPN.fromIntegral d-1) arbitrary )
      return (Blade scale indices) 
                
\end{code}
\bibliographystyle{IEEEtran}
\bibliography{biblio.bib}
\end{document}

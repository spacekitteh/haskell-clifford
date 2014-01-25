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
\end{code}
Clifford algebras are a module over a ring. They also support all the usual transcendental functions.
\begin{code}
module Clifford  where

import NumericPrelude
import Algebra.Laws
import Algebra.Additive
import Algebra.Ring
import Algebra.OccasionallyScalar
import Algebra.Transcendental
import Algebra.ZeroTestable
import Algebra.Module

import System.IO
import Data.List

import qualified Test.QuickCheck as QC


\end{code}


The first problem: How to represent basis vectors. One way to do it is via generalised Pauli matrices. Another way is to use lists, which we will do because this is Haskell. >:0

\texttt{bScale} is the amplitude of the blade. \texttt{bIndices} are the indices for the basis. 
\begin{code}
data Blade f = Blade {bScale :: f, bIndices :: [Int]}
\end{code}

For example, a scalar would be constructed like so: \texttt{Blade Double 1}
\begin{code}
scalar d = Blade d []
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

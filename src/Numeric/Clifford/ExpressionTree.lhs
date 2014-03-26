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

Expression tree!

\begin{code}
{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RankNTypes, ScopedTypeVariables, DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs#-}
{-# LANGUAGE FlexibleInstances, StandaloneDeriving, KindSignatures, DataKinds #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}
\end{code}


\begin{code}
module Numeric.Clifford.ExpressionTree where

import Numeric.Clifford.Multivector
import Numeric.Clifford.LinearOperators

data Expr p q t where
    Const :: Multivector p q t → Expr p q t
    Sum :: [Expr p q t] → Expr p q t
    Product :: [Expr p q t] → Expr p q t
    Apply :: Function p q t → Expr p q t → Expr p q t
    Undefined :: Expr p q t
    Symbol :: Symbol → Expr p q t
    Differential :: Symbol → Expr p q t → Expr p q t
    Root :: Integer → Expr p q t → Expr p q t
    Power :: Expr p q t → Expr p q t → Expr p q t

data Function p q t = Id
                    | Sqrt

\end{code}
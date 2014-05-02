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
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, InstanceSigs#-}
{-# LANGUAGE FlexibleInstances, StandaloneDeriving, KindSignatures, DataKinds, PolyKinds #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, DeriveFunctor, DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, DeriveFoldable #-}
{-# OPTIONS_HADDOCK show-extensions #-}
\end{code}


\begin{code}
module Numeric.Clifford.ExpressionTree where
import NumericPrelude 
import GHC.TypeLits 
import Data.Typeable
import Data.Data
import Data.Foldable
import Data.Traversable
import Data.Monoid.Unicode
import Control.Applicative
import Data.Eq.Unicode
import Data.Bool.Unicode 
data Symbolic = MakeSymbol {_unicodeName ∷ String, _texName ∷ String} deriving (Show, Eq, Typeable, Data )

data SafeList (χ∷Nat) a where
         Empty ∷ SafeList 0 a
         Cons ∷ a → SafeList l a → SafeList (l+1) a 

deriving instance Show a ⇒ Show (SafeList χ a)

instance Eq (SafeList 0 a) where
         (==) a b = True
instance (Eq a, 1 <= χ, γ ~ χ)   ⇒ Eq (SafeList χ a) where
       (==) ∷ SafeList χ a → SafeList γ a → Bool
       (==) (Cons x xs)  (Cons y ys) = (x ≡ y) ∧ xs ≡ ys

instance Foldable (SafeList χ) where
         foldMap f Empty = (∅)
         foldMap f (x `Cons` xs) = (f x) ⊕ foldMap f xs
instance Functor (SafeList χ) where
         fmap f Empty = Empty
         fmap f (x `Cons` xs) = (f x) `Cons` (fmap f xs)
--instance Traversable (SafeList χ) where
--         traverse f list = Data.Foldable.foldr cons_f (pure Empty) list where
--                  cons_f x ys = Cons <$> f x <*> ys

data ExprTuple (χ∷Nat) = MkExprTuple (SafeList χ Expr) deriving (Show )
data SymbolTuple (χ∷Nat) = MkSymbolTuple (SafeList χ Symbolic) deriving (Show )

data Expr where
    Const :: Symbolic → Expr 
    Sum :: [Expr] → Expr 
    Product :: [Expr] → Expr
    Tuple ∷ ∀ (χ∷Nat) . ExprTuple χ → Expr
    Undefined :: Expr 
    Monomial ∷ {_coefficient ∷ Expr, _in ∷ Expr, _power ∷ Expr} → Expr
    Apply :: Operator χ → ExprTuple χ → Expr
    Power :: Expr → Expr → Expr 

deriving instance Show (Expr)
instance Eq (Expr) where
         (==) a b = False


data Operator (χ∷Nat)  where
     ArbitraryFunction ∷ Function χ→ Operator χ
     Derivative ∷  Symbolic → Operator 1
     Integral ∷ Symbolic → Operator 1
     BinaryOperator ∷ Function 2 → Operator 2

deriving instance Show (Operator χ)
deriving instance Eq (Operator χ)

data Function (χ∷Nat) where
    Function ∷ {_boundVariables ∷ SymbolTuple χ, _expr ∷ Expr } → Function χ

deriving instance Show (Function χ)
deriving instance Eq (Function χ)


\end{code}
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
{-# LANGUAGE NoMonomorphismRestriction, UnicodeSyntax, GADTs, InstanceSigs, AllowAmbiguousTypes#-}
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
import Data.Functor.Foldable hiding (Cons)
import Data.Type.Equality


data Symbolic = MakeSymbol {_unicodeName ∷ String, _texName ∷ String} deriving ( Eq, Typeable, Data )

instance Show (Symbolic) where
         show = _unicodeName
{-data SafeList (χ∷Nat) a where
          Empty ∷ SafeList 0 a
          Cons ∷ a → SafeList l a → SafeList (l+1) a 
h ∷ (χ == 0) ~ False ⇒ SafeList χ a → a
h (Cons x _) = x
t ∷ (χ == 0) ~ False ⇒ SafeList χ a → SafeList (χ-1) a
t (Cons _ xs) = xs
deriving instance Show a ⇒ Show (SafeList χ a)

instance Eq (SafeList 0 a) where
         (==) a b = True
instance (Eq a, 1 <= χ, ( (l+1) == (χ)) ~ True )   ⇒ Eq (SafeList χ a) where
       (==) ∷ SafeList χ a → SafeList χ a → Bool
       (==) a b {-(Cons x (xs∷SafeList l a))  (Cons y (ys ∷ SafeList l a))-} = (x ≡ y) ∧ xs ≡ ys where
            x = h a
            y = h b
            xs = t a
            ys = t b


--instance Data.Foldable.Foldable (SafeList 0) where
--         foldMap f Empty = (∅)

--instance (1 <= χ) ⇒ Data.Foldable.Foldable (SafeList χ) where
--         foldMap f (x `Cons` xs) = (f x) ⊕ foldMap f xs
--instance Functor (SafeList χ) where
--         fmap f Empty = Empty
--         fmap f (x `Cons` xs) = (f x) `Cons` (fmap f xs)
--instance Traversable (SafeList χ) where
--         traverse f list = Data.Foldable.foldr cons_f (pure Empty) list where
--                  cons_f x ys = Cons <$> f x <*> ys
--
-}

data ExprF a self where
    Const :: Symbolic → ExprF a self
    Sum :: [self] → ExprF a self
    Product :: [self] → ExprF a self
    Tuple ∷ [self] → ExprF a self
    Undefined :: ExprF a self
    Polynomial ∷ self → [PowerSeriesCoefficient a] → ExprF a self
    Apply ∷ Operator → [self] → ExprF a self
    Power :: self → self → ExprF a self
    
data PowerSeriesCoefficient a  = PowerSeriesCoefficient {_coefficient ∷ TExpr a, _power ∷ TExpr a} deriving (Eq, Show)
deriving instance Show self ⇒ Show (ExprF a self)
deriving instance Eq self ⇒ Eq (ExprF a self)
deriving instance Functor (ExprF a)
deriving instance Data.Foldable.Foldable (ExprF a)
deriving instance Traversable (ExprF a)

type TExpr a = Fix (ExprF a)
type Expr = TExpr ()


data Operator  where
     ArbitraryFunction ∷ Function → Operator 
     Derivative ∷  Symbolic → Operator 
     Integral ∷ Symbolic → Operator 
     BinaryOperator ∷ Function  → Operator 

deriving instance Show (Operator)
deriving instance Eq (Operator)

data Function where
    Function ∷ {_boundVariables ∷ [Symbolic], _expr ∷ Expr } → Function 

deriving instance Show (Function )
deriving instance Eq (Function )



\end{code}
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
import Algebra.Ring
import Algebra.Additive
import GHC.TypeLits 
import Data.Typeable
import Data.Data
import Data.Foldable
import Data.Traversable
import Data.Monoid.Unicode
--import Control.Applicative
import Data.Eq.Unicode
import Data.Bool.Unicode 
import Data.Maybe
import Data.Functor.Foldable 
import Data.Type.Equality
import qualified Data.Map
import Data.List.Stream

data Symbolic = MakeSymbol {_unicodeName ∷ String, _texName ∷ String} deriving ( Eq, Typeable, Data, Ord ) 

instance Show (Symbolic) where
         show = _unicodeName


eval ∷ Algebra.Ring.C a ⇒  Env a → TExpr anno → a
eval env = cata (evalAlg env) 

type Env a = Data.Map.Map Symbolic a
evalAlg ∷ Algebra.Ring.C a ⇒ Env a → ExprF anno a → a
evalAlg env = eval' where
 eval' (Const var) = fromJust $ Data.Map.lookup var env
 eval' (Sum xs) = Data.List.Stream.foldr1 (+)  xs
 eval' (Product xs) =  Data.List.Stream.foldr1 (*) xs
 eval' (UnaryOperator op val) = evalUnary op val
 eval' (Add a b) = a + b
 eval' (Subtract a b) = a - b

evalUnary ∷ Algebra.Ring.C a ⇒ UnaryOperator → a → a
evalUnary Negate val = negate val

simplify ∷ TExpr anno → TExpr anno
simplify = cata alg where
  alg (Add a b) = simplifyAdd a b
  alg a = Fix a
  simplifyAdd (Fix (Sum xs)) s = Fix (Sum (s:xs))
  simplifyAdd s (Fix (Sum xs)) = Fix (Sum (s:xs))
  simplifyAdd a (Fix (Add b c)) = Fix (Sum [a,b,c])
  simplifyAdd (Fix (Add a b)) c = Fix (Sum [a,b,c])
  simplifyAdd a b = Fix (Add a b)

data ExprF a self where
     Const :: Symbolic → ExprF a self
     Zero ∷ ExprF a self
     Add :: self → self → ExprF a self
     Subtract ∷ self → self→ ExprF a self
     Sum :: [self] → ExprF a self
     Product :: [self] → ExprF a self
     Tuple ∷ [self] → ExprF a self
--    Undefined :: ExprF a self
     Polynomial ∷ self → [PowerSeriesCoefficient a] → ExprF a self
     Apply ∷ Operator → [self] → ExprF a self
     Power :: self → self → ExprF a self
     Psuedoscalar ∷ ExprF a self
     Exp ∷ self → ExprF a self
     Cos ∷ self → ExprF a self
     UnaryOperator ∷ UnaryOperator → self → ExprF a self
     BinaryOperator ∷ BinaryOperator → self → self → ExprF a self

makeSymbol unicode tex = Fix (Const (MakeSymbol unicode tex))
instance Algebra.Additive.C (TExpr a) where
        a + b = Fix $ Add a b
        zero = Fix Zero
        negate a = Fix $ UnaryOperator Negate a
        a - b = Fix $ Subtract a b
data UnaryOperator = Negate deriving (Eq, Show)

data BinaryOperator = Dot
                      | Wedge
                      | Cross deriving (Eq,Show)
data PowerSeriesCoefficient a  = PowerSeriesCoefficient {_coefficient ∷ TExpr a, _power ∷ TExpr a} deriving (Eq, Show)
deriving instance Show self ⇒ Show (ExprF a self)
deriving instance Eq self ⇒ Eq (ExprF a self)
deriving instance Functor (ExprF a)
deriving instance Data.Foldable.Foldable (ExprF a)
deriving instance Traversable (ExprF a)




type TExpr a = Fix (ExprF a)
type Expr = TExpr ()


data Operator  where
--     ArbitraryFunction ∷ Function → Operator 
     Derivative ∷  Symbolic → Operator 
     Integral ∷ Symbolic → Operator 

deriving instance Show (Operator)
deriving instance Eq (Operator)

--data Function where
    --Function ∷ {_boundVariables ∷ [Symbolic], _expr ∷ Expr } → Function 

--deriving instance Show (Function )
--deriving instance Eq (Function )



\end{code}
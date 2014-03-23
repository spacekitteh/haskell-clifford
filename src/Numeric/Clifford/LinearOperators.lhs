\begin{code}
{-# LANGUAGE NoImplicitPrelude, RankNTypes, KindSignatures, DataKinds, GADTs #-}
module Numeric.Clifford.LinearOperators where
import NumericPrelude
import Numeric.Clifford.Multivector
import Algebra.Algebraic
import Algebra.Field
import Algebra.Transcendental
import GHC.TypeLits
import Data.Monoid
import Control.Applicative
import Control.Monad
\end{code}
What is a linear operator? Just a Vector -> Vector!

\begin{code}

-- linear operators appear to satisfy monad laws. possible design: use accumulate operator elements, simplify them down to a single operator, and then apply that to a multivector
data LinearOperator (p::Nat) (q::Nat) f where
    LinearOperator :: forall (p::Nat) (q::Nat) f . (Algebra.Field.C f, Ord f, SingI p, SingI q) => {_operator :: Multivector p q f -> Multivector p q f} -> LinearOperator p q f
type LinearOperatorCreator p q f = (Algebra.Algebraic.C f, Ord f, SingI p, SingI q) => Multivector p q f -> LinearOperator p q f

instance Functor (LinearOperator p q) where
    fmap func (LinearOperator a) = LinearOperator (func a)
instance Applicative (LinearOperator p q) where
    pure a = LinearOperator a
    (<*>) = ap
instance (Algebra.Field.C f, Ord f, SingI p, SingI q) => Monoid (LinearOperator p q f) where
    mempty = LinearOperator NumericPrelude.id
    mappend a b = a . b


instance forall (p::Nat) (q::Nat). Monad (LinearOperator p q) where
    return a =LinearOperator a
    (>>=) a action = action (_operator a)
reflect u x = (-u)*x*recip u

makeReflectionOperator ::LinearOperatorCreator p q f
makeReflectionOperator u = LinearOperator (reflect u)

rotate spinor x = (reverseMultivector spinor) * x * spinor
rotatePlaneAngle plane angle = rotate (exp (((fst.normalised) plane) * (angle/2)))

makeRotationOperator :: LinearOperatorCreator p q f
makeRotationOperator u = LinearOperator (rotate u)

project u x = inverse u * (u `dot` x)

makeProjectionOperator :: LinearOperatorCreator p q f
makeProjectionOperator u = LinearOperator (project u)

\end{code}
\begin{code}
{-# LANGUAGE NoImplicitPrelude, RankNTypes, KindSignatures, DataKinds, GADTs, FlexibleInstances, UndecidableInstances, InstanceSigs #-}
module Numeric.Clifford.LinearOperators where
import qualified NumericPrelude as NP ((.), id)
import NumericPrelude hiding ((.), id)
import Numeric.Clifford.Multivector
import Algebra.Algebraic
import Algebra.Field
import Algebra.Transcendental
import GHC.TypeLits
import Data.Monoid
import Control.Applicative
import Control.Category
import Control.Arrow
import Control.Monad
import qualified Control.Lens
import Control.Lens.Operators
import Data.Semigroupoid
import qualified Numeric.Clifford.Blade
\end{code}
What is a linear operator? Just a Vector -> Vector!

\begin{code}

-- linear operators appear to satisfy monad laws. possible design: use accumulate operator elements, simplify them down to a single operator, and then apply that to a multivector
data LinearOperator' p q f g where
    LinearOperator' :: {_operator' :: Multivector p q f -> Multivector p q g} -> LinearOperator' p q f g
    LinearOperator :: {_operator :: Multivector p q f -> Multivector p q f} -> LinearOperator' p q f f
type LinearOperator p q f = LinearOperator' p q f f
type LinearOperatorCreator p q f = (Algebra.Algebraic.C f, Ord f, SingI p, SingI q) => Multivector p q f -> LinearOperator p q f

instance Category (LinearOperator' p q) where
    id = LinearOperator' NP.id
    (.) (LinearOperator' a) (LinearOperator' b)  = LinearOperator' (a NP.. b)


{-instance Arrow (LinearOperator p q) where
--   arr :: forall b c. {-(Algebra.Field.C c, Ord c) =>-}  (b -> c) -> LinearOperator p q b c
   arr func = undefined
       --applyToScales z@(BladeSum indices) = BladeSum $ map (\blade@(Blade _ _) -> 
       --applyToScales z@(BladeSum indices) = BladeSum $ map (\z@(Numeric.Clifford.Blade.Blade scale x) -> Numeric.Clifford.Blade.Blade (func scale) x ) indices
   first = undefined
-}
instance (Algebra.Field.C f, Ord f,Algebra.Field.C g, Ord g, SingI p, SingI q, f~g) => Monoid (LinearOperator' p q f g) where
    mempty = id
    mappend = (.)




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
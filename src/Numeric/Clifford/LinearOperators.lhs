\begin{code}
{-# LANGUAGE NoImplicitPrelude, RankNTypes, KindSignatures, DataKinds, GADTs, FlexibleInstances, UndecidableInstances, InstanceSigs, MultiParamTypeClasses, PolyKinds, ConstraintKinds, UnicodeSyntax #-}
{-# OPTIONS_HADDOCK show-extensions #-}
module Numeric.Clifford.LinearOperators where
import qualified NumericPrelude as NP ((.), id)
import NumericPrelude hiding ((.), id, (!!), zipWith, map, length)
import Numeric.Clifford.Multivector
import Algebra.Algebraic
import Algebra.Field
import Algebra.Ring
import Algebra.Transcendental
import GHC.TypeLits
import Data.Monoid
import Control.Applicative
import Control.Category
import Control.Arrow
import Control.Monad
import Data.List.Stream
import qualified Control.Lens
import Control.Lens.Operators
import Data.Semigroupoid
import Numeric.Natural
import Data.Word
import Numeric.Clifford.Internal
import qualified Numeric.Clifford.Blade
\end{code}
What is a linear operator? Just a Vector -> Vector!

\begin{code}

-- linear operators appear to satisfy monad laws. possible design: use accumulate operator elements, simplify them down to a single operator, and then apply that to a multivector
data LinearOperator' p q f g where
    LinearOperator' :: {_operator' :: Multivector p q f -> Multivector p q g} -> LinearOperator' p q f g
    LinearOperator :: {_operator :: Multivector p q f -> Multivector p q f} -> LinearOperator' p q f f

getFuncFromOperator :: LinearOperator' p q f g → (Multivector p q f → Multivector p q g)
getFuncFromOperator (LinearOperator' op) = op
getFuncFromOperator (LinearOperator op) = op

type LinearOperator p q f = LinearOperator' p q f f
type LinearOperatorCreator p q f = (Algebra.Algebraic.C f, Ord f, SingI p, SingI q) => Multivector p q f -> LinearOperator p q f

instance Category (LinearOperator' p q) where
    id = LinearOperator' NP.id
    (.) (LinearOperator' a) (LinearOperator' b)  = LinearOperator' (a NP.. b)

 
instance (Algebra.Field.C f, Ord f,Algebra.Field.C g, Ord g, SingI p, SingI q, f~g) => Monoid (LinearOperator' p q f g) where
    mempty = id
    mappend = (.)



{-
--GHC 7.8: The Control.Category module now has the PolyKinds extension enabled, meaning that instances of Category no longer need be of kind * -> * -> *.
class Operator (p::Nat) (q::Nat) f g where
    apply :: Operator p q f g ->  Multivector p q f -> Multivector p q g

instance forall (p::Nat) (q::Nat) . Category (Operator p q) where
    id = NP.id
    (.) a b = a (NP..) b
-}  

{-
[[f11, f12, f13],
 [f21, f22, f21],
 [f31, f32, f33]]
-}

getMatrixElementsFromOperator :: LinearOperator' p q f' f'-> [[f']]
getMatrixElementsFromOperator operator = error "Not implemented yet!" where
    f = getFuncFromOperator operator
    
   

createFunctionalFromElements :: ∀  (p::Nat) (q::Nat) f . (Algebra.Field.C f, Ord f, SingI p, SingI q) => [[f]] ->(Multivector p q f -> Multivector p q f)
createFunctionalFromElements elements = (\x -> f*x) where
    d = (length elements) - 1
    f = sumList $ map elementsForK [0..d]
    column k = let transposed = transpose elements in transposed !! k   
    elementsForK k =sumList $   zipWith (scaleRight) basisVectors (column k) 
    
createLinearOperatorFromElements :: forall (p::Nat) (q::Nat) f . (Algebra.Field.C f, Ord f, SingI p, SingI q) => [[f]] -> LinearOperator p q f
createLinearOperatorFromElements  = LinearOperator .  createFunctionalFromElements


reflect u x = (-u)*x*recip u

makeReflectionOperator ::LinearOperatorCreator p q f
makeReflectionOperator u = LinearOperator (reflect u)

rotate spinor x = (reverseMultivector spinor) * x * spinor
rotatePlaneAngle plane angle = rotate (exp (((fst.normalised) plane) * (angle/2)))

makeRotationOperator :: LinearOperatorCreator p q f
makeRotationOperator u = LinearOperator (rotate u)
makeRotationOperatorFromPlaneAngle plane angle = LinearOperator (rotatePlaneAngle plane angle)


project u x = inverse u * (u `dot` x)
makeProjectionOperator :: LinearOperatorCreator p q f
makeProjectionOperator u = LinearOperator (project u)

\end{code}
{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
module Numeric.Clifford.NumericIntegration.DefaultIntegrators where
import           Algebra.Absolute
import           Algebra.Additive                    hiding (elementAdd,
                                                      elementSub)
import           Algebra.Algebraic
import           Algebra.Field
import           Algebra.Module
import           Algebra.Ring
import           Algebra.ToInteger
import           Algebra.ToRational
import           Control.Exception                   (assert)
import           Control.Lens                        hiding (indices)
import           Data.DeriveTH
import           Data.List.Stream
import           Data.Maybe
import           Data.Monoid
import qualified Data.Vector                         as V
import           Debug.Trace
import           GHC.TypeLits
import           Math.Sequence.Converge              (convergeBy)
import           Number.Ratio                        hiding (scale)
import           Numeric.Clifford.Multivector        as MV
import           Numeric.Clifford.NumericIntegration
import           Numeric.Natural
import           NumericPrelude                      hiding (any, concat,
                                                      concatMap, drop, elem,
                                                      filter, foldl, foldl1,
                                                      foldr, head, iterate,
                                                      length, map, null, repeat,
                                                      replicate, replicate,
                                                      reverse, scanl, tail, zip,
                                                      zipWith, (!!), (++))
import           NumericPrelude.Numeric              (sum)
import qualified NumericPrelude.Numeric              as NPN
import           Test.QuickCheck
--trace _ a = a

--rk4ClassicalTableau :: ButcherTableau NPN.Double
rk4ClassicalTableau = ButcherTableau [[0,0,0,0],[0.5,0,0,0],[0,0.5,0,0],[0,0,1,0]] [1.0 NPN./6,1.0 NPN./3, 1.0 NPN./3, 1.0 NPN./6] [0, 0.5, 0.5, 1]
implicitEulerTableau = ButcherTableau [[1.0::NPN.Double]] [1] [1]



gaussLegendreFourthOrderTableau = ButcherTableau [[0.25::NPN.Double, 0.25 - ((sqrt 3.0) NPN./6.0)],[0.25 + ((sqrt 3.0) NPN./ 6.0) , 0.25]] [0.5, 0.5] [0.5 - ((sqrt 3.0) NPN./6.0), 0.5 + ((sqrt 3.0) NPN./ 6.0)]
gaussLegendreFourthOrder h f (t, state) = impl h f id id (t,state) where
    impl= genericRKMethod gaussLegendreFourthOrderTableau [ConvergenceTolerance 1.0e-9]


rk4ClassicalFromTableau h f (t,state) = impl h f id id (t, state) where
    impl = genericRKMethod rk4ClassicalTableau []
implicitEulerMethod h f (t, state) = impl h f id id (t, state) where
    impl = genericRKMethod implicitEulerTableau [ConvergenceTolerance 1.0e-8]

lobattoIIIASecondOrderTableau = ButcherTableau [[0,0],[0.5::NPN.Double,0.5]] [0.5,0.5] [0,1]
lobattoIIIASecondOrder h f (t, state) = impl h f id id  (t, state) where
    impl = genericRKMethod lobattoIIIASecondOrderTableau []

lobattoIIIAFourthOrderWithTol h f (t, state) = impl h f id id (t, state) where
    impl = genericRKMethod lobattoIIIAFourthOrderTableau [ConvergenceTolerance 1.0e-8]
lobattoIIIAFourthOrderTableau = ButcherTableau [[0,0,0],[((5 NPN./24)::NPN.Double),1 NPN./3,-1 NPN./24],[1 NPN./6,2 NPN./3,1 NPN./6]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIAFourthOrder h f (t, state) = impl h f id id (t, state) where
    impl = genericRKMethod lobattoIIIAFourthOrderTableau []

lobattoIIIBFourthOrderTableau = ButcherTableau [[1 NPN./6,(-1) NPN./6,0],[((1 NPN./6)::NPN.Double),1 NPN./3,0],[1 NPN./6,5 NPN./6, 0]] [1 NPN./6,2 NPN./3,1 NPN./6] [0,0.5,1]
lobattoIIIBFourthOrder h f (t, state) = impl h f id id (t, state) where
    impl = genericRKMethod lobattoIIIBFourthOrderTableau []

rk4Classical :: (Ord a, Algebra.Algebraic.C a, SingI p, SingI q) =>  stateType -> a -> (stateType->stateType) -> ([Multivector p q a] -> stateType) -> (stateType -> [Multivector p q a]) -> stateType
rk4Classical state h f project unproject = project newState where
    update = map (\(k1', k2', k3', k4') -> sumList [k1',2*k2',2*k3',k4'] `divideRight`  Algebra.Ring.fromInteger 6) $ zip4 k1 k2 k3 k4
    newState = zipWith (+) state' update
    state' = unproject state
    evalDerivatives x = unproject $ f $ project x
    k1 = map (h*>) $ evalDerivatives state'
    k2 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (`divideRight` two) k1)
    k3 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' (map (`divideRight` two) k2)
    k4 = map (h*>) $ evalDerivatives . map (uncurry (+)) $ zip state' k3

rk4ClassicalList  h f state = rk4Classical  h f id id state

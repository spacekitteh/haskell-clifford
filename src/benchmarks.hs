{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE DataKinds #-}

import           Numeric.Clifford.Multivector
import Numeric.Clifford.NumericIntegration.DefaultIntegrators
import           Criterion.Main
import           Data.List.Stream
import           NumericPrelude   hiding (iterate, last, map, take, log)
import           Prelude          hiding (iterate, last, map, negate, take,log, (*),
                                   (+))
                                   
type STVector = Multivector 3 1 Double
scalar2 = scalar (2.0::NumericPrelude.Double) :: STVector
ij2 = (2.0::NumericPrelude.Double) `e` [1,2] :: STVector 
ik3 = (3::NumericPrelude.Double) `e` [1,3] :: STVector 
ijk4 = (4::NumericPrelude.Double) `e` [1,2,3] :: STVector 
ijl5 = (5::NumericPrelude.Double) `e` [1,2,4] :: STVector
a = ij2 + ik3 + ijk4 + ijl5 + (scalar 1.5)
enormousThing = a*a*a*a*a*a*a + scalar2
expDecay _ x =  map negate $ map ((*) (1.3 `e` [] :: STVector))  x
thelambda init = lobattoIIIAFourthOrder 0.01 expDecay init
main = defaultMain [
	bgroup "log" [ bench "scalar 2.0" $ nf (log) scalar2
			, bench "2ij" $ nf (log) ij2
			, bench "3ik" $ nf (log) ik3
			, bench "4ijk" $ nf (log) ijk4
			, bench "5ijl" $ nf (log) ijl5
			, bench "sum" $ nf (log) a
			, bench "enormous thing" $ nf (log) enormousThing
		     ],
        bgroup "lobatto IIIA 4th order RK solver"
		    [
		 bench "200 iterations exponential decay" $ nf (\x -> last $ take 200 (iterate thelambda x)) (0.0,[scalar 1.0])
		    ]
		   ]

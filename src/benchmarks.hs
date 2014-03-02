{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -optlc-O=3 -O3 #-}

import Prelude hiding ((+), (*),negate,iterate,last,take,map)
import Clifford
import Criterion.Main
import NumericPrelude hiding (iterate,last,map,take)
import Data.List.Stream
scalar2 = scalar (2.0::NumericPrelude.Double)
ij2 = (2.0::NumericPrelude.Double) `e` [1,2]
ik3 = (3::NumericPrelude.Double) `e` [1,3]
ijk4 = (4::NumericPrelude.Double) `e` [1,2,3]
ijl5 = (5::NumericPrelude.Double) `e` [1,2,4]
a = ij2 + ik3 + ijk4 + ijl5 + (scalar 1.5)
enormousThing = a*a*a*a*a*a*a + scalar2
expDecay _ x =  map negate $ map ((*) (1.3 `e` []))  x
thelambda init = lobattoIIIAFourthOrder init 0.01 expDecay
main = defaultMain [
	bgroup "log" [ bench "scalar 2.0" $ nf Clifford.log scalar2
			, bench "2ij" $ nf Clifford.log ij2
			, bench "3ik" $ nf Clifford.log ik3
			, bench "4ijk" $ nf Clifford.log ijk4
			, bench "5ijl" $ nf Clifford.log ijl5
			, bench "sum" $ nf Clifford.log a
			, bench "enormous thing" $ nf Clifford.log enormousThing
		     ],
        bgroup "lobatto IIIA 4th order RK solver" 
		    [
		 bench "200 iterations exponential decay" $ nf (\x -> last $ take 200 (iterate thelambda x)) (0.0,[scalar 1.0])
		    ]
		   ]

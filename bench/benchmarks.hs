{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -optlc-O=3 -O3 #-}

import           Numeric.Clifford.Multivector
import Numeric.Clifford.NumericIntegration.DefaultIntegrators
import           Criterion.Main
import Algebra.Transcendental
import Algebra.Algebraic
import           Data.List.Stream
import           NumericPrelude   hiding (iterate, last, map, take, log)
import           Prelude          hiding (iterate, last, map, negate, take,log, (*),
                                   (+), (-), (/))
import Numeric.Compensated
import MathObj.Wrapper.Haskell98
import Control.DeepSeq 

comp a = Cons (compensated a 0)
scalar2 = scalar (comp 2.0) :: STVectorComp
ij2 = (comp 2.0) `e` [1,2] :: STVectorComp
ik3 = (comp 3.0) `e` [1,3] :: STVectorComp
ijk4 = (comp 4.0) `e` [1,2,3] :: STVectorComp 
ijl5 = (comp 5.0) `e` [1,2,4] :: STVectorComp
a = ij2 + ik3 + ijk4 + ijl5 + (scalar 1.5)
enormousThing = a*a*a*a*a*a*a + scalar2
expDecay _ x =  map negate $ map ((*) (1.3 `e` [] :: STVectorComp))  x
thelambda init = lobattoIIIAFourthOrderComp (comp 0.01)  expDecay init


main = defaultMain [
	bgroup "log" [ bench "scalar 2.0" $ nf log scalar2
			, bench "2ij" $ nf log ij2
			, bench "3ik" $ nf log ik3
			, bench "4ijk" $ nf log ijk4
			, bench "5ijl" $ nf log ijl5
			, bench "sum" $ nf log a
			, bench "enormous thing" $ nf log enormousThing
		     ],
        bgroup "lobatto IIIA 4th order RK solver"
		    [
		 bench "200 iterations exponential decay" $ nf (\x -> last $ take 200 (iterate thelambda x)) (0.0,[scalar 1.0])
		    ]
		   ]

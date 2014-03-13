module Clifford.Demo.ExponentialDecay where
import Clifford
import Debug.Trace
import qualified NumericPrelude.Numeric as NPN
import Algebra.Module
expDecay _ x = map negate $ map ((*) (1.0 `e` []))  x --Debug.Trace.trace ("Input of expdecay is " ++ show x) x
decay = map (\(t, x) -> (t,magnitude $ head x))  $  iterate (\init -> lobattoIIIAFourthOrder init 0.01 expDecay) (0.0::NPN.Double,[scalar (1.0::NPN.Double)])
decayTol = map (\(t, x) -> (t,magnitude $ head x))  $  iterate (\init -> lobattoIIIAFourthOrderWithTol init 0.01 expDecay) (0.0::NPN.Double,[scalar (1.0::NPN.Double)])

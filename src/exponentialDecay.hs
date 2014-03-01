module Clifford.Demo.ExponentialDecay where
import Clifford
import Debug.Trace
import qualified NumericPrelude.Numeric as NPN
expDecay _ x = map negate $ Debug.Trace.trace ("Input of expdecay is " ++ show x) x
decay = map magnitude $ map head $ iterate (\init -> lobattoIIIASecondOrder (0::NPN.Double) init 0.001 expDecay) [scalar (1.0::NPN.Double)]

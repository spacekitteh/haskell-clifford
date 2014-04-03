{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, DataKinds, FlexibleInstances #-}
import NumericPrelude (Double, fst, snd, ($), (.), seq, id, show )
import Prelude (getLine, putStrLn)
import Algebra.Transcendental
import Data.List.Stream
import Numeric.Clifford.Multivector
import Algebra.Ring 
import Algebra.Additive 
import Algebra.Field
import Numeric.Clifford.NumericIntegration.DefaultIntegrators
import Numeric.Clifford.Blade

import Control.Lens
import Graphics.Rendering.Chart
import Data.Colour
import Data.Colour.Names
import Data.Default.Class
import Graphics.Rendering.Chart.Backend.Cairo
import Numeric.Compensated
import Control.DeepSeq
import MathObj.Wrapper.Haskell98
import Debug.Trace
comp a = Cons (fadd a 0.0 compensated)

m = scalar 1 :: E3VectorComp
l = scalar 2 :: E3VectorComp
g = scalar 9.801 :: E3VectorComp
showOutput name x = Debug.Trace.trace ("output of " ++ name ++" is " ++ show x) x
pendulum t [p,theta] =   [ (-m*g*l)* sin theta, p / (m*l*l)] 

integrator = gaussLegendreFourthOrderComp (comp 0.1)  pendulum 
hamiltonian [ p', theta'] = extract $ magnitude $ (p*p/ (2*m*l*l)) - m*g*l* cos theta where
              p = scalar $ comp p'
              theta = scalar $ comp theta'


--pendulum _ [theta,thetadot] = [one,(-g/l) * sin theta]
tenSeconds =   take 5001 $ Debug.Trace.trace ("Value of m is " ++ show m) iterate integrator (0,[zero::E3VectorComp,showOutput "theta initial" $ scalar $ comp (0.3)]) --[zero::E3Vector,one/10]) 

extract  = uncompensated . decons
plottableFormat :: [(Double,Double,Double)]
plottableFormat = map ((\ (t, ([BladeSum [Blade a []],BladeSum [Blade b []]])) -> (extract t,extract a,extract b) ) ) tenSeconds

chart = toRenderable layout
  where
    momentum = plot_lines_values .~ [ ( map (\(t,p,_) -> (t,p)) plottableFormat )]
                     $ plot_lines_style  . line_color .~ opaque blue
                     $ plot_lines_title .~ "momentum"
                     $ def

    angle = plot_lines_style . line_color .~ (opaque red)
                  $ plot_lines_values .~ [ ( map (\(t,_,theta) -> (t,theta)) plottableFormat )]
                  $ plot_lines_title .~ "angle"
                  $ def
    energy = plot_lines_values .~ [ ( map (\(t,p,theta) -> (t,hamiltonian [p,theta])) plottableFormat )]
                          $ plot_lines_style  . line_color .~ opaque pink
                          $ plot_lines_title .~ "energy"
                          $ def
    layout = layout_title .~ "Pendulum"
           $ layout_plots .~ [toPlot momentum,
                              toPlot angle,
                              toPlot energy]
           $ def

main = renderableToFile def  chart "pendulum.png"


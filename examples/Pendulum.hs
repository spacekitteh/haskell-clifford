{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, DataKinds #-}
import NumericPrelude (Double, fst, snd, ($), (.), seq, id)
import Prelude (getLine, putStrLn)
import Algebra.Transcendental
import Data.List.Stream
import Numeric.Clifford.Multivector
import Algebra.Ring 
import Algebra.Additive 
import Algebra.Field
import Numeric.Clifford.NumericIntegration
import Numeric.Clifford.NumericIntegration.DefaultIntegrators
import Numeric.Clifford.Blade

import Control.Lens
import Graphics.Rendering.Chart
import Data.Colour
import Data.Colour.Names
import Data.Default.Class
import Graphics.Rendering.Chart.Backend.Cairo

m = scalar 1 :: E3Vector
l = scalar 20 :: E3Vector
g = scalar 9.801 :: E3Vector

pendulum _ [p,theta] = [ (-m*g*l)* sin  theta, p / (m*l*l)] 

integrator = gaussLegendreFourthOrder 0.01 pendulum 
hamiltonian [ p', theta'] = magnitude $ (p*p/ (2*m*l*l)) - m*g*l*cos theta where
              p = scalar p'
              theta = scalar theta'


--pendulum _ [theta,thetadot] = [one,(-g/l) * sin theta]
tenSeconds =   take 50001 $ iterate integrator (0,[one::E3Vector,one]) --[zero::E3Vector,one/10]) 

plottableFormat = map ((\ (t, ([BladeSum [Blade a []],BladeSum [Blade b []]])) -> (t,a,b) ) ) tenSeconds

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


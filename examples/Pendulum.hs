{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, DataKinds #-}
import NumericPrelude (Double, fst, snd, ($), (.), seq)
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

m = scalar 3 :: E3Vector
l = scalar 20 :: E3Vector
g = scalar 9.81 :: E3Vector

hamil _ [p,theta] = [ (-m*g*l)* {-sin-}  theta, p / (m*l*l)] 

integrator = gaussLegendreFourthOrder 0.1 hamil --gaussLegendreFourthOrder 0.1 hamil


tenSeconds =   take 5001 $ iterate integrator (0,[one::E3Vector,one]) --[zero::E3Vector,one/10]) 

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

    layout = layout_title .~ "Pendulum"
           $ layout_plots .~ [toPlot momentum,
                              toPlot angle]
           $ def

main = renderableToFile def  chart "pendulum.png"


{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction, DataKinds, FlexibleInstances #-}
import NumericPrelude (Double, fst, snd, ($), (.), seq, id, show)
import Prelude (getLine, putStrLn)
import Algebra.Transcendental
import Data.List.Stream
import Numeric.Clifford.Multivector
import Algebra.Ring 
import Algebra.Additive 
import Algebra.Field
import Numeric.Clifford.NumericIntegration.DefaultIntegrators
import Numeric.Clifford.Blade
import Control.Monad
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
import Data.String
import System.Remote.Monitoring

comp a = Cons (fadd a 0.0 compensated)
--comp = id

m = scalar 1 :: E3VectorComp
l = scalar 2 :: E3VectorComp
g = scalar 9.801 :: E3VectorComp
ml = m*l
mgl = -g*ml
mll = ml*l
pendulum t [p,theta] =   [ mgl* sin theta, p / mll] 

integrator = gaussLegendreFourthOrderComp (comp 0.01)  pendulum 
hamiltonian [ p', theta'] = extract $ magnitude $ (p*p/ (2*mll)) + mgl* cos theta where
              p = scalar $ comp p'
              theta = scalar $ comp theta'


initialConditions = (0,[zero::E3VectorComp, scalar $ comp (0.3)])

history =   take 20001 $  iterate integrator initialConditions 

extract  = uncompensated . decons
--extract = id
plottableFormat :: [(Double,Double,Double)]
plottableFormat = map ((\ (t, ([BladeSum [Blade a []],BladeSum [Blade b []]])) -> (extract t,extract a,extract b) ) ) history

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

main = do 
--    forkServer ( fromString "localhost") 8000
    renderableToFile def  chart "pendulum.png"

\begin{code}

module Numeric.Clifford.BladeSpec (main, spec) where

import Test.Hspec
import Test.QuickCheck
import Numeric.Clifford.Blade
import Algebra.Ring
main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  let a = Blade 1.0 [0] :: Blade 3 1 Double
  let b =  Blade 2.0 [1] :: Blade 3 1 Double
  let ab =  Blade 2.0 [0,1] :: Blade 3 1 Double
  let c =  Blade 3.0 [1,2] :: Blade 3 1 Double
  let d =  Blade 4.0 [2] :: Blade 3 1 Double
  let e = Blade 2.0 [0] :: Blade 3 1 Double
  let f = Blade 3.0 [0] :: Blade 3 1 Double
  --todo: Memoise the blade index sorting function.
  describe "bladeMul" $ do
         it "multiplies an n-blade with an m-blade to give an n+m blade if each index is unique" $ do
                          (a `bladeMul` b) `shouldBe` ab
         it "should handle duplicate blades which square to +1 due to metric signature" $ do
                          c `bladeMul` d `shouldBe` Blade 12.0 [1]
         it "should handle diplicate blades which square to -1 due to metric signature" $ do
                          e `bladeMul` f `shouldBe` Blade (-6.0) []
         context "leaves blades unchanged when multiplied by a scalar of 1" $  do
             it "on the left" $  property $
                \x -> (Blade one []) `bladeMul` x == (x::Blade 3 1 Double)
             it "on the right" $ property $ 
                \x -> x `bladeMul` (Blade one []) == (x::Blade 3 1 Double)                       

\end{code}
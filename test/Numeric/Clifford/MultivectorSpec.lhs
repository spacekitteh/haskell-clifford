\begin{code}

module Numeric.Clifford.MultivectorSpec (main, spec) where
import Prelude hiding ((^), (*))
import Test.Hspec
import Test.QuickCheck
import Numeric.Clifford.Multivector
import Algebra.Ring
import Numeric.Natural
import Algebra.Additive (zero)
import Control.Exception (evaluate)
main :: IO ()
main = hspec spec

type STVector = Multivector 3 1 Double
spec :: Spec
spec = do
  let i = 1.0 `e` [1,2] :: STVector
  describe "multiplication" $ do
         it "should square unit bivectors to -1" $ do
           i*i `shouldBe` scalar (-1.0)
  describe "root n" $ do
         it "cannot compute the 0th root" $ do
            evaluate (root 0 i) `shouldThrow` anyErrorCall
         it "cannot compute a root of 0" $ do
            evaluate (root 1 (zero::STVector)) `shouldThrow` anyErrorCall
         it "computes the nth root of a vector" $ verbose prop where
            prop x k= (magnitude (abs ((rooted ^ n) - x))) <= 0.000001 || x == zero || n == zero  where
                 n :: Integer
                 n = (fromIntegral (k::Natural)) `mod` 6
                 rooted :: STVector
                 rooted = root n x


\end{code}
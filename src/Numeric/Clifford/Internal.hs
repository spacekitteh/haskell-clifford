{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -O3 -optlc-O=3 -Wall #-}
{-# LANGUAGE TypeOperators, TypeFamilies,CPP, ConstraintKinds, RankNTypes, DataKinds #-}
module Numeric.Clifford.Internal (myTrace, trie, untrie, enumerate, dimension, DefaultField, AllowableCliffordType) where
import Numeric.Natural
import Prelude hiding (head,tail, null)
import Data.MemoTrie
import Data.List.Stream
import Control.Arrow
import Data.Bits
import Test.QuickCheck
import Data.Word
import GHC.TypeLits
import Algebra.Field
import qualified Debug.Trace as DebugTrace
#ifdef DEBUG
myTrace = DebugTrace.trace
#else
myTrace _ x = x
#endif


type AllowableCliffordType p q f = forall (p::Nat) (q::Nat) f. (Ord f, Algebra.Field.C f, SingI p, SingI q)
type DefaultField = Double

instance HasTrie Natural where
    newtype Natural :->: a = NaturalTrie ((Bool,[Bool]) :->: a)
    trie f = NaturalTrie (trie (f . unbitsZ)) 
    untrie (NaturalTrie t) = untrie t . bitsZ
    enumerate (NaturalTrie t) = enum' unbitsZ t

dimension :: Natural -> Natural -> Natural
dimension p q = pred $ p + q

instance Arbitrary Natural where
    arbitrary = sized $ \n ->
                let n' = abs n in
                 fmap (toNatural . (\x -> (fromIntegral x)::Word)) (choose (0, n'))
    shrink = shrinkIntegral



unbitsZ :: (Prelude.Num n, Bits n) => (Bool,[Bool]) -> n
unbitsZ (headder,bs) =  (unbits  (headder:bs))

bitsZ :: (Prelude.Num n, Ord n, Bits n) => n -> (Bool,[Bool])
bitsZ i = (h, t ) where 
     theBits = bits i
     (h,t) = if null theBits
                then (False,[])
                else (head theBits, tail theBits)
bits :: (Prelude.Num t, Bits t) => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)
unbits :: (Prelude.Num t, Bits t) => [Bool] -> t
unbits [] = 0
unbits (x:xs) = unbit x .|. shiftL (unbits xs) 1
unbit :: Prelude.Num t => Bool -> t
unbit False = 0
unbit True  = 1
enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
enum' f = (fmap.first) f . enumerate

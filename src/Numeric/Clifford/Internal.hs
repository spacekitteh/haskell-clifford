{-# OPTIONS_GHC -fllvm -fexcess-precision -optlo-O3 -O3 -optlc-O=3 -Wall #-}
{-# LANGUAGE TypeOperators, TypeFamilies, CPP #-}
module Numeric.Clifford.Internal (myTrace, trie, untrie, enumerate) where
import Numeric.Natural
import Data.MemoTrie
import Data.List.Stream
import Control.Arrow
import Data.Bits
import qualified Debug.Trace as DebugTrace
#ifdef DEBUG
myTrace = DebugTrace.trace
#else
myTrace _ x = x
#endif
instance HasTrie Natural where
    newtype Natural :->: a = NaturalTrie ((Bool,[Bool]) :->: a)
    trie f = NaturalTrie (trie (f . unbitsZ))
    untrie (NaturalTrie t) = untrie t . bitsZ
    enumerate (NaturalTrie t) = enum' unbitsZ t


unbitsZ :: (Prelude.Num n, Bits n) => (Bool,[Bool]) -> n
unbitsZ (positive,bs) = sig (unbits bs)
 where
   sig | positive  = id
       | otherwise = Prelude.negate

bitsZ :: (Prelude.Num n, Ord n, Bits n) => n -> (Bool,[Bool])
bitsZ = (>= 0) &&& (bits . Prelude.abs)
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

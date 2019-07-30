module Cryptol.Eval.Concrete.Integer where

import Data.Bits

import Cryptol.TypeCheck.Solver.InfNat (genLog)
import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad

intModExp :: Integer -> Integer -> Integer -> Eval Integer
intModExp modulus base e
  | modulus > 0  = ready $ doubleAndAdd base e modulus
  | modulus == 0 = integerExp base e
  | otherwise    = evalPanic "intModExp" [ "negative modulus: " ++ show modulus ]

integerExp :: Integer -> Integer -> Eval Integer
integerExp x y
  | y < 0     = negativeExponent
  | otherwise = ready $ x ^ y

integerLg2 :: Integer -> Eval Integer
integerLg2 x
  | x < 0     = logNegative
  | otherwise = ready $ lg2 x

integerNeg :: Integer -> Eval Integer
integerNeg x = ready $ negate x

intModNeg :: Integer -> Integer -> Eval Integer
intModNeg modulus x = ready $ negate x `mod` modulus

doubleAndAdd :: Integer -- ^ base
             -> Integer -- ^ exponent mask
             -> Integer -- ^ modulus
             -> Integer
doubleAndAdd base0 expMask modulus = go 1 base0 expMask
  where
  go acc base k
    | k > 0     = acc' `seq` base' `seq` go acc' base' (k `shiftR` 1)
    | otherwise = acc
    where
    acc' | k `testBit` 0 = acc `modMul` base
         | otherwise     = acc

    base' = base `modMul` base

    modMul x y = (x * y) `mod` modulus

mask :: Integer  -- ^ Bit-width
     -> Integer  -- ^ Value
     -> Integer  -- ^ Masked result
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)



liftBinInteger :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Eval Integer
liftBinInteger op x y = ready $ op x y

liftBinIntMod ::
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> Eval Integer
liftBinIntMod op m x y
  | m == 0    = ready $ op x y
  | otherwise = ready $ (op x y) `mod` m

liftDivInteger :: (Integer -> Integer -> Integer) ->
                  Integer -> Integer -> Eval Integer
liftDivInteger _  _ 0 = divideByZero
liftDivInteger op x y = ready $ op x y

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0









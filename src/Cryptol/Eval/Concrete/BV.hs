{-# Language DeriveGeneric, DeriveAnyClass #-}
module Cryptol.Eval.Concrete.BV where

import GHC.Generics (Generic)
import Control.DeepSeq(NFData)
import Data.Bits
import Numeric (showIntAtBase)

import Cryptol.Eval.PP
import Cryptol.Utils.PP
import Cryptol.Eval.Monad
import Cryptol.Eval.Concrete.Integer

-- | Concrete bitvector values: width, value
-- Invariant: The value must be within the range 0 .. 2^width-1
data BV = BV !Integer !Integer deriving (Generic, NFData)

instance Show BV where
  show = show . bvVal

-- | Apply an integer function to the values of bitvectors.
--   This function assumes both bitvectors are the same width.
binBV :: (Integer -> Integer -> Integer) -> BV -> BV -> BV
binBV f (BV w x) (BV _ y) = mkBv w (f x y)

-- | Apply an integer function to the values of a bitvector.
--   This function assumes the function will not require masking.
unaryBV :: (Integer -> Integer) -> BV -> BV
unaryBV f (BV w x) = mkBv w $ f x

bvVal :: BV -> Integer
bvVal (BV _w x) = x

bvWidth :: BV -> Integer
bvWidth (BV w _) = w

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer {-^ width -} -> Integer {-^ value -} -> BV
mkBv w i = BV w (mask w i)

ppBV :: PPOpts -> BV -> Doc
ppBV opts (BV width i)
  | base > 36 = integer i -- not sure how to rule this out
  | asciiMode opts width = text (show (toEnum (fromInteger i) :: Char))
  | otherwise = prefix <.> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <.> padding 1
    8  -> text "0o" <.> padding 3
    10 -> empty
    16 -> text "0x" <.> padding 4
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"


liftSigned :: (Integer -> Integer -> Integer -> Eval BV) ->
              Integer -> BV -> BV -> Eval BV
liftSigned _  0    = \_ _ -> return $ mkBv 0 0
liftSigned op size = f
 where
 f (BV i x) (BV j y)
   | i == j && size == i = op size sx sy
   | otherwise = evalPanic "liftSigned" ["Attempt to compute with words of different sizes"]
   where sx = signedValue i x
         sy = signedValue j y

signedBV :: BV -> Integer
signedBV (BV i x) = signedValue i x

bvSdiv :: Integer -> Integer -> Integer -> Eval BV
bvSdiv  _ _ 0 = divideByZero
bvSdiv sz x y = return $! mkBv sz (x `quot` y)

bvSrem :: Integer -> Integer -> Integer -> Eval BV
bvSrem  _ _ 0 = divideByZero
bvSrem sz x y = return $! mkBv sz (x `rem` y)

modExp :: Integer -- ^ bit size of the resulting word
       -> BV      -- ^ base
       -> BV      -- ^ exponent
       -> Eval BV
modExp bits (BV _ base) (BV _ e)
  | bits == 0            = ready $ BV bits 0
  | base < 0 || bits < 0 = evalPanic "modExp"
                             [ "bad args: "
                             , "  base = " ++ show base
                             , "  e    = " ++ show e
                             , "  bits = " ++ show modulus
                             ]
  | otherwise            = ready $ mkBv bits $ doubleAndAdd base e modulus
  where
  modulus = 0 `setBit` fromInteger bits

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   However, if the bitvector size is 0, always return the 0
--   bitvector.
liftBinArith :: (Integer -> Integer -> Integer) ->
                Integer -> BV -> BV -> Eval BV
liftBinArith _  0 _        _        = ready $ mkBv 0 0
liftBinArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   Generate a thunk that throws a divide by 0 error when forced if the second
--   argument is 0.  However, if the bitvector size is 0, always return the 0
--   bitvector.
liftDivArith :: (Integer -> Integer -> Integer) ->
                Integer -> BV -> BV -> Eval BV
liftDivArith _  0 _        _        = ready $ mkBv 0 0
liftDivArith _  _ _        (BV _ 0) = divideByZero
liftDivArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y


liftUnaryArith :: (Integer -> Integer) ->
                  Integer -> BV -> Eval BV
liftUnaryArith op w (BV _ x) = ready $ mkBv w $ op x

signedValue :: Integer -> Integer -> Integer
signedValue i x
  | testBit x (fromIntegral (i-1)) = x - (1 `shiftL` (fromIntegral i))
  | otherwise                      = x



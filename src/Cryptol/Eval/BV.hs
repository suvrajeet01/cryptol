{-# Language DeriveGeneric, DeriveAnyClass #-}
module Cryptol.Eval.BV where

import GHC.Generics (Generic)
import Control.DeepSeq(NFData)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad(wordTooWide)
import Data.Bits((.&.), shiftL)

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

mask :: Integer  -- ^ Bit-width
     -> Integer  -- ^ Value
     -> Integer  -- ^ Masked result
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)



-- | Concrete evaluation of floating point numbers[
module Cryptol.Eval.Float where

import Data.Word
import LibBF
import Data.Bits(shiftL,shiftR,setBit)
import Data.Int(Int64)

import Control.DeepSeq
import Control.Exception(throw)

import Cryptol.Eval.BV
import Cryptol.Eval.Monad
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)


-- | A floating point value annotated with its precision parameters.
data FV = FV { fvPrecBits :: !Word64      -- ^ precision bits
             , fvExpBits  :: !Word64      -- ^ exponent bits
             , fvValue    :: !BigFloat
             }

instance Show FV where
  show fv = bfToString 16 fmt (fvValue fv)
    where fmt = addPrefix <> showFreeMin (Just (fvPrecBits fv))

instance NFData FV where
  rnf x = x `seq` ()


supportedFloat :: Integer -> Integer -> Bool
supportedFloat mBits eBits =
  eBits >= fromIntegral expBitsMin &&
  eBits <= fromIntegral expBitsMax &&
  mBits >= fromIntegral precMin &&
  mBits <= fromIntegral precMax


ppFV :: Int {-^base-} -> FV -> Doc
ppFV b fv = text (bfToString b fmt (fvValue fv))
  where
  fmt = addPrefix <> showFreeMin (Just (fvPrecBits fv))

fp :: Bool -> BV -> BV -> Eval FV
fp sig mBits eBits
  | mv == 0 && ev == 0  = fv (if sig then bfNegZero else bfPosZero)
  | mv == 0 && isMaxExp = fv (if sig then bfNegInf else bfPosInf)
  | isMaxExp            = fv bfNaN
  | otherwise           = fv (if sig then bfNeg num else num)
  where
  m         = bvWidth mBits
  n         = bvWidth eBits

  mv        = bvVal mBits
  ev        = bvVal eBits :: Integer
  isMaxExp  = ev == allOnes
  allOnes   = (1 `shiftL` fromIntegral n) - 1
  bias      = allOnes `shiftR` 1

  realExp   = fromIntegral (ev - bias - m)
  integ     = if ev == 0 then mv else (mv `setBit` fromIntegral m)
  (num,Ok)  = bfMul2Exp infPrec (bfFromInteger integ) realExp

  fv x | supportedFloat m n = pure $! FV { fvPrecBits = fromIntegral (m+1)
                                         , fvExpBits  = fromIntegral n
                                         , fvValue    = x
                                         }
       | otherwise = unsupportedFloat m n


fpZero :: Integer -> Integer -> FV
fpZero m n
  | supportedFloat m n = FV { fvPrecBits = fromIntegral m
                            , fvExpBits  = fromIntegral n
                            , fvValue    = bfPosZero
                            }
  | otherwise = throw (UnsupportedFloat m n)


liftPred1 :: (BigFloat -> Bool) -> FV -> Eval Bool
liftPred1 p x = pure $! p (fvValue x)

fpIsZero :: FV -> Eval Bool
fpIsZero = liftPred1 bfIsZero

fpIsNaN :: FV -> Eval Bool
fpIsNaN = liftPred1 bfIsNaN

fpIsInf :: FV -> Eval Bool
fpIsInf = liftPred1 $ \x -> not (bfIsFinite x) && not (bfIsNaN x)

fpIsNegative :: FV -> Eval Bool
fpIsNegative = liftPred1 $ \x -> bfSign x == Just Neg

fpIsPositive :: FV -> Eval Bool
fpIsPositive = liftPred1 $ \x -> bfSign x == Just Pos

fpIsNormal :: FV -> Eval Bool
fpIsNormal fv = liftPred1 (\x ->
  case bfExponent x of
    Just e -> e >= minExp fv
    _ -> False
  ) fv

fpIsSubNormal :: FV -> Eval Bool
fpIsSubNormal fv = liftPred1 (\x ->
  case bfExponent x of
    Just e -> e < minExp fv
    _ -> False
  ) fv

minExp :: FV -> Int64
minExp fv = 2 - (1 `shiftL` fromIntegral (fvExpBits fv - 1))

rndMode :: BV -> RoundMode
rndMode v = case bvVal v of
              0 -> NearEven
              1 -> NearAway
              2 -> ToPosInf
              3 -> ToNegInf
              4 -> ToZero
              x -> panic "rndMode" ["Unknown rounding mode", show x]




liftBin :: (BFOpts -> BigFloat -> BigFloat -> (BigFloat,Status)) ->
           BV -> FV -> FV -> Eval FV
liftBin f r x y = pure $! x { fvValue = res }
  where
  opts = rnd (rndMode r) <> precBits (fromIntegral (fvPrecBits x))
                         <> expBits  (fromIntegral (fvExpBits x))
  (res,_stat) = f opts (fvValue x) (fvValue y)


fpAdd :: BV -> FV -> FV -> Eval FV
fpAdd = liftBin bfAdd

fpSub :: BV -> FV -> FV -> Eval FV
fpSub = liftBin bfSub

fpMul :: BV -> FV -> FV -> Eval FV
fpMul = liftBin bfMul

fpDiv :: BV -> FV -> FV -> Eval FV
fpDiv = liftBin bfDiv



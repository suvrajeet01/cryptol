-- | Concrete evaluation of floating point numbers[
module Cryptol.Eval.Float where

import Data.Word
import LibBF
import Data.Bits(shiftL,shiftR,setBit)
import Data.Int(Int64)

import Control.DeepSeq
import Control.Exception(throw)
import Control.Monad(unless)

import Cryptol.Eval.BV
import Cryptol.Eval.Monad
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)


-- | A floating point value annotated with its precision parameters.
data FV = FV { fvExpBits  :: !Word64      -- ^ exponent bits
             , fvPrecBits :: !Word64      -- ^ precision bits
             , fvValue    :: !BigFloat
             }

instance Show FV where
  show fv = bfToString 16 fmt (fvValue fv)
    where fmt = addPrefix <> showFreeMin (Just (fvPrecBits fv))

instance NFData FV where
  rnf x = x `seq` ()


supportedFloat :: Integer -> Integer -> Bool
supportedFloat eBits mBits =
  eBits >= fromIntegral expBitsMin &&
  eBits <= fromIntegral expBitsMax &&
  mBits >= fromIntegral precMin &&
  mBits <= fromIntegral precMax


ppFV :: Int {-^base-} -> FV -> Doc
ppFV b fv = text (bfToString b fmt (fvValue fv))
  where
  fmt = addPrefix <> showFreeMin (Just (fvPrecBits fv))

fp :: Bool -> BV -> BV -> Eval FV
fp sig inExp inMant
  | expoBiased == 0 && mantVal == 0 = fv (if sig then bfNegZero else bfPosZero)
  | isMaxExp        && mantVal == 0 = fv (if sig then bfNegInf else bfPosInf)
  | isMaxExp                        = fv bfNaN
  | otherwise                       = fv (if sig then bfNeg num else num)
  where
  iExpoBits   = bvWidth inExp
  iPrecBits   = bvWidth inMant  -- one less than actual precision

  mantVal     = bvVal inMant
  expoBiased  = bvVal inExp

  isMaxExp    = expoBiased == allOnes
  allOnes     = (1 `shiftL` fromIntegral iExpoBits) - 1
  bias        = allOnes `shiftR` 1

  expoVal     = fromIntegral (expoBiased - bias - iPrecBits)
  mant        | expoBiased == 0 = mantVal
              | otherwise       = mantVal `setBit` fromIntegral iPrecBits
  (num,Ok)    = bfMul2Exp infPrec (bfFromInteger mant) expoVal


  iPrec       = iPrecBits + 1

  fv x        = pure $! fpVal x iExpoBits iPrec


fpVal :: BigFloat -> Integer -> Integer -> FV
fpVal x e p
  | supportedFloat e p = FV { fvPrecBits = fromIntegral p
                            , fvExpBits  = fromIntegral e
                            , fvValue    = x
                            }
  | otherwise = throw (FloatError (UnsupportedFloat e p))


fpNaN :: Integer -> Integer -> FV
fpNaN = fpVal bfNaN

fpPosInf :: Integer -> Integer -> FV
fpPosInf = fpVal bfPosInf


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

rndMode :: BV -> Eval RoundMode
rndMode v = case bvVal v of
              0 -> pure NearEven
              1 -> pure NearAway
              2 -> pure ToPosInf
              3 -> pure ToNegInf
              4 -> pure ToZero
              x -> floatError (UnsupportedRoundingMode x)

{-# INLINE rndToBV #-}
rndToBV :: RoundMode -> BV
rndToBV r = BV 3 $ case r of
                     NearEven -> 0
                     NearAway -> 1
                     ToPosInf -> 2
                     ToNegInf -> 3
                     ToZero   -> 4
                     _        -> panic "rndToBV"
                                  [ "Unexpeced rouding mode: " ++ show r ]



liftBin :: (BFOpts -> BigFloat -> BigFloat -> (BigFloat,Status)) ->
           BV -> FV -> FV -> Eval FV
liftBin f r x y =
  do rm <- rndMode r
     let opts = rnd rm <> precBits (fromIntegral (fvPrecBits x))
                       <> expBits  (fromIntegral (fvExpBits x))
         (res,_stat) = f opts (fvValue x) (fvValue y)
     pure $! x { fvValue = res }

fpAdd :: BV -> FV -> FV -> Eval FV
fpAdd = liftBin bfAdd

fpSub :: BV -> FV -> FV -> Eval FV
fpSub = liftBin bfSub

fpMul :: BV -> FV -> FV -> Eval FV
fpMul = liftBin bfMul

fpDiv :: BV -> FV -> FV -> Eval FV
fpDiv = liftBin bfDiv

fpMod :: BV -> FV -> FV -> Eval FV
fpMod = liftBin bfMod -- XXX: or fpRem??

fpExp :: BV -> FV -> FV -> Eval FV
fpExp = liftBin bfPow

--------------------------------------------------------------------------------
-- Class instances

-- class Zero
fpZero :: Integer -> Integer -> FV
fpZero = fpVal bfPosZero

fpBinInst :: (BV -> FV -> FV -> Eval FV) -> FV -> FV -> Eval FV
fpBinInst f x y =
  do opts <- getEvalOpts
     f (rndToBV (evalRound opts)) x y


--------------------------------------------------------------------------------
-- class Arith


fpArithAdd, fpArithSub, fpArithMul, fpArithDiv, fpArithMod, fpArithExp,
  fpArithSDiv, fpArithSMod
  :: FV -> FV -> Eval FV
fpArithAdd      = fpBinInst fpAdd
fpArithSub      = fpBinInst fpSub
fpArithMul      = fpBinInst fpMul
fpArithDiv      = fpBinInst fpDiv
fpArithMod      = fpBinInst fpMod
fpArithExp      = fpBinInst fpExp
fpArithSDiv _ _ = floatError (UnsupportedFloatOp "/$")
fpArithSMod _ _ = floatError (UnsupportedFloatOp "%$")

fpArithLg2, fpArithNegate :: FV -> Eval FV
fpArithLg2 _      = floatError (UnsupportedFloatOp "lg2")
fpArithNegate x   = pure $! x { fvValue = bfNeg (fvValue x) }

fpFromInteger :: Integer {-^ exp bits-} -> Integer {-^ prec bits -} ->
                 Integer -> Eval FV
fpFromInteger e p i =
  do r <- evalRound <$> getEvalOpts
     unless (supportedFloat e p) (floatError (UnsupportedFloat e p))
     let opts = expBits  (fromIntegral e) <>
                precBits (fromIntegral p) <>
                rnd r
     pure $! FV { fvValue = fst (bfRoundInt opts (bfFromInteger i))
                , fvExpBits = fromIntegral e
                , fvPrecBits = fromIntegral p
                }


-- | Compare two values.  If they are equal, then use the given continuation
-- to decide.  The continutaion is used to implement lexicographic ordering.
fpCmp :: FV -> FV -> Eval Ordering -> Eval Ordering
fpCmp x y k =
  case compare (fvValue x) (fvValue y) of
    EQ  -> k
    res -> pure res





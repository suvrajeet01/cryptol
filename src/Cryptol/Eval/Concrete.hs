{-# Language TypeFamilies, DataKinds, ViewPatterns, LambdaCase #-}
module Cryptol.Eval.Concrete where

import Data.Bits
import MonadLib
import Data.List(genericLength)
import qualified Data.Text as T
import qualified Data.Foldable as Fold
import qualified Data.Sequence as Seq


import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),genLog)
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(mkIdent)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.GenPrims
import Cryptol.Eval.Monad
import Cryptol.Eval.Concrete.BV
import Cryptol.Eval.Concrete.Float
import Cryptol.Eval.SeqMap
import Cryptol.Eval.Value
import Cryptol.Eval.PP
import Cryptol.Eval.Class.Cmp
import Cryptol.Eval.Type



data EvalConc

type Value = GenValue EvalConc

type instance VBool EvalConc    = Bool
type instance VInteger EvalConc = Integer
type instance VWord EvalConc    = BV
type instance VFloat EvalConc   = FV


instance BitWord EvalConc where
  wordLen (BV w _) = w
  wordAsChar (BV _ x) = Just $ integerToChar x

  wordBit (BV w x) idx = testBit x (fromInteger (w - 1 - idx))

  wordUpdate (BV w x) idx True  = BV w (setBit   x (fromInteger (w - 1 - idx)))
  wordUpdate (BV w x) idx False = BV w (clearBit x (fromInteger (w - 1 - idx)))

  ppBit b | b         = text "True"
          | otherwise = text "False"

  ppWord = ppBV

  ppInteger _opts i = integer i

  ppFloat opts i = ppFV (useBase opts) i
  floatZero e p = fpZero e p

  bitLit b = b
  wordLit = mkBv
  integerLit i = i

  packWord bits = BV (toInteger w) a
    where
      w = case length bits of
            len | toInteger len >= Arch.maxBigIntWidth -> wordTooWide (toInteger len)
                | otherwise                  -> len
      a = foldl setb 0 (zip [w - 1, w - 2 .. 0] bits)
      setb acc (n,b) | b         = setBit acc n
                     | otherwise = acc

  unpackWord (BV w a) = [ testBit a n | n <- [w' - 1, w' - 2 .. 0] ]
    where
      w' = fromInteger w

  joinWord (BV i x) (BV j y) =
    BV (i + j) (shiftL x (fromInteger j) + y)

  splitWord leftW rightW (BV _ x) =
     ( BV leftW (x `shiftR` (fromInteger rightW)), mkBv rightW x )

  extractWord n i (BV _ x) = mkBv n (x `shiftR` (fromInteger i))

  wordPlus (BV i x) (BV j y)
    | i == j = mkBv i (x+y)
    | otherwise = panic "Attempt to add words of different sizes: wordPlus" []

  wordMinus (BV i x) (BV j y)
    | i == j = mkBv i (x-y)
    | otherwise = panic "Attempt to subtract words of different sizes: wordMinus" []

  wordMult (BV i x) (BV j y)
    | i == j = mkBv i (x*y)
    | otherwise = panic "Attempt to multiply words of different sizes: wordMult" []

  intPlus  x y = x + y
  intMinus x y = x - y
  intMult  x y = x * y
  intMod   x y = mod x y

  intModPlus  m x y = (x + y) `mod` m
  intModMinus m x y = (x - y) `mod` m
  intModMult  m x y = (x * y) `mod` m

  wordToInt (BV _ x) = x
  wordFromInt w x = mkBv w x
  fpFromInteger' = fpFromInteger
  fpArithAdd'    = \_ _ -> fpArithAdd
  fpArithSub'    = \_ _ -> fpArithSub
  fpArithMul'    = \_ _ -> fpArithMul


-- | This is strict!
boolToWord :: [Bool] -> Value
boolToWord bs = VWord (genericLength bs) $ ready $ WordVal $ packWord bs



fromStr :: Value -> Eval String
fromStr (VSeq n vals) =
  traverse (\x -> toEnum . fromInteger <$> (fromWord "fromStr" =<< x)) (enumerateSeqMap n vals)
fromStr _ = evalPanic "fromStr" ["Not a finite sequence"]

-- | Turn a value into an integer represented by w bits.
fromWord :: String -> Value -> Eval Integer
fromWord msg val = bvVal <$> fromVWord msg val


--------------------------------------------------------------------------------
liftSigned :: (Integer -> Integer -> Integer -> Eval BV) -> Integer -> Fun 2 BV
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

signedValue :: Integer -> Integer -> Integer
signedValue i x = if testBit x (fromIntegral (i-1)) then x - (1 `shiftL` (fromIntegral i)) else x

bvSlt :: Integer -> Integer -> Integer -> Eval Value
bvSlt _sz x y = return . VBit $! (x < y)

bvSdiv :: Integer -> Integer -> Integer -> Eval BV
bvSdiv  _ _ 0 = divideByZero
bvSdiv sz x y = return $! mkBv sz (x `quot` y)

bvSrem :: Integer -> Integer -> Integer -> Eval BV
bvSrem  _ _ 0 = divideByZero
bvSrem sz x y = return $! mkBv sz (x `rem` y)

sshrV :: Value
sshrV =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam $ \(BV i x) -> return $
  wlam $ \y ->
   let signx = testBit x (fromIntegral (i-1))
       amt   = fromInteger (bvVal y)
       negv  = (((-1) `shiftL` amt) .|. x) `shiftR` amt
       posv  = x `shiftR` amt
    in return . VWord i . ready . WordVal . mkBv i $! if signx then negv else posv

-- | Signed carry bit.
scarryV :: Value
scarryV =
  nlam $ \_n ->
  wlam $ \(BV i x) -> return $
  wlam $ \(BV j y) ->
    if i == j
      then let z     = x + y
               xsign = testBit x (fromInteger i - 1)
               ysign = testBit y (fromInteger i - 1)
               zsign = testBit z (fromInteger i - 1)
               sc    = (xsign == ysign) && (xsign /= zsign)
            in return $ VBit sc
      else evalPanic "scarryV" ["Attempted to compute with words of different sizes"]

-- | Unsigned carry bit.
carryV :: Value
carryV =
  nlam $ \_n ->
  wlam $ \(BV i x) -> return $
  wlam $ \(BV j y) ->
    if i == j
      then return . VBit $! testBit (x + y) (fromInteger i)
      else evalPanic "carryV" ["Attempted to compute with words of different sizes"]




--------------------------------------------------------------------------------
-- Comparisons

signedLexCompare :: TValue -> Value -> Value -> Eval Ordering
signedLexCompare ty a b = cmpValue ops ty a b (return EQ)
  where
  ops = CmpPrims { cmpBool    =         nope "Bit"
                 , cmpWord    = \_   -> cmpBy signedBV
                 , cmpInteger =         nope "Integer"
                 , cmpZ       = \_   -> nope "Z"
                 , cmpFloat   = \_ _ -> nope "Float"
                 }

  nope x = \_ _ _ -> panic "signedLexCompare"
                      ["Attempted to perform signed comparisons on type " ++ x]


lexCompare :: TValue -> Value -> Value -> Eval Ordering
lexCompare ty a b = cmpValue ops ty a b (return EQ)
  where
  ops = CmpPrims { cmpBool    =         cmpBy id
                 , cmpWord    = \_ ->   cmpBy bvVal
                 , cmpInteger =         cmpBy id
                 , cmpZ       = \_   -> cmpBy id
                 , cmpFloat   = \_ _ -> fpCmp
                 }

-- | Process two elements based on their lexicographic ordering.
cmpOrder :: String -> (Ordering -> Bool) ->
            TValue -> Fun 2 (GenValue EvalConc)
cmpOrder _nm op ty l r = VBit . op <$> lexCompare ty l r

-- | Process two elements based on their lexicographic ordering, using signed comparisons
signedCmpOrder :: String -> (Ordering -> Bool) ->
                  TValue -> Fun 2 (GenValue EvalConc)
signedCmpOrder _nm op ty l r = VBit . op <$> signedLexCompare ty l r




--------------------------------------------------------------------------------
floatPrims :: [(String, GenValue EvalConc)]
floatPrims =
  [ ("fp"        , {-# SCC "Prelude::fp" #-}
                    nlam $ \ _e ->
                    nlam $ \ _p ->
                    lam  $ \ sign -> pure $
                    wlam $ \ expo -> pure $
                    wlam $ \ prec -> do ~(VBit s) <- sign
                                        VFloat <$> fp s expo prec)

  , ("fpNaN"        , {-# SCC "Prelude::fpNaN" #-}         mkK fpNaN)
  , ("fpPosInf"     , {-# SCC "Prelude::fpPosInf" #-}      mkK fpPosInf)

  , ("fpIsInf"      , {-# SCC "Prelude::fpIsInf" #-}       pred1 fpIsInf)
  , ("fpIsNaN"      , {-# SCC "Prelude::fpIsNaN" #-}       pred1 fpIsNaN)
  , ("fpIsZero"     , {-# SCC "Prelude::fpIsZero" #-}      pred1 fpIsZero)
  , ("fpIsNegative" , {-# SCC "Prelude::fpIsNegative" #-}  pred1 fpIsNegative)
  , ("fpIsPositive" , {-# SCC "Prelude::fpIsPositive" #-}  pred1 fpIsPositive)
  , ("fpIsNormal"   , {-# SCC "Prelude::fpIsNormal" #-}    pred1 fpIsNormal)
  , ("fpIsSubNormal", {-# SCC "Prelude::fpIsSubNormal" #-} pred1 fpIsSubNormal)

  , ("fpAdd",         {-# SCC "Prelude::fpAdd" #-} bin fpAdd)
  , ("fpSub",         {-# SCC "Prelude::fpSub" #-} bin fpSub)
  , ("fpMul",         {-# SCC "Prelude::fpMul" #-} bin fpMul)
  , ("fpDiv",         {-# SCC "Prelude::fpAdd" #-} bin fpDiv)
  ]

  where
  mkK f = nlam $ \e' -> nlam $ \p' ->
            case (e',p') of
              (Nat e, Nat p) -> VFloat (f e p)
              _ -> panic "mkK" [ "Unexpected `inf` in constant" ]

  pred1 p = nlam $ \_e ->
            nlam $ \_p ->
            lam  $ \fv -> do ~(VFloat v) <- fv
                             VBit <$> p v

  bin f   = nlam $ \_e ->
            nlam $ \_p ->
            wlam $ \r  -> pure $
             lam $ \x  -> pure $
             lam $ \y  -> do ~(VFloat a) <- x
                             ~(VFloat b) <- y
                             VFloat <$> f r a b



--------------------------------------------------------------------------------
-- | Create a packed word
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




-- Arith -----------------------------------------------------------------------

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   However, if the bitvector size is 0, always return the 0
--   bitvector.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith _  0 _        _        = ready $ mkBv 0 0
liftBinArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   Generate a thunk that throws a divide by 0 error when forced if the second
--   argument is 0.  However, if the bitvector size is 0, always return the 0
--   bitvector.
liftDivArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftDivArith _  0 _        _        = ready $ mkBv 0 0
liftDivArith _  _ _        (BV _ 0) = divideByZero
liftDivArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

type BinArith w = Integer -> w -> w -> Eval w

liftBinInteger :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Eval Integer
liftBinInteger op x y = ready $ op x y

liftBinIntMod ::
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> Eval Integer
liftBinIntMod op m x y
  | m == 0    = ready $ op x y
  | otherwise = ready $ (op x y) `mod` m

liftDivInteger :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Eval Integer
liftDivInteger _  _ 0 = divideByZero
liftDivInteger op x y = ready $ op x y

modWrap :: Integral a => a -> a -> Eval a
modWrap _ 0 = divideByZero
modWrap x y = return (x `mod` y)


type UnaryArith w = Integer -> w -> Eval w

liftUnaryArith :: (Integer -> Integer) -> UnaryArith BV
liftUnaryArith op w (BV _ x) = ready $ mkBv w $ op x

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0





--------------------------------------------------------------------------------
-- Sequences


type SeqValMap = SeqMapV EvalConc

updateFront
  :: Nat'
  -> TValue
  -> SeqMapV EvalConc
  -> WordValue EvalConc
  -> Eval (GenValue EvalConc)
  -> Eval (SeqMapV EvalConc)
updateFront len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs idx val

updateFront_word
 :: Nat'
 -> TValue
 -> WordValue EvalConc
 -> WordValue EvalConc
 -> Eval (GenValue EvalConc)
 -> Eval (WordValue EvalConc)
updateFront_word _len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  updateWordValue bs idx (fromBit =<< val)

updateBack
  :: Nat'
  -> TValue
  -> SeqMapV EvalConc
  -> WordValue EvalConc
  -> Eval (GenValue EvalConc)
  -> Eval (SeqMapV EvalConc)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word
 :: Nat'
 -> TValue
 -> WordValue EvalConc
 -> WordValue EvalConc
 -> Eval (GenValue EvalConc)
 -> Eval (WordValue EvalConc)
updateBack_word Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_word (Nat n) _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  updateWordValue bs (n - idx - 1) (fromBit =<< val)

indexFront :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexFront mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> lookupSeqMap vs ix

indexFront_bits :: Maybe Integer -> TValue -> SeqValMap -> Seq.Seq Bool -> Eval Value
indexFront_bits mblen a vs = indexFront mblen a vs . packWord . Fold.toList

indexBack :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexBack mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len > ix  -> lookupSeqMap vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

indexBack_bits :: Maybe Integer -> TValue -> SeqValMap -> Seq.Seq Bool -> Eval Value
indexBack_bits mblen a vs = indexBack mblen a vs . packWord . Fold.toList




logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool))
           -> (Nat' -> TValue -> SeqMapV EvalConc -> Integer -> SeqMapV EvalConc)
           -> Value
logicShift opW obB opS
  = nlam $ \ a ->
    nlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        BV _ i <- fromVWord "logicShift amount" =<< r
        l >>= \case
          VWord w wv -> return $ VWord w $ wv >>= \case
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))
                          BitsVal bs -> return $ BitsVal (obB w bs i)
                          LargeBitsVal n xs ->
                            return $ LargeBitsVal n $
                                     fmap fromVBit $
                                     opS (Nat n) c (fmap VBit xs) i

          _ -> mkSeq a c <$> (opS a c <$> (fromSeq "logicShift" =<< l) <*> return i)

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

shiftLB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
shiftLB w bs by =
  Seq.drop (fromInteger (min w by)) bs
  Seq.><
  Seq.replicate (fromInteger (min w by)) (ready False)

shiftLS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftLS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> return $ zeroV ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w i by
  | by >= w   = 0
  | otherwise = shiftR i (fromInteger by)

shiftRB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
shiftRB w bs by =
  Seq.replicate (fromInteger (min w by)) (ready False)
  Seq.><
  Seq.take (fromInteger (w - min w by)) bs

shiftRS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftRS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i >= by   -> lookupSeqMap vs (i-by)
      | i < len   -> return $ zeroV ety
      | otherwise -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf
      | i >= by   -> lookupSeqMap vs (i-by)
      | otherwise -> return $ zeroV ety


-- XXX integer doesn't implement rotateL, as there's no bit bound
rotateLW :: Integer -> Integer -> Integer -> Integer
rotateLW 0 i _  = i
rotateLW w i by = mask w $ (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateLB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
rotateLB w bs by =
  let (hd,tl) = Seq.splitAt (fromInteger (by `mod` w)) bs
   in tl Seq.>< hd

rotateLS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateLS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Integer -> Integer
rotateRW 0 i _  = i
rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateRB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
rotateRB w bs by =
  let (hd,tl) = Seq.splitAt (fromInteger (w - (by `mod` w))) bs
   in tl Seq.>< hd

rotateRS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateRS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]




-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: PrimMap -> Type -> Value -> Eval (Maybe Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (mkIdent (T.pack n))

  go :: Type -> Value -> ChoiceT Eval Expr
  go ty val = case (tNoUser ty, val) of
    (TRec tfs, VRecord vfs) -> do
      let fns = map fst vfs
      guard (map fst tfs == fns)
      fes <- zipWithM go (map snd tfs) =<< lift (traverse snd vfs)
      return $ ERec (zip fns fes)
    (TCon (TC (TCTuple tl)) ts, VTuple tvs) -> do
      guard (tl == (length tvs))
      ETuple `fmap` (zipWithM go ts =<< lift (sequence tvs))
    (TCon (TC TCBit) [], VBit True ) -> return (prim "True")
    (TCon (TC TCBit) [], VBit False) -> return (prim "False")
    (TCon (TC TCInteger) [], VInteger i) ->
      return $ ETApp (ETApp (prim "number") (tNum i)) ty
    (TCon (TC TCIntMod) [_n], VInteger i) ->
      return $ ETApp (ETApp (prim "number") (tNum i)) ty
    (TCon (TC TCSeq) [a,b], VSeq 0 _) -> do
      guard (a == tZero)
      return $ EList [] b
    (TCon (TC TCSeq) [a,b], VSeq n svs) -> do
      guard (a == tNum n)
      ses <- mapM (go b) =<< lift (sequence (enumerateSeqMap n svs))
      return $ EList ses b
    (TCon (TC TCSeq) [a,(TCon (TC TCBit) [])], VWord _ wval) -> do
      BV w v <- lift (asWordVal =<< wval)
      guard (a == tNum w)
      return $ ETApp (ETApp (prim "number") (tNum v)) ty
    (_, VStream _) -> fail "cannot construct infinite expressions"
    (_, VFun    _) -> fail "cannot convert function values to expressions"
    (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
    _ -> do doc <- lift (ppValue defaultPPOpts val)
            panic "Cryptol.Eval.Value.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
             ]



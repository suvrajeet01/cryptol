-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.Concrete
  ( module Cryptol.Eval.Concrete.Value
  , evalPrim
  , toExpr
  ) where

import Control.Monad (join, unless,guard,zipWithM)
import MonadLib( ChoiceT, findOne, lift )

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.Testing.Random (randomV)
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)

import qualified Data.Foldable as Fold
import qualified Data.Sequence as Seq
import Data.Bits (Bits(..))

import qualified Data.Map.Strict as Map
import qualified Data.Text as T


-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: PrimMap -> AST.Type -> Value -> Eval (Maybe AST.Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (mkIdent (T.pack n))

  go :: AST.Type -> Value -> ChoiceT Eval Expr
  go ty val = case (tNoUser ty, val) of
    (TRec tfs, VRecord vfs) -> do
      let fns = Map.keys vfs
      guard (map fst tfs == fns)
      fes <- zipWithM go (map snd tfs) =<< lift (sequence (Map.elems vfs))
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
      BV w v <- lift (asWordVal Concrete =<< wval)
      guard (a == tNum w)
      return $ ETApp (ETApp (prim "number") (tNum v)) ty
    (_, VStream _) -> fail "cannot construct infinite expressions"
    (_, VFun    _) -> fail "cannot convert function values to expressions"
    (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
    _ -> do doc <- lift (ppValue Concrete defaultPPOpts val)
            panic "Cryptol.Eval.Value.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
             ]


-- Primitives ------------------------------------------------------------------

evalPrim :: Ident -> Maybe Value
evalPrim prim = Map.lookup prim primTable

primTable :: Map.Map Ident Value
primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (arithBinary Concrete (liftBinArith (+)) (liftBinInteger (+))
                            (liftBinIntMod (+))))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (arithBinary Concrete (liftBinArith (-)) (liftBinInteger (-))
                            (liftBinIntMod (-))))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (arithBinary Concrete (liftBinArith (*)) (liftBinInteger (*))
                            (liftBinIntMod (*))))
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (arithBinary Concrete (liftDivArith div) (liftDivInteger div)
                            (const (liftDivInteger div))))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (arithBinary Concrete (liftDivArith mod) (liftDivInteger mod)
                            (const (liftDivInteger mod))))

  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    binary (arithBinary Concrete modExp integerExp intModExp))
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    unary  (arithUnary Concrete (liftUnaryArith lg2) integerLg2 (const integerLg2)))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary  (arithUnary Concrete (liftUnaryArith negate) integerNeg intModNeg))

  , ("<"          , {-# SCC "Prelude::(<)" #-}
                    binary (cmpOrder "<"  (\o -> o == LT           )))
  , (">"          , {-# SCC "Prelude::(>)" #-}
                    binary (cmpOrder ">"  (\o -> o == GT           )))
  , ("<="         , {-# SCC "Prelude::(<=)" #-}
                    binary (cmpOrder "<=" (\o -> o == LT || o == EQ)))
  , (">="         , {-# SCC "Prelude::(>=)" #-}
                    binary (cmpOrder ">=" (\o -> o == GT || o == EQ)))
  , ("=="         , {-# SCC "Prelude::(==)" #-}
                    binary (cmpOrder "==" (\o ->            o == EQ)))
  , ("!="         , {-# SCC "Prelude::(!=)" #-}
                    binary (cmpOrder "!=" (\o ->            o /= EQ)))
  , ("<$"         , {-# SCC "Prelude::(<$)" #-}
                    binary (signedCmpOrder "<$" (\o -> o == LT)))
  , ("/$"         , {-# SCC "Prelude::(/$)" #-}
                    binary (arithBinary Concrete (liftSigned bvSdiv) (liftDivInteger div)
                            (const (liftDivInteger div))))

  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    binary (arithBinary Concrete (liftSigned bvSrem) (liftDivInteger mod)
                            (const (liftDivInteger mod))))
  , (">>$"        , {-# SCC "Prelude::(>>$)" #-}
                    sshrV)
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (logicBinary Concrete (\x y -> pure $ x .&. y) (binBV (.&.))))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (logicBinary Concrete (\x y -> pure $ x .|. y) (binBV (.|.))))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (logicBinary Concrete (\x y -> pure $ xor x y) (binBV xor)))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (logicUnary complement (unaryBV complement)))

  , ("toInteger"  , ecToIntegerV Concrete)
  , ("fromInteger", ecFromIntegerV Concrete (flip mod))
  , ("fromZ"      , {-# SCC "Prelude::fromZ" #-}
                    nlam $ \ _modulus ->
                    lam  $ \ x -> x)

  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("carry"      , {-# SCC "Prelude::carry" #-}
                    carryV)
  , ("scarry"     , {-# SCC "Prelude::scarry" #-}
                    scarryV)
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV Concrete)

  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> join (ccatV Concrete front back elty <$> l <*> r))


  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim Concrete indexFront_bits indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim Concrete indexBack_bits indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim updateBack_word updateBack)

  , ("zero"       , {-# SCC "Prelude::zero" #-}
                    VPoly (zeroV Concrete))

  , ("join"       , {-# SCC "Prelude::join" #-}
                    nlam $ \ parts ->
                    nlam $ \ (finNat' -> each)  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                      joinV Concrete parts each a =<< x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    ecSplitV Concrete)

  , ("splitAt"    , {-# SCC "Prelude::splitAt" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                       splitAtV Concrete front back a =<< x)

  , ("fromTo"     , {-# SCC "Prelude::fromTo" #-}
                    fromToV Concrete)
  , ("fromThenTo" , {-# SCC "Prelude::fromThenTo" #-}
                    fromThenToV Concrete)
  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV Concrete)
  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV Concrete)

  , ("error"      , {-# SCC "Prelude::error" #-}
                      tlam $ \a ->
                      nlam $ \_ ->
                       lam $ \s -> errorV a =<< (fromStr =<< s))

  , ("reverse"    , {-# SCC "Prelude::reverse" #-}
                    nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV Concrete =<< xs)

  , ("transpose"  , {-# SCC "Prelude::transpose" #-}
                    nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV Concrete a b c =<< xs)

  , ("random"      , {-# SCC "Prelude::random" #-}
                     tlam $ \a ->
                     wlam Concrete $ \(bvVal -> x) -> randomV Concrete a x)
  , ("trace"       , {-# SCC "Prelude::trace" #-}
                     nlam $ \_n ->
                     tlam $ \_a ->
                     tlam $ \_b ->
                      lam $ \s -> return $
                      lam $ \x -> return $
                      lam $ \y -> do
                         msg <- fromStr =<< s
                         EvalOpts { evalPPOpts, evalLogger } <- getEvalOpts
                         doc <- ppValue Concrete evalPPOpts =<< x
                         yv <- y
                         io $ logPrint evalLogger
                             $ if null msg then doc else text msg <+> doc
                         return yv)
  ]


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


-- | This is strict!
--boolToWord :: [Bool] -> Value
--boolToWord bs = VWord (genericLength bs) (WordVal <$> io (packWord () bs))

-- | Turn a value into an integer represented by w bits.
fromWord :: String -> Value -> Eval Integer
fromWord msg val = bvVal <$> fromVWord Concrete msg val

fromStr :: Value -> Eval String
fromStr (VSeq n vals) =
  traverse (\x -> toEnum . fromInteger <$> (fromWord "fromStr" =<< x)) (enumerateSeqMap n vals)
fromStr _ = evalPanic "fromStr" ["Not a finite sequence"]

lexCompare :: TValue -> Value -> Value -> Eval Ordering
lexCompare ty a b = cmpValue Concrete op opw op (const op) ty a b (return EQ)
 where
   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = op (bvVal x) (bvVal y) k

   op :: Ord a => a -> a -> Eval Ordering -> Eval Ordering
   op x y k = case compare x y of
                     EQ  -> k
                     cmp -> return cmp


-- Arith -----------------------------------------------------------------------

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   However, if the bitvector size is 0, always return the 0
--   bitvector.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith Concrete
liftBinArith _  0 _        _        = ready $ mkBv 0 0
liftBinArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   Generate a thunk that throws a divide by 0 error when forced if the second
--   argument is 0.  However, if the bitvector size is 0, always return the 0
--   bitvector.
liftDivArith :: (Integer -> Integer -> Integer) -> BinArith Concrete
liftDivArith _  0 _        _        = ready $ mkBv 0 0
liftDivArith _  _ _        (BV _ 0) = divideByZero
liftDivArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

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

liftUnaryArith :: (Integer -> Integer) -> UnaryArith Concrete
liftUnaryArith op w (BV _ x) = ready $ mkBv w $ op x


signedLexCompare :: TValue -> Value -> Value -> Eval Ordering
signedLexCompare ty a b = cmpValue Concrete opb opw opi (const opi) ty a b (return EQ)
 where
   opb :: Bool -> Bool -> Eval Ordering -> Eval Ordering
   opb _x _y _k = panic "signedLexCompare"
                    ["Attempted to perform signed comparisons on bare Bit type"]

   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = case compare (signedBV x) (signedBV y) of
                     EQ  -> k
                     cmp -> return cmp

   opi :: Integer -> Integer -> Eval Ordering -> Eval Ordering
   opi _x _y _k = panic "signedLexCompare"
                    ["Attempted to perform signed comparisons on Integer type"]

-- | Process two elements based on their lexicographic ordering.
cmpOrder :: String -> (Ordering -> Bool) -> Binary Concrete
cmpOrder _nm op ty l r = VBit . op <$> lexCompare ty l r

-- | Process two elements based on their lexicographic ordering, using signed comparisons
signedCmpOrder :: String -> (Ordering -> Bool) -> Binary Concrete
signedCmpOrder _nm op ty l r = VBit . op <$> signedLexCompare ty l r



liftSigned ::
  (Integer -> Integer -> Integer -> Eval BV) ->
  BinArith Concrete
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
signedValue i x = if testBit x (fromInteger (i-1)) then x - (1 `shiftL` (fromInteger i)) else x

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
  wlam Concrete $ \(BV i x) -> return $
  wlam Concrete $ \y ->
   let signx = testBit x (fromInteger (i-1))
       amt   = fromInteger (bvVal y)
       x'    = if signx then x - bit (fromInteger i) else x
    in return . VWord i . ready . WordVal . mkBv i $! x' `shiftR` amt

-- | Signed carry bit.
scarryV :: Value
scarryV =
  nlam $ \_n ->
  wlam Concrete $ \(BV i x) -> return $
  wlam Concrete $ \(BV j y) ->
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
  wlam Concrete $ \(BV i x) -> return $
  wlam Concrete $ \(BV j y) ->
    if i == j
      then return . VBit $! testBit (x + y) (fromInteger i)
      else evalPanic "carryV" ["Attempted to compute with words of different sizes"]


logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete)
           -> Value
logicShift opW opS
  = nlam $ \ a ->
    nlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        BV _ i <- fromVWord Concrete "logicShift amount" =<< r
        l >>= \case
          VWord w wv -> return $ VWord w $ wv >>= \case
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))
                          LargeBitsVal n xs -> return $ LargeBitsVal n $ opS (Nat n) c xs i

          _ -> mkSeq a c <$> (opS a c <$> (fromSeq "logicShift" =<< l) <*> return i)

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

shiftLS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
shiftLS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> zeroV Concrete ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w i by
  | by >= w   = 0
  | otherwise = shiftR i (fromInteger by)

shiftRS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
shiftRS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i >= by   -> lookupSeqMap vs (i-by)
      | i < len   -> zeroV Concrete ety
      | otherwise -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf
      | i >= by   -> lookupSeqMap vs (i-by)
      | otherwise -> zeroV Concrete ety


-- XXX integer doesn't implement rotateL, as there's no bit bound
rotateLW :: Integer -> Integer -> Integer -> Integer
rotateLW 0 i _  = i
rotateLW w i by = mask w $ (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateLS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
rotateLS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Integer -> Integer
rotateRW 0 i _  = i
rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateRS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
rotateRS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------


indexFront :: Maybe Integer -> TValue -> SeqMap Concrete -> BV -> Eval Value
indexFront mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> lookupSeqMap vs ix

indexFront_bits :: Maybe Integer -> TValue -> SeqMap Concrete -> Seq.Seq Bool -> Eval Value
indexFront_bits mblen a vs bs = indexFront mblen a vs =<< io (packWord Concrete (Fold.toList bs))

indexBack :: Maybe Integer -> TValue -> SeqMap Concrete -> BV -> Eval Value
indexBack mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len > ix  -> lookupSeqMap vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

indexBack_bits :: Maybe Integer -> TValue -> SeqMap Concrete -> Seq.Seq Bool -> Eval Value
indexBack_bits mblen a vs bs = indexBack mblen a vs =<< io (packWord Concrete (Fold.toList bs))


updateFront
  :: Nat'
  -> TValue
  -> SeqMap Concrete
  -> WordValue Concrete
  -> Eval Value
  -> Eval (SeqMap Concrete)
updateFront len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs idx val

updateFront_word
 :: Nat'
 -> TValue
 -> WordValue Concrete
 -> WordValue Concrete
 -> Eval Value
 -> Eval (WordValue Concrete)
updateFront_word _len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs idx (fromBit =<< val)

updateBack
  :: Nat'
  -> TValue
  -> SeqMap Concrete
  -> WordValue Concrete
  -> Eval Value
  -> Eval (SeqMap Concrete)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word
 :: Nat'
 -> TValue
 -> WordValue Concrete
 -> WordValue Concrete
 -> Eval Value
 -> Eval (WordValue Concrete)
updateBack_word Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_word (Nat n) _eltTy bs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs (n - idx - 1) (fromBit =<< val)

{-
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  let idx' = n - idx - 1
  return $! Seq.update (fromInteger idx') (fromVBit <$> val) bs
-}
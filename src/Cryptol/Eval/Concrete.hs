{-# Language TypeFamilies #-}
module Cryptol.Eval.Concrete where

import Data.Bits
import MonadLib
import Data.List(genericLength)
import qualified Data.Text as T


import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(mkIdent)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.BV
import Cryptol.Eval.Float
import Cryptol.Eval.SeqMap
import Cryptol.Eval.Value
import Cryptol.Eval.PP



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

  intModPlus  m x y = (x + y) `mod` m
  intModMinus m x y = (x - y) `mod` m
  intModMult  m x y = (x * y) `mod` m

  wordToInt (BV _ x) = x
  wordFromInt w x = mkBv w x


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

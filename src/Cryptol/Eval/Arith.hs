{-# Language TupleSections, DataKinds #-}
-- | Utilities for implementing the @Arith@ class.
module Cryptol.Eval.Arith where

import Control.Monad(join)

import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Eval.SeqMap
import Cryptol.Eval.Monad

--------------------------------------------------------------------------------
-- Lifting through structured types for 'Arith'. Words are considered
-- to be a primitive types.

data ArithPrims n p = ArithPrims
  { arithWord    :: Integer ->            Fun n (VWord p)
  , arithInteger ::                       Fun n (VInteger p)
  , arithZ       :: Integer ->            Fun n (VInteger p)
  , arithFloat   :: Integer -> Integer -> Fun n (VFloat p)
  }

arith0 :: BitWord p => ArithPrims 0 p -> GenValue p
arith0 ops = nullary (arithNullary ops)

arith1 :: BitWord p => ArithPrims 1 p -> GenValue p
arith1 ops = unary (arithUnary ops)

arith2 :: BitWord p => ArithPrims 2 p -> GenValue p
arith2 ops = binary (arithBinary ops)

arithNullary :: BitWord p => ArithPrims 0 p -> TValue -> Fun 0 (GenValue p)
arithNullary ops = loop
  where
    loop ty =
      case ty of
        TVBit       -> evalPanic "arithNullary" ["Bit not in class Arith"]
        TVInteger   -> VInteger <$> arithInteger ops
        TVIntMod n  -> VInteger <$> arithZ ops n
        TVFloat e p -> VFloat   <$> arithFloat ops e p

        TVSeq w a
          -- words and finite sequences
          | isTBit a  -> pure $ VWord w (WordVal <$> arithWord ops w)
          | otherwise -> pure $ VSeq w $ IndexSeqMap $ const $ loop a

        TVStream a -> pure $ VStream $ IndexSeqMap $ const $ loop a

        TVFun _ b -> pure $ lam $ const $ loop b

        TVTuple tys -> pure $ VTuple $ map loop tys

        TVRec fs -> pure $ VRecord [ (f, loop a) | (f, a) <- fs ]

        TVAbstract {} ->
          evalPanic "arithNullary" ["Abstract type not in `Arith`"]


arithUnary :: BitWord p => ArithPrims 1 p -> TValue -> Fun 1 (GenValue p)
arithUnary ops = loop
  where
  loop' ty x = loop ty =<< x

  loop ty x = case ty of

    TVBit ->
      evalPanic "arithUnary" ["Bit not in class Arith"]

    TVInteger ->
      VInteger <$> arithInteger ops (fromVInteger x)

    TVIntMod n ->
      VInteger <$> arithZ ops n (fromVInteger x)

    TVFloat e p ->
      VFloat <$> arithFloat ops e p (fromVFloat x)


    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord "arithUnary" x
              return $ VWord w (WordVal <$> arithWord ops w wx)
      | otherwise -> VSeq w <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    TVStream a ->
      VStream <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    -- functions
    TVFun _ ety ->
      return $ lam $ \ y -> loop' ety (fromVFun x y)

    -- tuples
    TVTuple tys ->
      do as <- mapM (delay Nothing) (fromVTuple x)
         return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      do fs' <- sequence
                 [ (f,) <$> delay Nothing (loop' fty (lookupRecord f x))
                 | (f,fty) <- fs
                 ]
         return $ VRecord fs'

    TVAbstract {} -> evalPanic "arithUnary" ["Abstract type not in `Arith`"]




arithBinary :: BitWord p => ArithPrims 2 p -> TValue -> Fun 2 (GenValue p)
arithBinary ops = loop
  where
  loop' ty l r = join (loop ty <$> l <*> r)

  loop ty l r = case ty of
    TVBit ->
      evalPanic "arithBinary" ["Bit not in class Arith"]

    TVInteger ->
      VInteger <$> arithInteger ops (fromVInteger l) (fromVInteger r)

    TVIntMod n ->
      VInteger <$> arithZ ops n (fromVInteger l) (fromVInteger r)

    TVFloat e p ->
      VFloat <$> arithFloat ops e p (fromVFloat l) (fromVFloat r)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
                  lw <- fromVWord "arithLeft" l
                  rw <- fromVWord "arithRight" r
                  return $ VWord w (WordVal <$> arithWord ops w lw rw)
      | otherwise -> VSeq w <$> (join (zipSeqMap (loop a) <$>
                                      (fromSeq "arithBinary left" l) <*>
                                      (fromSeq "arithBinary right" r)))

    TVStream a ->
      -- streams
      VStream <$> (join (zipSeqMap (loop a) <$>
                             (fromSeq "arithBinary left" l) <*>
                             (fromSeq "arithBinary right" r)))

    -- functions
    TVFun _ ety ->
      return $ lam $ \ x -> loop' ety (fromVFun l x) (fromVFun r x)

    -- tuples
    TVTuple tys ->
      do ls <- mapM (delay Nothing) (fromVTuple l)
         rs <- mapM (delay Nothing) (fromVTuple r)
         return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    TVRec fs ->
      do fs' <- sequence
                 [ (f,) <$> delay Nothing (loop' fty (lookupRecord f l) (lookupRecord f r))
                 | (f,fty) <- fs
                 ]
         return $ VRecord fs'

    TVAbstract {} ->
      evalPanic "arithBinary" ["Abstract type not in `Arith`"]



--------------------------------------------------------------------------------
-- Arith primitives that are used in the definitions of other primitives

intV :: BitWord p => VInteger p -> TValue -> Fun 0 (GenValue p)
intV i = arithNullary ArithPrims
  { arithWord    = \n -> pure (wordFromInt n i)
  , arithInteger = pure i
  , arithZ       = \n -> pure (intMod i (integerLit n))
  , arithFloat   = \e p -> fpFromInteger' e p i
  }

addV :: BitWord p => TValue -> Fun 2 (GenValue p)
addV = arithBinary ArithPrims
  { arithWord     = \_w x y -> ready $ wordPlus x y
  , arithInteger  = \x y    -> ready $ intPlus x y
  , arithZ        = \m x y  -> ready $ intModPlus m x y
  , arithFloat    = fpArithAdd'
  }

subV :: BitWord p => TValue -> Fun 2 (GenValue p)
subV = arithBinary ArithPrims
  { arithWord    = \_w x y -> ready $ wordMinus x y
  , arithInteger = \x y    -> ready $ intMinus x y
  , arithZ       = \m x y  -> ready $ intModMinus m x y
  , arithFloat   = fpArithSub'
  }

mulV :: BitWord p => TValue -> Fun 2 (GenValue p)
mulV = arithBinary ArithPrims
  { arithWord      = \_w x y -> ready $ wordMult x y
  , arithInteger   = \x y    -> ready $ intMult x y
  , arithZ         = \m x y  -> ready $ intModMult m x y
  , arithFloat     = fpArithMul'
  }



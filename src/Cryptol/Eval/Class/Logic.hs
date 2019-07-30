{-# Language TupleSections, DataKinds #-}
-- | Utilities for implementing the @Logic@ class.
module Cryptol.Eval.Class.Logic where

import Control.Monad(join)
import qualified Data.Sequence as Seq

import Cryptol.Eval.Value
import Cryptol.Eval.SeqMap
import Cryptol.Eval.Type
import Cryptol.Eval.Monad

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary ::
  BitWord p =>
  (VBool p -> VBool p -> VBool p) ->
  (VWord p -> VWord p -> VWord p) ->
  TValue -> Fun 2 (GenValue p)

logicBinary opb opw = loop
  where
  loop' ty l r = join (loop ty <$> l <*> r)

  loop ty l r = case ty of
    TVBit -> return $ VBit (opb (fromVBit l) (fromVBit r))
    TVInteger -> evalPanic "logicBinary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicBinary" ["Z not in class Logic"]
    TVFloat {} -> evalPanic "logicBinary" ["Float not in class Logic"]
    TVReal {} -> evalPanic "logicBinary" ["`Real` not in class `Logic`"]
    TVSeq w aty
         -- words
         | isTBit aty
              -> do v <- delay Nothing $ join
                            (wordValLogicOp opb opw <$>
                                    fromWordVal "logicBinary l" l <*>
                                    fromWordVal "logicBinary r" r)
                    return $ VWord w v

         -- finite sequences
         | otherwise -> VSeq w <$>
                           (join (zipSeqMap (loop aty) <$>
                                    (fromSeq "logicBinary left" l)
                                    <*> (fromSeq "logicBinary right" r)))

    TVStream aty ->
        VStream <$> (join (zipSeqMap (loop aty) <$>
                          (fromSeq "logicBinary left" l) <*>
                          (fromSeq "logicBinary right" r)))

    TVTuple etys -> do
        ls <- mapM (delay Nothing) (fromVTuple l)
        rs <- mapM (delay Nothing) (fromVTuple r)
        return $ VTuple $ zipWith3 loop' etys ls rs

    TVFun _ bty ->
        return $ lam $ \ a -> loop' bty (fromVFun l a) (fromVFun r a)

    TVRec fields ->
        do fs <- sequence
                   [ (f,) <$> delay Nothing (loop' fty a b)
                   | (f,fty) <- fields
                   , let a = lookupRecord f l
                         b = lookupRecord f r
                   ]
           return $ VRecord fs

    TVAbstract {} -> evalPanic "logicBinary" [ "Abstract type not in `Logic`" ]


wordValLogicOp ::
  BitWord p =>
  (VBool p -> VBool p -> VBool p) ->
  (VWord p -> VWord p -> VWord p) ->
  Fun 2 (WordValue p)

wordValLogicOp _ wop (WordVal w1) (WordVal w2) = return $ WordVal (wop w1 w2)

wordValLogicOp bop _ (BitsVal xs) (BitsVal ys) =
  BitsVal <$> sequence (Seq.zipWith f xs ys)
  where
  f x y = delay Nothing (bop <$> x <*> y)

wordValLogicOp bop _ (WordVal w1) (BitsVal ys) =
  ready $ BitsVal $ Seq.zipWith f (Seq.fromList $ map ready $ unpackWord w1) ys
  where
  f x y = bop <$> x <*> y

wordValLogicOp bop _ (BitsVal xs) (WordVal w2) =
  ready $ BitsVal $ Seq.zipWith f xs (Seq.fromList $ map ready $ unpackWord w2)
  where
  f x y = bop <$> x <*> y

wordValLogicOp bop _ w1 w2 = LargeBitsVal (wordValueSize w1) <$> zs
  where
  zs = memoMap $ IndexSeqMap $ \i ->
                          bop <$> (lookupSeqMap xs i) <*> (lookupSeqMap ys i)
  xs = asBitsMap w1
  ys = asBitsMap w2




wordValUnaryOp ::
  BitWord p =>
  (VBool p -> VBool p) ->
  (VWord p -> VWord p) ->
  WordValue p -> WordValue p

wordValUnaryOp _ wop (WordVal w)  = WordVal (wop w)
wordValUnaryOp bop _ (BitsVal bs) = BitsVal (fmap (bop <$>) bs)
wordValUnaryOp bop _ (LargeBitsVal n xs) = LargeBitsVal n (bop <$> xs)


logicUnary ::
  BitWord p =>
  (VBool p -> VBool p) ->
  (VWord p -> VWord p) ->
  TValue -> Fun 1 (GenValue p)

logicUnary opb opw = loop
  where
  loop' ty val = loop ty =<< val

  loop ty val = case ty of
    TVBit -> return . VBit . opb $ fromVBit val

    TVInteger -> evalPanic "logicUnary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicUnary" ["Z not in class Logic"]
    TVFloat {} -> evalPanic "logicUnary" ["Float is not in class Logic"]
    TVReal {}  -> evalPanic "logicUnary" ["`Real` is not in class `Logic`"]

    TVSeq w ety
         -- words
         | isTBit ety
              -> do v <- delay Nothing (wordValUnaryOp opb opw <$> fromWordVal "logicUnary" val)
                    return $ VWord w v

         -- finite sequences
         | otherwise
              -> VSeq w <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

         -- streams
    TVStream ety ->
         VStream <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

    TVTuple etys ->
      do as <- mapM (delay Nothing) (fromVTuple val)
         return $ VTuple (zipWith loop' etys as)

    TVFun _ bty ->
      return $ lam $ \ a -> loop' bty (fromVFun val a)

    TVRec fields ->
      do fs <- sequence
                 [ (f,) <$> delay Nothing (loop' fty a)
                 | (f,fty) <- fields, let a = lookupRecord f val
                 ]
         return $ VRecord fs

    TVAbstract {} -> evalPanic "logicUnary" [ "Abstract type not in `Logic`" ]



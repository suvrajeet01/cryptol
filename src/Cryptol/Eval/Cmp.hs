-- | Utilities for implementing the @Cmp@ class.
module Cryptol.Eval.Cmp where

import Data.List(sortBy)
import Data.Ord (comparing)

import Cryptol.Utils.Panic(panic)
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Eval.Monad
import Cryptol.Eval.SeqMap

data CmpPrims p r = CmpPrims
  { cmpBool       :: CmpFun (VBool p) r
  , cmpWord       :: Integer -> CmpFun (VWord p) r
  , cmpInteger    :: CmpFun (VInteger p) r
  , cmpZ          :: Integer -> CmpFun (VInteger p) r
  , cmpFloat      :: Integer -> Integer -> CmpFun (VFloat p) r
  }

type CmpFun a r = a -> a -> Eval r -> Eval r

cmpValue :: BitWord p => CmpPrims p a -> TValue -> CmpFun (GenValue p) a
cmpValue ps = cmp
  where
    cmp ty v1 v2 k =
      case ty of
        TVBit         -> cmpBool ps (fromVBit v1) (fromVBit v2) k
        TVInteger     -> cmpInteger ps (fromVInteger v1) (fromVInteger v2) k
        TVIntMod n    -> cmpZ ps n (fromVInteger v1) (fromVInteger v2) k
        TVFloat e p   -> cmpFloat ps e p (fromVFloat v1) (fromVFloat v2) k

        TVSeq n t
          | isTBit t  -> do w1 <- fromVWord "cmpValue" v1
                            w2 <- fromVWord "cmpValue" v2
                            cmpWord ps n w1 w2 k
          | otherwise -> cmpValues (repeat t)
                         (enumerateSeqMap n (fromVSeq v1))
                         (enumerateSeqMap n (fromVSeq v2)) k
        TVStream _    -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Infinite streams are not comparable" ]
        TVFun _ _     -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Functions are not comparable" ]
        TVTuple tys   -> cmpValues tys (fromVTuple v1) (fromVTuple v2) k
        TVRec fields  -> do let vals = map snd . sortBy (comparing fst)
                            let tys = vals fields
                            cmpValues tys
                              (vals (fromVRecord v1))
                              (vals (fromVRecord v2)) k
        TVAbstract {} -> evalPanic "cmpValue"
                          [ "Abstract type not in `Cmp`" ]

    cmpValues (t : ts) (x1 : xs1) (x2 : xs2) k =
      do x1' <- x1
         x2' <- x2
         cmp t x1' x2' (cmpValues ts xs1 xs2 k)
    cmpValues _ _ _ k = k


cmpBy :: Ord b => (a -> b) -> a -> a -> Eval Ordering -> Eval Ordering
cmpBy f = \x y k -> case compare (f x) (f y) of
                      EQ -> k
                      r  -> pure r




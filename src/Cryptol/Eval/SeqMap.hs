module Cryptol.Eval.SeqMap where

import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List(genericIndex)
import Control.DeepSeq

import Cryptol.Eval.Monad


-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap a
  = IndexSeqMap  !(Integer -> Eval a)
  | UpdateSeqMap !(Map Integer (Eval a)) !(Integer -> Eval a)

instance Functor SeqMap where
  fmap f mp =
    case mp of
      IndexSeqMap i    -> IndexSeqMap                 (\n -> f <$> i n)
      UpdateSeqMap m i -> UpdateSeqMap (fmap f <$> m) (\n -> f <$> i n)

lookupSeqMap :: SeqMap a -> Integer -> Eval a
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m f) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> f i

instance NFData (SeqMap a) where
  rnf x = seq x ()

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: [Eval a] -> SeqMap a
finiteSeqMap xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      invalidIndex

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: [Eval a] -> Eval (SeqMap a)
infiniteSeqMap xs =
   -- TODO: use an int-trie?
   memoMap (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length `n` of the values from [0..n-1] in
--   the given the sequence emap.
enumerateSeqMap :: (Integral n) => n -> SeqMap a -> [Eval a]
enumerateSeqMap n m = [ lookupSeqMap m i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: SeqMap a -> [Eval a]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Integer     -- ^ Size of the sequence map
              -> SeqMap a
              -> SeqMap a
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap a -> Integer -> Eval a -> SeqMap a
updateSeqMap (UpdateSeqMap m sm) i x = UpdateSeqMap (Map.insert i x m) sm
updateSeqMap (IndexSeqMap f) i x = UpdateSeqMap (Map.singleton i x) f

-- | Concatenate the first `n` values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Integer -> SeqMap a -> SeqMap a -> SeqMap a
concatSeqMap n x y =
    IndexSeqMap $ \i ->
       if i < n
         then lookupSeqMap x i
         else lookupSeqMap y (i-n)

-- | Given a number `n` and a sequence map, return two new sequence maps:
--   the first containing the values from `[0..n-1]` and the next containing
--   the values from `n` onward.
splitSeqMap :: Integer -> SeqMap a -> (SeqMap a, SeqMap a)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Drop the first @n@ elements of the given @SeqMap@.
dropSeqMap :: Integer -> SeqMap a -> SeqMap a
dropSeqMap 0 xs = xs
dropSeqMap n xs = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: SeqMap a -> Eval (SeqMap a)
memoMap x = do
  cache <- io $ newIORef $ Map.empty
  return $ IndexSeqMap (memo cache)

  where
  memo cache i = do
    mz <- io (Map.lookup i <$> readIORef cache)
    case mz of
      Just z  -> return z
      Nothing -> doEval cache i

  doEval cache i = do
    v <- lookupSeqMap x i
    io $ modifyIORef' cache (Map.insert i v)
    return v

-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap :: (a -> b -> Eval c) -> SeqMap a -> SeqMap b -> Eval (SeqMap c)
zipSeqMap f x y =
  memoMap $ IndexSeqMap $ \i -> do a <- lookupSeqMap x i
                                   b <- lookupSeqMap y i
                                   f a b

-- | Apply the given function to each value in the given sequence map
mapSeqMap :: (a -> Eval b) -> SeqMap a -> Eval (SeqMap b)
mapSeqMap f x = memoMap (IndexSeqMap $ \i -> f =<< lookupSeqMap x i)

mergeSeqMapWith :: (a -> b -> Eval c) -> SeqMap a -> SeqMap b -> SeqMap c
mergeSeqMapWith f x y =
  IndexSeqMap $ \i ->
  do xi <- lookupSeqMap x i
     yi <- lookupSeqMap y i
     f xi yi




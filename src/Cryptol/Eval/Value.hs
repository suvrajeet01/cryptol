-- |
-- Module      :  Cryptol.Eval.Value
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cryptol.Eval.Value where

import Data.Bits
import Data.IORef
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import MonadLib
import qualified Data.Kind as HS (Type,Constraint)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Type

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

import Data.List(genericLength, genericIndex, genericDrop)
import qualified Data.Text as T
import Numeric (showIntAtBase)

import GHC.Generics (Generic)
import Control.DeepSeq

-- Values ----------------------------------------------------------------------

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

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i = BV w (mask w i)

-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap p
  = IndexSeqMap  !(Integer -> Eval (GenValue p))
  | UpdateSeqMap !(Map Integer (Eval (GenValue p)))
                 !(Integer -> Eval (GenValue p))

lookupSeqMap :: SeqMap p -> Integer -> Eval (GenValue p)
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m f) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> f i

type SeqValMap = SeqMap EvalConc

instance NFData (SeqMap p) where
  rnf x = seq x ()

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: [Eval (GenValue p)] -> SeqMap p
finiteSeqMap xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      invalidIndex

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: [Eval (GenValue p)] -> Eval (SeqMap p)
infiniteSeqMap xs =
   -- TODO: use an int-trie?
   memoMap (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length `n` of the values from [0..n-1] in
--   the given the sequence emap.
enumerateSeqMap :: (Integral n) => n -> SeqMap p -> [Eval (GenValue p)]
enumerateSeqMap n m = [ lookupSeqMap m i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: SeqMap p -> [Eval (GenValue p)]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Integer     -- ^ Size of the sequence map
              -> SeqMap p
              -> SeqMap p
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap p -> Integer -> Eval (GenValue p) -> SeqMap p
updateSeqMap (UpdateSeqMap m sm) i x = UpdateSeqMap (Map.insert i x m) sm
updateSeqMap (IndexSeqMap f) i x = UpdateSeqMap (Map.singleton i x) f

-- | Concatenate the first `n` values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Integer -> SeqMap p -> SeqMap p -> SeqMap p
concatSeqMap n x y =
    IndexSeqMap $ \i ->
       if i < n
         then lookupSeqMap x i
         else lookupSeqMap y (i-n)

-- | Given a number `n` and a sequence map, return two new sequence maps:
--   the first containing the values from `[0..n-1]` and the next containing
--   the values from `n` onward.
splitSeqMap :: Integer -> SeqMap p -> (SeqMap p, SeqMap p)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Drop the first @n@ elements of the given @SeqMap@.
dropSeqMap :: Integer -> SeqMap p -> SeqMap p
dropSeqMap 0 xs = xs
dropSeqMap n xs = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: SeqMap p -> Eval (SeqMap p)
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
zipSeqMap :: (GenValue p -> GenValue p -> Eval (GenValue p))
          -> SeqMap p
          -> SeqMap p
          -> Eval (SeqMap p)
zipSeqMap f x y =
  memoMap (IndexSeqMap $ \i -> join (f <$> lookupSeqMap x i <*> lookupSeqMap y i))

-- | Apply the given function to each value in the given sequence map
mapSeqMap :: (GenValue p -> Eval (GenValue p))
          -> SeqMap p -> Eval (SeqMap p)
mapSeqMap f x =
  memoMap (IndexSeqMap $ \i -> f =<< lookupSeqMap x i)

-- | For efficiency reasons, we handle finite sequences of bits as special cases
--   in the evaluator.  In cases where we know it is safe to do so, we prefer to
--   used a "packed word" representation of bit sequences.  This allows us to rely
--   directly on Integer types (in the concrete evaluator) and SBV's Word types (in
--   the symbolic simulator).
--
--   However, if we cannot be sure all the bits of the sequence
--   will eventually be forced, we must instead rely on an explicit sequence of bits
--   representation.
data WordValue p
  = WordVal !(VWord p)                      -- ^ Packed word representation for bit sequences.
  | BitsVal !(Seq.Seq (Eval (VBool p)))     -- ^ Sequence of thunks representing bits.
  | LargeBitsVal !Integer !(SeqMap p)       -- ^ A large bitvector sequence, represented as a
                                            --   @SeqMap@ of bits.
 deriving (Generic)

deriving instance (Class NFData p) => NFData (WordValue p)

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to @SeqMap@ representation.
largeBitSize :: Integer
largeBitSize = 1 `shiftL` 16

-- | Force a word value into packed word form
asWordVal :: BitWord p => WordValue p -> Eval (VWord p)
asWordVal (WordVal w)         = return w
asWordVal (BitsVal bs)        = packWord <$> sequence (Fold.toList bs)
asWordVal (LargeBitsVal n xs) = packWord <$> traverse (fromBit =<<) (enumerateSeqMap n xs)

-- | Force a word value into a sequence of bits
asBitsMap :: BitWord p => WordValue p -> SeqMap p
asBitsMap (WordVal w)  = IndexSeqMap $ \i -> ready $ VBit $ wordBit w i
asBitsMap (BitsVal bs) = IndexSeqMap $ \i -> VBit <$> join (checkedSeqIndex bs i)
asBitsMap (LargeBitsVal _ xs) = xs

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in big-endian order.
enumerateWordValue :: BitWord p => WordValue p -> Eval [VBool p]
enumerateWordValue (WordVal w)  = return $ unpackWord w
enumerateWordValue (BitsVal bs) = sequence (Fold.toList bs)
enumerateWordValue (LargeBitsVal n xs) = traverse (fromBit =<<) (enumerateSeqMap n xs)

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in reverse of the usual order, which is little-endian order.
enumerateWordValueRev :: BitWord p => WordValue p -> Eval [VBool p]
enumerateWordValueRev (WordVal w)  = return $ reverse $ unpackWord w
enumerateWordValueRev (BitsVal bs) = sequence (Fold.toList $ Seq.reverse bs)
enumerateWordValueRev (LargeBitsVal n xs) = traverse (fromBit =<<) (enumerateSeqMap n (reverseSeqMap n xs))

-- | Compute the size of a word value
wordValueSize :: BitWord p => WordValue p -> Integer
wordValueSize (WordVal w)  = wordLen w
wordValueSize (BitsVal bs) = toInteger $ Seq.length bs
wordValueSize (LargeBitsVal n _) = n

checkedSeqIndex :: Seq.Seq a -> Integer -> Eval a
checkedSeqIndex xs i =
  case Seq.viewl (Seq.drop (fromInteger i) xs) of
    x Seq.:< _ -> return x
    Seq.EmptyL -> invalidIndex i

checkedIndex :: [a] -> Integer -> Eval a
checkedIndex xs i =
  case genericDrop i xs of
    (x:_) -> return x
    _     -> invalidIndex i

-- | Select an individual bit from a word value
indexWordValue :: BitWord p => WordValue p -> Integer -> Eval (VBool p)
indexWordValue (WordVal w) idx
   | idx < wordLen w = return $ wordBit w idx
   | otherwise = invalidIndex idx
indexWordValue (BitsVal bs) idx = join (checkedSeqIndex bs idx)
indexWordValue (LargeBitsVal n xs) idx
   | idx < n   = fromBit =<< lookupSeqMap xs idx
   | otherwise = invalidIndex idx

-- | Produce a new @WordValue@ from the one given by updating the @i@th bit with the
--   given bit value.
updateWordValue :: BitWord p => WordValue p -> Integer -> Eval (VBool p) -> Eval (WordValue p)
updateWordValue (WordVal w) idx (Ready b)
   | idx < wordLen w = return $ WordVal $ wordUpdate w idx b
   | otherwise = invalidIndex idx
updateWordValue (WordVal w) idx b
   | idx < wordLen w = return $ BitsVal $ Seq.update (fromInteger idx) b $ Seq.fromList $ map ready $ unpackWord w
   | otherwise = invalidIndex idx
updateWordValue (BitsVal bs) idx b
   | idx < toInteger (Seq.length bs) = return $ BitsVal $ Seq.update (fromInteger idx) b bs
   | otherwise = invalidIndex idx
updateWordValue (LargeBitsVal n xs) idx b
   | idx < n = return $ LargeBitsVal n $ updateSeqMap xs idx (VBit <$> b)
   | otherwise = invalidIndex idx

-- | Generic value type, parameterized on the representation of basic types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   `VSeq` must never be used for finite sequences of bits.
--   Always use the `VWord` constructor instead!  Infinite sequences of bits
--   are handled by the `VStream` constructor, just as for other types.
data GenValue p
  = VRecord ![(Ident, Eval (GenValue p))]     -- ^ @ { .. } @
  | VTuple ![Eval (GenValue p)]               -- ^ @ ( .. ) @
  | VBit !(VBool p)                           -- ^ @ Bit    @
  | VInteger !(VInteger p)                    -- ^ @ Integer @ or @ Z n @
  | VSeq !Integer !(SeqMap p)                 -- ^ @ [n]a   @
                                              --   Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(Eval (WordValue p))      -- ^ @ [n]Bit @
  | VStream !(SeqMap p)                       -- ^ @ [inf]a @
  | VFun (Eval (GenValue p) -> Eval (GenValue p)) -- ^ functions
  | VPoly (TValue -> Eval (GenValue p))       -- ^ polymorphic values (kind *)
  | VNumPoly (Nat' -> Eval (GenValue p))      -- ^ polymorphic values (kind #)
 deriving (Generic)

deriving instance Class NFData p => NFData (GenValue p)


type family VBool p = b | b -> p
type family VInteger p = i | i -> p
type family VWord p = w | w -> p

type Class (c :: HS.Type -> HS.Constraint) p =
    (c (VBool p), c (VInteger p), c (VWord p))


data EvalConc

type instance VBool EvalConc = Bool
type instance VInteger EvalConc = Integer
type instance VWord EvalConc = BV



-- | Force the evaluation of a word value
forceWordValue :: WordValue p -> Eval ()
forceWordValue (WordVal _w)  = return ()
forceWordValue (BitsVal bs) = mapM_ (\b -> const () <$> b) bs
forceWordValue (LargeBitsVal n xs) = mapM_ (\x -> const () <$> x) (enumerateSeqMap n xs)

-- | Force the evaluation of a value
forceValue :: GenValue p -> Eval ()
forceValue v = case v of
  VRecord fs  -> mapM_ (\x -> forceValue =<< snd x) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit _b     -> return ()
  VInteger _i -> return ()
  VWord _ wv  -> forceWordValue =<< wv
  VStream _   -> return ()
  VFun _      -> return ()
  VPoly _     -> return ()
  VNumPoly _  -> return ()


instance Class Show p => Show (GenValue p) where
  show v = case v of
    VRecord fs -> "record:" ++ show (map fst fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit b     -> show b
    VInteger i -> show i
    VSeq n _   -> "seq:" ++ show n
    VWord n _  -> "word:"  ++ show n
    VStream _  -> "stream"
    VFun _     -> "fun"
    VPoly _    -> "poly"
    VNumPoly _ -> "numpoly"

type Value = GenValue EvalConc


-- Pretty Printing -------------------------------------------------------------

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5 }

atFst :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
atFst f (x,y) = fmap (,y) $ f x

atSnd :: Functor f => (a -> f b) -> (c, a) -> f (c, b)
atSnd f (x,y) = fmap (x,) $ f y

ppValue :: forall p
         . BitWord p
        => PPOpts
        -> GenValue p
        -> Eval Doc
ppValue opts = loop
  where
  loop :: GenValue p -> Eval Doc
  loop val = case val of
    VRecord fs         -> do fs' <- traverse (atSnd (>>=loop)) $ fs
                             return $ braces (sep (punctuate comma (map ppField fs')))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop) vals
                             return $ parens (sep (punctuate comma vals'))
    VBit b             -> return $ ppBit b
    VInteger i         -> return $ ppInteger opts i
    VSeq sz vals       -> ppWordSeq sz vals
    VWord _ wv         -> ppWordVal =<< wv
    VStream vals       -> do vals' <- traverse (>>=loop) $ enumerateSeqMap (useInfLength opts) vals
                             return $ brackets $ fsep
                                   $ punctuate comma
                                   ( vals' ++ [text "..."]
                                   )
    VFun _             -> return $ text "<function>"
    VPoly _            -> return $ text "<polymorphic value>"
    VNumPoly _         -> return $ text "<polymorphic value>"

  ppWordVal :: WordValue p -> Eval Doc
  ppWordVal w = ppWord opts <$> asWordVal w

  ppWordSeq :: Integer -> SeqMap p -> Eval Doc
  ppWordSeq sz vals = do
    ws <- sequence (enumerateSeqMap sz vals)
    case ws of
      w : _
        | Just l <- vWordLen w
        , asciiMode opts l
        -> do vs <- traverse (fromVWord "ppWordSeq") ws
              case traverse wordAsChar vs of
                Just str -> return $ text (show str)
                _ -> return $ brackets (fsep (punctuate comma $ map (ppWord opts) vs))
      _ -> do ws' <- traverse loop ws
              return $ brackets (fsep (punctuate comma ws'))

asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger


ppBV :: PPOpts -> BV -> Doc
ppBV opts (BV width i)
  | base > 36 = integer i -- not sure how to rule this out
  | asciiMode opts width = text (show (toEnum (fromInteger i) :: Char))
  | otherwise = prefix <.> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <.> padding 1
    8  -> text "0o" <.> padding 3
    10 -> empty
    16 -> text "0x" <.> padding 4
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"


-- | This type class defines a collection of operations on bits and words that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class BitWord p where

  -- | Pretty-print an individual bit
  ppBit :: VBool p -> Doc

  -- | Pretty-print a word value
  ppWord :: PPOpts -> VWord p -> Doc

  -- | Pretty-print an integer value
  ppInteger :: PPOpts -> VInteger p -> Doc

  -- | Attempt to render a word value as an ASCII character.  Return `Nothing`
  --   if the character value is unknown (e.g., for symbolic values).
  wordAsChar :: VWord p -> Maybe Char

  -- | The number of bits in a word value.
  wordLen :: VWord p -> Integer

  -- | Construct a literal bit value from a boolean.
  bitLit :: Bool -> VBool p

  -- | Construct a literal word value given a bit width and a value.
  wordLit :: Integer {- ^ Width -} ->
             Integer {- ^ Value -} ->
             VWord p

  -- | Construct a literal integer value from the given integer.
  integerLit :: Integer {-- ^ Value -} -> VInteger p

  -- | Extract the numbered bit from the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordBit :: VWord p -> Integer -> VBool p

  -- | Update the numbered bit in the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordUpdate :: VWord p -> Integer -> VBool p -> VWord p

  -- | Construct a word value from a finite sequence of bits.
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   first element of the list will be the most significant bit.
  packWord :: [VBool p] -> VWord p

  -- | Deconstruct a packed word value in to a finite sequence of bits.
  --   NOTE: this produces a list of bits that represent a big-endian word, so
  --   the most significant bit is the first element of the list.
  unpackWord :: VWord p -> [VBool p]

  -- | Concatenate the two given word values.
  --   NOTE: the first argument represents the more-significant bits
  joinWord :: VWord p -> VWord p -> VWord p

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  --   The two integer sizes must sum to the length of the given word value.
  splitWord :: Integer {- ^ left width -} ->
               Integer {- ^ right width -} ->
               VWord p ->
               (VWord p, VWord p)

  -- | Extract a subsequence of bits from a packed word value.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation `extractWord n i w` is equivalent to
  --   first shifting `w` right by `i` bits, and then truncating to
  --   `n` bits.
  extractWord :: Integer {-  ^ Number of bits to take -} ->
                 Integer {- ^ starting bit -} ->
                 VWord p ->
                 VWord p

  -- | 2's complement addition of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordPlus :: VWord p -> VWord p -> VWord p

  -- | 2's complement subtraction of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordMinus :: VWord p -> VWord p -> VWord p

  -- | 2's complement multiplication of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. The high bits of the
  --   multiplication are silently discarded.
  wordMult :: VWord p -> VWord p -> VWord p

  -- | Construct an integer value from the given packed word.
  wordToInt :: VWord p -> VInteger p

  -- | Addition of unbounded integers.
  intPlus :: VInteger p -> VInteger p -> VInteger p

  -- | Subtraction of unbounded integers.
  intMinus :: VInteger p -> VInteger p -> VInteger p

  -- | Multiplication of unbounded integers.
  intMult :: VInteger p -> VInteger p -> VInteger p

  -- | Addition of integers modulo n, for a concrete positive integer n.
  intModPlus :: Integer -> VInteger p -> VInteger p -> VInteger p

  -- | Subtraction of integers modulo n, for a concrete positive integer n.
  intModMinus :: Integer -> VInteger p -> VInteger p -> VInteger p

  -- | Multiplication of integers modulo n, for a concrete positive integer n.
  intModMult :: Integer -> VInteger p -> VInteger p -> VInteger p

  -- | Construct a packed word of the specified width from an integer value.
  wordFromInt :: Integer -> VInteger p -> VWord p

-- | This class defines additional operations necessary to define generic evaluation
--   functions.
class BitWord p => EvalPrims p where
  -- | Eval prim binds primitive declarations to the primitive values that implement them.  Returns 'Nothing' for abstract primitives (i.e., once that are
  -- not implemented by this backend).
  evalPrim :: Decl -> Maybe (GenValue p)

  -- | if/then/else operation.  Choose either the 'then' value or the 'else' value depending
  --   on the value of the test bit.
  iteValue :: VBool p                -- ^ Test bit
           -> Eval (GenValue p)      -- ^ 'then' value
           -> Eval (GenValue p)      -- ^ 'else' value
           -> Eval (GenValue p)


-- Concrete Big-endian Words ------------------------------------------------------------

mask :: Integer  -- ^ Bit-width
     -> Integer  -- ^ Value
     -> Integer  -- ^ Masked result
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)

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

-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: BitWord p => Integer -> Integer -> GenValue p
word n i = VWord n $ ready $ WordVal $ wordLit n i

lam :: (Eval (GenValue p) -> Eval (GenValue p)) -> GenValue p
lam  = VFun

-- | Functions that assume word inputs
wlam :: BitWord p => (VWord p -> Eval (GenValue p)) -> GenValue p
wlam f = VFun (\x -> x >>= fromVWord "wlam" >>= f)

-- | A type lambda that expects a @Type@.
tlam :: (TValue -> GenValue p) -> GenValue p
tlam f = VPoly (return . f)

-- | A type lambda that expects a @Type@ of kind #.
nlam :: (Nat' -> GenValue p) -> GenValue p
nlam f = VNumPoly (return . f)

-- | Generate a stream.
toStream :: [GenValue p] -> Eval (GenValue p)
toStream vs =
   VStream <$> infiniteSeqMap (map ready vs)

toFinSeq :: BitWord p => Integer -> TValue -> [GenValue p] -> GenValue p
toFinSeq len elty vs
   | isTBit elty = VWord len $ ready $ WordVal $ packWord $ map fromVBit vs
   | otherwise   = VSeq len $ finiteSeqMap (map ready vs)

-- | This is strict!
boolToWord :: [Bool] -> Value
boolToWord bs = VWord (genericLength bs) $ ready $ WordVal $ packWord bs

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq :: BitWord p => Nat' -> TValue -> [GenValue p] -> Eval (GenValue p)
toSeq len elty vals = case len of
  Nat n -> return $ toFinSeq n elty vals
  Inf   -> toStream vals


-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Nat' -> TValue -> SeqMap p -> GenValue p
mkSeq len elty vals = case len of
  Nat n
    | isTBit elty -> VWord n $ return $ BitsVal $ Seq.fromFunction (fromInteger n) $ \i ->
                        fromVBit <$> lookupSeqMap vals (toInteger i)
    | otherwise   -> VSeq n vals
  Inf             -> VStream vals


-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: GenValue p -> VBool p
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit"]

-- | Extract an integer value.
fromVInteger :: GenValue p -> VInteger p
fromVInteger val = case val of
  VInteger i -> i
  _      -> evalPanic "fromVInteger" ["not an Integer"]

-- | Extract a finite sequence value.
fromVSeq :: GenValue p -> SeqMap p
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence"]

-- | Extract a sequence.
fromSeq :: forall p. BitWord p => String -> GenValue p -> Eval (SeqMap p)
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg]

fromStr :: Value -> Eval String
fromStr (VSeq n vals) =
  traverse (\x -> toEnum . fromInteger <$> (fromWord "fromStr" =<< x)) (enumerateSeqMap n vals)
fromStr _ = evalPanic "fromStr" ["Not a finite sequence"]

fromBit :: GenValue p -> Eval (VBool p)
fromBit (VBit b) = return b
fromBit _ = evalPanic "fromBit" ["Not a bit value"]

fromWordVal :: String -> GenValue p -> Eval (WordValue p)
fromWordVal _msg (VWord _ wval) = wval
fromWordVal msg _ = evalPanic "fromWordVal" ["not a word value", msg]

-- | Extract a packed word.
fromVWord :: BitWord p => String -> GenValue p -> Eval (VWord p)
fromVWord _msg (VWord _ wval) = wval >>= asWordVal
fromVWord msg _ = evalPanic "fromVWord" ["not a word", msg]

vWordLen :: BitWord p => GenValue p -> Maybe Integer
vWordLen val = case val of
  VWord n _wv              -> Just n
  _                        -> Nothing

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return `Nothing`.
tryFromBits :: forall p. BitWord p => [Eval (GenValue p)] -> Maybe (VWord p)
tryFromBits = go id
  where
  go f [] = Just (packWord (f []))
  go f (Ready (VBit b) : vs) = go (f . (b :)) vs
  go _ (_ : _) = Nothing

-- | Turn a value into an integer represented by w bits.
fromWord :: String -> Value -> Eval Integer
fromWord msg val = bvVal <$> fromVWord msg val

-- | Extract a function from a value.
fromVFun :: GenValue p -> (Eval (GenValue p) -> Eval (GenValue p))
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue p -> (TValue -> Eval (GenValue p))
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: GenValue p -> (Nat' -> Eval (GenValue p))
fromVNumPoly val = case val of
  VNumPoly f -> f
  _          -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue p -> [Eval (GenValue p)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue p -> [(Ident, Eval (GenValue p))]
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

-- | Lookup a field in a record.
lookupRecord :: Ident -> GenValue p -> Eval (GenValue p)
lookupRecord f rec = case lookup f (fromVRecord rec) of
  Just val -> val
  Nothing  -> evalPanic "lookupRecord" ["malformed record"]

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

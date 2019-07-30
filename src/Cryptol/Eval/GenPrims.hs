{-# Language DataKinds, LambdaCase, BangPatterns, FlexibleContexts #-}
module Cryptol.Eval.GenPrims where

import qualified Data.Sequence as Seq

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), fromNat, nMul)
import Cryptol.TypeCheck.AST

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Value
import Cryptol.Eval.Class.Arith
import Cryptol.Eval.Type
import Cryptol.Eval.Monad
import Cryptol.Eval.SeqMap


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




--------------------------------------------------------------------------------
-- Words and Sequences


-- | Lifted operation on finite bitsequences.  Used
--   for signed comparisons and arithemtic.
liftWord :: BitWord p
         => (VWord p -> VWord p -> Eval (GenValue p))
         -> GenValue p
liftWord op =
  nlam $ \_n ->
  wlam $ \w1 -> return $
  wlam $ \w2 -> op w1 w2



-- | Indexing operations.
indexPrim ::
  BitWord p =>
  ( Maybe Integer ->
    TValue ->
    SeqMapV p ->
    Seq.Seq (VBool p) ->
    Eval (GenValue p)
  ) ->
  ( Maybe Integer ->
    TValue ->
    SeqMapV p ->
    VWord p ->
    Eval (GenValue p)
  ) ->
  GenValue p
indexPrim bits_op word_op =
  nlam $ \ n  ->
  tlam $ \ a ->
  nlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
      vs <- l >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrim"]
      r >>= \case
         VWord _ w -> w >>= \case
           WordVal w' -> word_op (fromNat n) a vs w'
           BitsVal bs -> bits_op (fromNat n) a vs =<< sequence bs
           LargeBitsVal m xs -> bits_op (fromNat n) a vs . Seq.fromList =<<
                                              sequence (enumerateSeqMap m xs)
         _ -> evalPanic "Expected word value" ["indexPrim"]



updatePrim
     :: BitWord p
     => (Nat' -> TValue -> WordValue p -> WordValue p -> Eval (GenValue p) -> Eval (WordValue p))
     -> (Nat' -> TValue -> SeqMapV p    -> WordValue p -> Eval (GenValue p) -> Eval (SeqMapV p))
     -> GenValue p
updatePrim updateWord updateSeq =
  nlam $ \len ->
  tlam $ \eltTy ->
  nlam $ \_idxLen ->
  lam $ \xs  -> return $
  lam $ \idx -> return $
  lam $ \val -> do
    idx' <- fromWordVal "update" =<< idx
    xs >>= \case
      VWord l w  -> do w' <- delay Nothing w
                       return $ VWord l (w' >>= \w'' -> updateWord len eltTy w'' idx' val)
      VSeq l vs  -> VSeq l  <$> updateSeq len eltTy vs idx' val
      VStream vs -> VStream <$> updateSeq len eltTy vs idx' val
      _ -> evalPanic "Expected sequence value" ["updatePrim"]

-- @[ 0 .. 10 ]@
fromToV :: BitWord p
        => GenValue p
fromToV  =
  nlam $ \ first ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
    let !f = mkLit ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        let len = 1 + (lst' - first')
        in VSeq len $ IndexSeqMap $ \i -> ready $ f (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: BitWord p
            => GenValue p
fromThenToV  =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
  nlam $ \ len   ->
    let !f = mkLit ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        let diff = next' - first'
        in VSeq len' $ IndexSeqMap $ \i -> ready $ f (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]


infFromV :: BitWord p => GenValue p
infFromV =
  tlam $ \ ty ->
  lam  $ \ x' ->
  return $ VStream $ IndexSeqMap $ \i ->
  do x <- x'
     addV ty x =<< intV (integerLit i) ty

infFromThenV :: BitWord p => GenValue p
infFromThenV =
  tlam $ \ ty ->
  lam $ \ first -> return $
  lam $ \ next ->
  do x <- first
     y <- next
     d <- subV ty y x
     return $ VStream $ IndexSeqMap $ \i ->
       addV ty x =<< mulV ty d =<< intV (integerLit i) ty



joinWordVal :: BitWord p =>
            WordValue p -> WordValue p -> WordValue p
joinWordVal (WordVal w1) (WordVal w2)
  | wordLen w1 + wordLen w2 < largeBitSize
  = WordVal $ joinWord w1 w2
joinWordVal (BitsVal xs) (WordVal w2)
  | toInteger (Seq.length xs) + wordLen w2 < largeBitSize
  = BitsVal (xs Seq.>< Seq.fromList (map ready $ unpackWord w2))
joinWordVal (WordVal w1) (BitsVal ys)
  | wordLen w1 + toInteger (Seq.length ys) < largeBitSize
  = BitsVal (Seq.fromList (map ready $ unpackWord w1) Seq.>< ys)
joinWordVal (BitsVal xs) (BitsVal ys)
  | toInteger (Seq.length xs) + toInteger (Seq.length ys) < largeBitSize
  = BitsVal (xs Seq.>< ys)
joinWordVal w1 w2
  = LargeBitsVal (n1+n2) (concatSeqMap n1 (asBitsMap w1) (asBitsMap w2))
 where n1 = wordValueSize w1
       n2 = wordValueSize w2


joinWords :: BitWord p => Integer -> Integer -> SeqMapV p -> Eval (GenValue p)
joinWords nParts nEach xs =
  loop (ready $ WordVal (wordLit 0 0)) (enumerateSeqMap nParts xs)

 where
 loop !wv [] = return $ VWord (nParts * nEach) wv
 loop !wv (w : ws) = do
    w >>= \case
      VWord _ w' -> loop (joinWordVal <$> wv <*> w') ws
      _ -> evalPanic "joinWords: expected word value" []


joinSeq :: BitWord p
        => Nat'
        -> Integer
        -> TValue
        -> SeqMapV p
        -> Eval (GenValue p)

-- Special case for 0 length inner sequences.
joinSeq _parts 0 a _xs
  = return $ zeroV (TVSeq 0 a)

-- finite sequence of words
joinSeq (Nat parts) each TVBit xs
  | parts * each < largeBitSize
  = joinWords parts each xs
  | otherwise
  = do let zs = IndexSeqMap $ \i ->
                  do let (q,r) = divMod i each
                     ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
                     indexWordValue ys (fromInteger r)
       return $ VWord (parts * each) $ ready $ LargeBitsVal (parts * each) zs

-- infinite sequence of words
joinSeq Inf each TVBit xs
  = return $ VStream $ IndexSeqMap $ \i ->
      do let (q,r) = divMod i each
         ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
         VBit <$> indexWordValue ys (fromInteger r)

-- finite or infinite sequence of non-words
joinSeq parts each _a xs
  = return $ vSeq $ IndexSeqMap $ \i -> do
      let (q,r) = divMod i each
      ys <- fromSeq "join seq" =<< lookupSeqMap xs q
      lookupSeqMap ys r
  where
  len = parts `nMul` (Nat each)
  vSeq = case len of
           Inf    -> VStream
           Nat n  -> VSeq n


-- | Join a sequence of sequences into a single sequence.
joinV :: BitWord p
      => Nat'
      -> Integer
      -> TValue
      -> GenValue p
      -> Eval (GenValue p)
joinV parts each a val = joinSeq parts each a =<< fromSeq "joinV" val


splitWordVal :: BitWord p
             => Integer
             -> Integer
             -> WordValue p
             -> (WordValue p, WordValue p)
splitWordVal leftWidth rightWidth (WordVal w) =
  let (lw, rw) = splitWord leftWidth rightWidth w
   in (WordVal lw, WordVal rw)
splitWordVal leftWidth _rightWidth (BitsVal bs) =
  let (lbs, rbs) = Seq.splitAt (fromInteger leftWidth) bs
   in (BitsVal lbs, BitsVal rbs)
splitWordVal leftWidth rightWidth (LargeBitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in (LargeBitsVal leftWidth lxs, LargeBitsVal rightWidth rxs)

splitAtV :: BitWord p
         => Nat'
         -> Nat'
         -> TValue
         -> GenValue p
         -> Eval (GenValue p)
splitAtV front back a val =
  case back of

    Nat rightWidth | aBit -> do
          ws <- delay Nothing (splitWordVal leftWidth rightWidth <$> fromWordVal "splitAtV" val)
          return $ VTuple
                   [ VWord leftWidth  . ready . fst <$> ws
                   , VWord rightWidth . ready . snd <$> ws
                   ]

    Inf | aBit -> do
       vs <- delay Nothing (fromSeq "splitAtV" val)
       ls <- delay Nothing (do m <- fst . splitSeqMap leftWidth <$> vs
                               let ms = map (fromVBit <$>) (enumerateSeqMap leftWidth m)
                               return $ Seq.fromList $ ms)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ return $ VWord leftWidth (BitsVal <$> ls)
                       , VStream <$> rs
                       ]

    _ -> do
       vs <- delay Nothing (fromSeq "splitAtV" val)
       ls <- delay Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ VSeq leftWidth <$> ls
                       , mkSeq back a <$> rs
                       ]

  where
  aBit = isTBit a

  leftWidth = case front of
    Nat n -> n
    _     -> evalPanic "splitAtV" ["invalid `front` len"]


  -- | Extract a subsequence of bits from a @WordValue@.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation `extractWordVal n i w` is equivalent to
  --   first shifting `w` right by `i` bits, and then truncating to
  --   `n` bits.
extractWordVal :: BitWord p
               => Integer
               -> Integer
               -> WordValue p
               -> WordValue p
extractWordVal len start (WordVal w) =
   WordVal $ extractWord len start w
extractWordVal len start (BitsVal bs) =
   BitsVal $ Seq.take (fromInteger len) $
     Seq.drop (Seq.length bs - fromInteger start - fromInteger len) bs
extractWordVal len start (LargeBitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in LargeBitsVal len xs'


-- | Split implementation.
ecSplitV :: BitWord p
         => GenValue p
ecSplitV =
  nlam $ \ parts ->
  nlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
    case (parts, each) of
       (Nat p, Nat e) | isTBit a -> do
          ~(VWord _ val') <- val
          return $ VSeq p $ IndexSeqMap $ \i -> do
            return $ VWord e (extractWordVal e ((p-i-1)*e) <$> val')
       (Inf, Nat e) | isTBit a -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VWord e $ return $ BitsVal $ Seq.fromFunction (fromInteger e) $ \j ->
              let idx = i*e + toInteger j
               in idx `seq` do
                      xs <- val'
                      fromVBit <$> lookupSeqMap xs idx
       (Nat p, Nat e) -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VSeq p $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       (Inf  , Nat e) -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]


reverseV :: BitWord p => GenValue p -> Eval (GenValue p)
reverseV (VSeq n xs) =
  return $ VSeq n $ reverseSeqMap n xs

reverseV (VWord n wv) = return (VWord n (revword <$> wv))
 where
 revword (WordVal w)         = BitsVal $ Seq.reverse $ Seq.fromList
                                                     $ map ready $ unpackWord w
 revword (BitsVal bs)        = BitsVal $ Seq.reverse bs
 revword (LargeBitsVal m xs) = LargeBitsVal m $ reverseSeqMap m xs

reverseV _ =
  evalPanic "reverseV" ["Not a finite sequence"]


transposeV :: BitWord p
           => Nat'
           -> Nat'
           -> TValue
           -> GenValue p
           -> Eval (GenValue p)
transposeV a b c xs
  | isTBit c, Nat na <- a = -- Fin a => [a][b]Bit -> [b][a]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ BitsVal $
          Seq.fromFunction (fromInteger na) $ \ai -> do
            ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> flip indexWordValue bi =<< wv
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | isTBit c, Inf <- a = -- [inf][b]Bit -> [b][inf]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VStream $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap ai =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> VBit . fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip indexWordValue bi =<< wv)
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | otherwise = -- [a][b]c -> [b][a]c
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ aseq $ IndexSeqMap $ \ai -> do
          ys  <- flip lookupSeqMap ai =<< fromSeq "transposeV 1" xs
          z   <- flip lookupSeqMap bi =<< fromSeq "transposeV 2" ys
          return z

 where
  bseq =
        case b of
          Nat nb -> VSeq nb
          Inf    -> VStream
  aseq =
        case a of
          Nat na -> VSeq na
          Inf    -> VStream




ccatV ::
  (Class Show p, BitWord p) => Nat' -> Nat' -> TValue -> Fun 2 (GenValue p)

ccatV _front _back _elty (VWord m l) (VWord n r) =
  return $ VWord (m+n) (joinWordVal <$> l <*> r)

ccatV _front _back _elty (VWord m l) (VStream r) = do
  l' <- delay Nothing l
  return $ VStream $ IndexSeqMap $ \i ->
    if i < m then
      VBit <$> (flip indexWordValue i =<< l')
    else
      lookupSeqMap r (i-m)

ccatV front back elty l r = do
       l'' <- delay Nothing (fromSeq "ccatV left" l)
       r'' <- delay Nothing (fromSeq "ccatV right" r)
       let Nat n = front
       mkSeq (evalTF TCAdd [front,back]) elty <$> return (IndexSeqMap $ \i ->
        if i < n then do
         ls <- l''
         lookupSeqMap ls i
        else do
         rs <- r''
         lookupSeqMap rs (i-n))






-- Literals --------------------------------------------------------------------

-- | Make a numeric literal value at the given type.
mkLit :: BitWord p => TValue -> Integer -> GenValue p
mkLit ty =
  case ty of
    TVInteger                    -> VInteger . integerLit
    TVIntMod _                   -> VInteger . integerLit
    TVSeq w TVBit
      | w >= Arch.maxBigIntWidth -> wordTooWide w
      | otherwise                -> word w
    _                            -> evalPanic "Cryptol.Eval.Prim.evalConst"
                                    [ "Invalid type for number" ]

-- | Make a numeric constant.
ecNumberV :: BitWord p => GenValue p
ecNumberV = nlam $ \valT ->
            tlam $ \ty ->
            case valT of
              Nat v -> mkLit ty v
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show ty
                       ]



-- Integers --------------------------------------------------------------------

-- | Convert a word to a non-negative integer.
ecToIntegerV :: BitWord p => GenValue p
ecToIntegerV =
  nlam $ \ _ ->
  wlam $ \ w -> return $ VInteger (wordToInt w)

-- | Convert an unbounded integer to a packed bitvector.
ecFromIntegerV :: BitWord p => GenValue p
ecFromIntegerV =
  tlam $ \ a ->
  lam  $ \ x ->
  do i <- fromVInteger <$> x
     intV i a

--------------------------------------------------------------------------------
-- Zero class

zeroV :: BitWord p => TValue -> GenValue p
zeroV ty = case ty of

  -- bits
  TVBit ->
    VBit (bitLit False)

  -- integers
  TVInteger ->
    VInteger (integerLit 0)

  -- integers mod n
  TVIntMod _ ->
    VInteger (integerLit 0)

  TVFloat m n -> VFloat (floatZero m n)

  -- sequences
  TVSeq w ety
      | isTBit ety -> word w 0
      | otherwise  -> VSeq w (IndexSeqMap $ \_ -> ready $ zeroV ety)

  TVStream ety ->
    VStream (IndexSeqMap $ \_ -> ready $ zeroV ety)

  -- functions
  TVFun _ bty ->
    lam (\ _ -> ready (zeroV bty))

  -- tuples
  TVTuple tys ->
    VTuple (map (ready . zeroV) tys)

  -- records
  TVRec fields ->
    VRecord [ (f,ready $ zeroV fty) | (f,fty) <- fields ]

  TVAbstract {} -> evalPanic "zeroV" [ "Abstract type not in `Zero`" ]







-- Miscellaneous ---------------------------------------------------------------

errorV :: BitWord p => TValue -> String -> Eval (GenValue p)
errorV ty msg = case ty of
  -- bits
  TVBit      -> cryUserError msg
  TVInteger  -> cryUserError msg
  TVIntMod _ -> cryUserError msg
  TVFloat {} -> cryUserError msg
  TVReal {}  -> cryUserError msg

  -- sequences
  TVSeq w ety
     | isTBit ety -> return $ VWord w $ return $ BitsVal $
                         Seq.replicate (fromInteger w) (cryUserError msg)
     | otherwise  -> return $ VSeq w (IndexSeqMap $ \_ -> errorV ety msg)

  TVStream ety ->
    return $ VStream (IndexSeqMap $ \_ -> errorV ety msg)

  -- functions
  TVFun _ bty ->
    return $ lam (\ _ -> errorV bty msg)

  -- tuples
  TVTuple tys ->
    return $ VTuple (map (flip errorV msg) tys)

  -- records
  TVRec fields ->
    return $ VRecord [ (f,errorV fty msg) | (f,fty) <- fields ]

  TVAbstract {} -> cryUserError msg



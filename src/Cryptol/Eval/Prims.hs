-- |
-- Module      :  Cryptol.Prims.Eval
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Eval.Prims where

import Control.Monad (join)
import Data.Bits (Bits(..))
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import System.Random.TF(seedTFGen)



import Cryptol.TypeCheck.AST
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete
import Cryptol.Eval.Concrete.Float
import Cryptol.Eval.Concrete.BV
import Cryptol.Eval.Concrete.Integer
import Cryptol.Eval.Class.Arith
import Cryptol.Eval.Class.Logic
import Cryptol.Eval.GenPrims
import Cryptol.ModuleSystem.Name (asPrim)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)
import Cryptol.Testing.Random(randomValue)




-- Primitives ------------------------------------------------------------------

instance EvalPrims EvalConc where
  evalPrim Decl { dName = n, .. } =
    do prim <- asPrim n
       Map.lookup prim primTable

  iteValue b t f = if b then t else f


primTable :: Map.Map Ident Value
primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v)) $
  [ ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary addV)

  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary subV)

  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary mulV)

  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    arith2 ArithPrims
                      { arithWord     = liftDivArith div
                      , arithInteger  = liftDivInteger div
                      , arithZ        = \_ -> liftDivInteger div
                      , arithFloat    = \_ _ -> fpArithDiv
                      })

  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    arith2 ArithPrims
                      { arithWord    = liftDivArith mod
                      , arithInteger = liftDivInteger mod
                      , arithZ       = \_ -> liftDivInteger mod
                      , arithFloat   = \_ _ -> fpArithMod
                      })

  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    arith2 ArithPrims
                       { arithWord    = modExp
                       , arithInteger = integerExp
                       , arithZ       = intModExp
                       , arithFloat   = \_ _ -> fpArithExp
                       })

  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    arith1 ArithPrims
                      { arithWord    = liftUnaryArith lg2
                      , arithInteger = integerLg2
                      , arithZ       = \_ -> integerLg2
                      , arithFloat   = \_ _ -> fpArithLg2
                      })

  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    arith1 ArithPrims
                      { arithWord    = liftUnaryArith negate
                      , arithInteger = integerNeg
                      , arithZ       = intModNeg
                      , arithFloat   = \_ _ -> fpArithNegate
                      })

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
                    arith2 ArithPrims
                      { arithWord = liftSigned bvSdiv
                      , arithInteger = liftDivInteger div
                      , arithZ       = \_   -> liftDivInteger div
                      , arithFloat   = \_ _ -> fpArithSDiv
                      })
  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    arith2 ArithPrims
                      { arithWord    = liftSigned bvSrem
                      , arithInteger = liftDivInteger mod
                      , arithZ       = \_ -> liftDivInteger mod
                      , arithFloat   = \_ _ -> fpArithSMod
                      })

  , (">>$"        , {-# SCC "Prelude::(>>$)" #-}
                    sshrV)
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (logicBinary (.&.) (binBV (.&.))))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (logicBinary (.|.) (binBV (.|.))))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (logicBinary xor (binBV xor)))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (logicUnary complement (unaryBV complement)))
  , ("toInteger"  , ecToIntegerV)
  , ("fromInteger", ecFromIntegerV)
  , ("fromZ"      , {-# SCC "Prelude::fromZ" #-}
                    nlam $ \ _modulus ->
                    lam  $ \ x -> x)
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLB shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftRB shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLB rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRB rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("carry"      , {-# SCC "Prelude::carry" #-}
                    carryV)
  , ("scarry"     , {-# SCC "Prelude::scarry" #-}
                    scarryV)
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV)

  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> join (ccatV front back elty <$> l <*> r))

  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim indexFront_bits indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim indexBack_bits indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim updateBack_word updateBack)

  , ("zero"       , {-# SCC "Prelude::zero" #-}
                    tlam zeroV)

  , ("join"       , {-# SCC "Prelude::join" #-}
                    nlam $ \ parts ->
                    nlam $ \ (finNat' -> each)  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                      joinV parts each a =<< x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    ecSplitV)

  , ("splitAt"    , {-# SCC "Prelude::splitAt" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                       splitAtV front back a =<< x)

  , ("fromTo"     , {-# SCC "Prelude::fromTo" #-}
                    fromToV)

  , ("fromThenTo" , {-# SCC "Prelude::fromThenTo" #-}
                    fromThenToV)

  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV)

  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV)

  , ("error"      , {-# SCC "Prelude::error" #-}
                      tlam $ \a ->
                      nlam $ \_ ->
                       lam $ \s -> errorV a =<< (fromStr =<< s))

  , ("reverse"    , {-# SCC "Prelude::reverse" #-}
                    nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV =<< xs)

  , ("transpose"  , {-# SCC "Prelude::transpose" #-}
                    nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV a b c =<< xs)

  , ("random"      , {-# SCC "Prelude::random" #-}
                     tlam $ \a ->
                     wlam $ \(bvVal -> x) -> return $ randomV a x)
  , ("trace"       , {-# SCC "Prelude::trace" #-}
                     nlam $ \_n ->
                     tlam $ \_a ->
                     tlam $ \_b ->
                      lam $ \s -> return $
                      lam $ \x -> return $
                      lam $ \y -> do
                         msg <- fromStr =<< s
                         EvalOpts { evalPPOpts, evalLogger } <- getEvalOpts
                         doc <- ppValue evalPPOpts =<< x
                         yv <- y
                         io $ logPrint evalLogger
                             $ if null msg then doc else text msg <+> doc
                         return yv)
  ] ++ floatPrims





-- Random Values ---------------------------------------------------------------
-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: BitWord p => TValue -> Integer -> GenValue p
randomV ty seed =
  case randomValue (tValTy ty) of
    Nothing -> zeroV ty
    Just gen ->
      -- unpack the seed into four Word64s
      let mask64 = 0xFFFFFFFFFFFFFFFF
          unpack s = fromIntegral (s .&. mask64) : unpack (s `shiftR` 64)
          [a, b, c, d] = take 4 (unpack seed)
      in fst $ gen 100 $ seedTFGen (a, b, c, d)



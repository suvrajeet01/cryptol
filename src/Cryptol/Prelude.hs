-- |
-- Module      :  Cryptol.Prelude
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Compile the prelude into the executable as a last resort

{-# LANGUAGE Safe #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.Prelude (builtInModules,cryptolTcContents) where


import Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as B
import Text.Heredoc (there)
import Data.Map (Map)
import qualified Data.Map as Map

import Cryptol.Utils.Ident(ModName,preludeName,textToModName)

builtInModules :: Map ModName ByteString
builtInModules = Map.fromList
  [ (preludeName, B.pack [there|lib/Cryptol.cry|])
  , (textToModName "Cryptol::Float", B.pack [there|lib/Cryptol/Float.cry|])
  ]

cryptolTcContents :: String
cryptolTcContents = [there|lib/CryptolTC.z3|]


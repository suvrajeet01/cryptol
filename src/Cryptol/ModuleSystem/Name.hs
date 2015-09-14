{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.ModuleSystem.Name where

import Cryptol.Utils.FastString

import GHC.Generics (Generic)
import Control.DeepSeq


type Ident = FastString

pack :: String -> Ident
pack = mkFastString

unpack :: Ident -> String
unpack = fastString

-- | Module names are just namespaces.
--
-- INVARIANT: the list of strings should never be empty in a valid module name.
newtype ModName = ModName [Ident]
                  deriving (Eq,Ord,Show,Generic)

instance NFData ModName


data Name     = Name Ident
              | NewName Pass Int
               deriving (Eq,Ord,Show,Generic)

instance NFData Name

data QName    = QName (Maybe ModName) Name
               deriving (Show,Generic)

instance Eq QName where
  QName mb1 n1 == QName mb2 n2 = n1 == n2 && mb1 == mb2
  QName mb1 n1 /= QName mb2 n2 = n1 /= n2 && mb1 /= mb2

instance Ord QName where
  compare (QName mb1 n1) (QName mb2 n2) =
    case compare n1 n2 of
      EQ -> compare mb1 mb2
      r  -> r

instance NFData QName

unModName :: ModName -> [Ident]
unModName (ModName ns) = ns

mkModName :: [Ident] -> ModName
mkModName ns = ModName ns

preludeName :: ModName
preludeName  = mkModName [mkFastStringText "Cryptol"]
{-# NOINLINE preludeName #-}

mkName :: FastString -> Name
mkName n = Name n

-- XXX It would be nice to also mark this as a name that doesn't need to be
-- resolved, if it's going to be created before renaming.
mkPrim :: String -> QName
mkPrim n = mkQual preludeName (Name (pack n))

asPrim :: QName -> Maybe String
asPrim (QName (Just m) (Name n))
  | m == preludeName = Just (unpack n)
asPrim _ = Nothing

mkQual :: ModName -> Name -> QName
mkQual  = QName . Just

mkUnqual :: Name -> QName
mkUnqual  = QName Nothing

unqual :: QName -> Name
unqual (QName _ n) = n


data Pass = NoPat | MonoValues
  deriving (Eq,Ord,Show,Generic)

instance NFData Pass

{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

-- | A port of GHC's FastString implementation, specialized to Text instead of
-- pointers.
module Cryptol.Utils.FastString (
    FastString(),
    mkFastStringText,
    mkFastStringTextLazy,
    mkFastString,
    fastStringText,
    fastString
  ) where

import           Control.DeepSeq
import           Data.Array (Array, (!))
import           Data.Array.IO (IOArray)
import           Data.Array.MArray (newArray_,writeArray)
import           Data.Array.Unsafe (unsafeFreeze)
import           Data.Bits (shiftL)
import           Data.Char (ord)
import           Data.Foldable (forM_)
import           Data.Function(on)
import           Data.IORef (IORef,newIORef,readIORef,atomicModifyIORef')
import           Data.Ix (range)
import           Data.List (find,elemIndex)
import qualified Data.Monoid as M
import           Data.String (IsString(..))
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import           GHC.Generics (Generic)
import           System.IO.Unsafe (unsafePerformIO)



-- String Table ----------------------------------------------------------------

type Bucket   = IORef [FastString]
type StrArray = Array Int Bucket

data FastStringTable =
  FastStringTable { tUnique :: {-# UNPACK #-} !(IORef Int)
                  , tTable  :: {-# UNPACK #-} !StrArray
                  }

hashTableLen :: Int
hashTableLen  = 4091

mkStringTable :: IO FastStringTable
mkStringTable  =
  do ix  <- newIORef 1

     let ixs = (0,hashTableLen - 1)
     tab <- newArray_ ixs

     forM_ (range ixs) $ \ i ->
       do ref <- newIORef []
          writeArray tab i ref

     -- as the mutable table never escapes this context, the immutable array
     -- will become the only interface to the data.
     arr <- unsafeFreeze (tab :: IOArray Int Bucket)

     return (FastStringTable ix arr)

{-# NOINLINE stringTable #-}
stringTable :: FastStringTable
stringTable  = unsafePerformIO mkStringTable


-- Fast Strings ----------------------------------------------------------------

data FastString =
  FastString { fsUnique :: {-# UNPACK #-} !Int
             , fsString :: {-# UNPACK #-} !T.Text
             } deriving (Generic)

instance Eq FastString where
  (==) = (==) `on` fsUnique
  {-# INLINE (==) #-}

  (/=) = (/=) `on` fsUnique
  {-# INLINE (/=) #-}

instance Ord FastString where
  compare = compare `on` fsUnique
  {-# INLINE compare #-}

instance Show FastString where
  show FastString { .. } = show fsString

instance M.Monoid FastString where
  mempty      = FastString { fsUnique = 0, fsString = mempty }
  mappend a b = mkFastStringText (fsString a `M.mappend` fsString b)

instance IsString FastString where
  fromString = mkFastString
  {-# INLINE fromString #-}

instance NFData FastString


fastStringText :: FastString -> T.Text
fastStringText  = fsString

fastString :: FastString -> String
fastString  = T.unpack . fsString


-- | Make a 'FastString' out of 'T.Text'.
mkFastStringText :: T.Text -> FastString
mkFastStringText str = unsafePerformIO $
  do entries <- readIORef bucket
     case find checkString entries of

       Just fs -> return fs

       Nothing ->
         do fsUnique <- getUid

            atomicModifyIORef' bucket $ \ entries' ->
              let delta = case entries of
                            []  -> entries'
                            l:_ -> case elemIndex l entries' of
                                     Just idx -> take idx entries'
                                     Nothing  -> error "mkFastStringBytes"

               in case find checkString delta of
                    Just fs -> (entries',fs)
                    Nothing -> let fs = FastString { fsString = str, .. }
                                in (fs:entries', fs)

  where

  FastStringTable { .. } = stringTable

  bucket = tTable ! hashStr str

  getUid = atomicModifyIORef' tUnique (\ix -> (ix+1,ix))

  checkString FastString { .. } = fsString == str

-- | Make a 'FastString' out of a 'LT.Text'.
mkFastStringTextLazy :: LT.Text -> FastString
mkFastStringTextLazy lt =
  case LT.toChunks lt of
    []    -> M.mempty
    [str] -> mkFastStringText str
    _     -> mkFastStringText (LT.toStrict lt)

-- | Make a 'FastString' out of a 'String'.
mkFastString :: String -> FastString
mkFastString str = mkFastStringText (T.pack str)


-- Hashing ---------------------------------------------------------------------

-- | Hash a 'T.Text' by summing all of the character values, modulo the size of
-- the string table.
hashStr :: T.Text -> Int
hashStr  = T.foldl' step 0
  where
  step acc c = (fromIntegral (ord c) + acc `shiftL` 7) `rem` hashTableLen

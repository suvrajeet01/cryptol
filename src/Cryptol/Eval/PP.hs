module Cryptol.Eval.PP where


-- | How to pretty print things when evaluating
data PPOpts = PPOpts
  { useAscii     :: Bool
  , useBase      :: Int
  , useInfLength :: Int
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5 }

asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

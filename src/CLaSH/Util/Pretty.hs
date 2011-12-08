module CLaSH.Util.Pretty
  ( module CLaSH.Util.Pretty.Core
  , pprString
  , zEncodeString
  )
where

-- GHC API
import Outputable (Outputable, showSDocDump, showSDoc, ppr)
import Data.Char  (isDigit,ord)
import Numeric    (showHex)

-- Internal Modules
import CLaSH.Util.Pretty.Core
import CLaSH.Util.Pretty.CoreHW

pprString :: (Outputable x) => x -> String
pprString = showSDoc . ppr

type UserString    = String -- As the user typed it
type EncodedString = String -- Encoded form

zEncodeString :: UserString -> EncodedString
zEncodeString cs = go cs
  where
        go []      = []
        go (c:cs)  = encode_digit_ch c ++ go' cs
        go' []     = []
        go' (c:cs) = encode_ch c ++ go' cs

encode_digit_ch :: Char -> EncodedString
encode_digit_ch c | c >= '0' && c <= '9' = encode_as_unicode_char c
encode_digit_ch c | otherwise            = encode_ch c

encode_ch :: Char -> EncodedString
encode_ch c | unencodedChar c = [c]     -- Common case first

-- Constructors
encode_ch '['  = "ZM"
encode_ch ']'  = "ZN"
encode_ch ':'  = "ZC"

-- Variables
encode_ch '&'  = "za"
encode_ch '|'  = "zb"
encode_ch '^'  = "zc"
encode_ch '$'  = "zd"
encode_ch '='  = "ze"
encode_ch '>'  = "zg"
encode_ch '#'  = "zh"
encode_ch '.'  = "zi"
encode_ch '<'  = "zl"
encode_ch '-'  = "zm"
encode_ch '!'  = "zn"
encode_ch '+'  = "zp"
encode_ch '\'' = "zq"
encode_ch '\\' = "zr"
encode_ch '/'  = "zs"
encode_ch '*'  = "zt"
encode_ch '%'  = "zv"
encode_ch c    = encode_as_unicode_char c

encode_as_unicode_char :: Char -> EncodedString
encode_as_unicode_char c = 'z' : if isDigit (head hex_str) then hex_str
                                                           else '0':hex_str
  where hex_str = showHex (ord c) "U"

unencodedChar :: Char -> Bool   -- True for chars that don't need encoding
unencodedChar c   =  c >= 'a' && c <= 'z'
                  || c >= 'A' && c <= 'Z'
                  || c >= '0' && c <= '9'
                  || c == '_' || c == '('
                  || c == ')'

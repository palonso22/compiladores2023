module Encoding (hashTerm) where

import Data.ByteString 
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Lang 
import Crypto.Hash.SHA256 (hash)
import Common (Pos (..))

packStr :: String -> ByteString
packStr = encodeUtf8 . T.pack



hashTerm :: TTerm -> ByteString
hashTerm t = hash $ packStr $ show (mapInfo sPos t)
    where sPos info = (Pos 0 0) -- IMPORTANTE Ver si es la forma correcta para hacerlo
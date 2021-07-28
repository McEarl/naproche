{- generated by Isabelle -}

{-  Title:      Isabelle/Byte_Message.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Byte-oriented messages.

See "$ISABELLE_HOME/src/Pure/PIDE/byte_message.ML"
and "$ISABELLE_HOME/src/Pure/PIDE/byte_message.scala".
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Isabelle.Byte_Message (
    write, write_line,
    read, read_block, trim_line, read_line,
    make_message, write_message, read_message,
    make_line_message, write_line_message, read_line_message,
    read_yxml, write_yxml
  )
where

import Prelude hiding (read)
import Data.Maybe
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Isabelle.UTF8 as UTF8
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML

import Network.Socket (Socket)
import qualified Network.Socket.ByteString as ByteString

import Isabelle.Library hiding (trim_line)
import qualified Isabelle.Value as Value


{- output operations -}

write :: Socket -> [ByteString] -> IO ()
write = ByteString.sendMany

newline :: ByteString
newline = ByteString.singleton 10

write_line :: Socket -> ByteString -> IO ()
write_line socket s = write socket [s, newline]


{- input operations -}

read :: Socket -> Int -> IO ByteString
read socket n = read_body 0 []
  where
    result = ByteString.concat . reverse
    read_body len ss =
      if len >= n then return (result ss)
      else
        (do
          s <- ByteString.recv socket (min (n - len) 8192)
          case ByteString.length s of
            0 -> return (result ss)
            m -> read_body (len + m) (s : ss))

read_block :: Socket -> Int -> IO (Maybe ByteString, Int)
read_block socket n = do
  msg <- read socket n
  let len = ByteString.length msg
  return (if len == n then Just msg else Nothing, len)

trim_line :: ByteString -> ByteString
trim_line s =
  if n >= 2 && at (n - 2) == 13 && at (n - 1) == 10 then ByteString.take (n - 2) s
  else if n >= 1 && (at (n - 1) == 13 || at (n - 1) == 10) then ByteString.take (n - 1) s
  else s
  where
    n = ByteString.length s
    at = ByteString.index s

read_line :: Socket -> IO (Maybe ByteString)
read_line socket = read_body []
  where
    result = trim_line . ByteString.pack . reverse
    read_body bs = do
      s <- ByteString.recv socket 1
      case ByteString.length s of
        0 -> return (if null bs then Nothing else Just (result bs))
        1 ->
          case ByteString.head s of
            10 -> return (Just (result bs))
            b -> read_body (b : bs)


{- messages with multiple chunks (arbitrary content) -}

make_header :: [Int] -> [ByteString]
make_header ns = [UTF8.encode (space_implode "," (map Value.print_int ns)), newline]

make_message :: [ByteString] -> [ByteString]
make_message chunks = make_header (map ByteString.length chunks) ++ chunks

write_message :: Socket -> [ByteString] -> IO ()
write_message socket = write socket . make_message

parse_header :: ByteString -> [Int]
parse_header line =
  let
    res = map Value.parse_nat (space_explode ',' (UTF8.decode line))
  in
    if all isJust res then map fromJust res
    else error ("Malformed message header: " ++ quote (UTF8.decode line))

read_chunk :: Socket -> Int -> IO ByteString
read_chunk socket n = do
  res <- read_block socket n
  return $
    case res of
      (Just chunk, _) -> chunk
      (Nothing, len) ->
        error ("Malformed message chunk: unexpected EOF after " ++
          show len ++ " of " ++ show n ++ " bytes")

read_message :: Socket -> IO (Maybe [ByteString])
read_message socket = do
  res <- read_line socket
  case res of
    Just line -> Just <$> mapM (read_chunk socket) (parse_header line)
    Nothing -> return Nothing


-- hybrid messages: line or length+block (with content restriction)

is_length :: ByteString -> Bool
is_length msg =
  not (ByteString.null msg) && ByteString.all (\b -> 48 <= b && b <= 57) msg

is_terminated :: ByteString -> Bool
is_terminated msg =
  not (ByteString.null msg) && (ByteString.last msg == 13 || ByteString.last msg == 10)

make_line_message :: ByteString -> [ByteString]
make_line_message msg =
  let n = ByteString.length msg in
    if is_length msg || is_terminated msg then
      error ("Bad content for line message:\n" ++ take 100 (UTF8.decode msg))
    else
      (if n > 100 || ByteString.any (== 10) msg then make_header [n + 1] else []) ++
      [msg, newline]

write_line_message :: Socket -> ByteString -> IO ()
write_line_message socket = write socket . make_line_message

read_line_message :: Socket -> IO (Maybe ByteString)
read_line_message socket = do
  opt_line <- read_line socket
  case opt_line of
    Nothing -> return Nothing
    Just line ->
      case Value.parse_nat (UTF8.decode line) of
        Nothing -> return $ Just line
        Just n -> fmap trim_line . fst <$> read_block socket n


read_yxml :: Socket -> IO (Maybe XML.Body)
read_yxml socket = do
  res <- read_line_message socket
  return (YXML.parse_body . UTF8.decode <$> res)

write_yxml :: Socket -> XML.Body -> IO ()
write_yxml socket body =
  write_line_message socket (UTF8.encode (YXML.string_of_body body))

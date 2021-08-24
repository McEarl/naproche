{- generated by Isabelle -}

{-  Title:      Isabelle/Properties.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Property lists.

See "$ISABELLE_HOME/src/Pure/General/properties.ML".
-}

module Isabelle.Properties (Entry, T, defined, get, get_value, put, remove)
where

import qualified Data.List as List
import Isabelle.Bytes (Bytes)


type Entry = (Bytes, Bytes)
type T = [Entry]

defined :: T -> Bytes -> Bool
defined props name = any (\(a, _) -> a == name) props

get :: T -> Bytes -> Maybe Bytes
get props name = List.lookup name props

get_value :: (Bytes -> Maybe a) -> T -> Bytes -> Maybe a
get_value parse props name =
  case get props name of
    Nothing -> Nothing
    Just s -> parse s

put :: Entry -> T -> T
put entry props = entry : remove (fst entry) props

remove :: Bytes -> T -> T
remove name props =
  if defined props name then filter (\(a, _) -> a /= name) props
  else props

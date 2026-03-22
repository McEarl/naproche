-- |
-- Module      : SAD.Export.Representation
-- Copyright   : (c) 2019, Anton Lorenzen
--                   2026, Marcel Schütz
-- License     : GPL-3
--
-- Represent expressions in different formats


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Representation where

import Data.Set (Set)
import Data.Set qualified as Set

import SAD.Helpers (intercalate)

import Isabelle.Bytes


-- | Possible ways an expression can be formatted as.
-- Usefull to render formulas in different formats.
data Format =
    PIDE
  | Console
  | Informal

class Representation a where
  represent :: Format -> a -> Bytes

instance Representation a => Representation [a] where
  represent PIDE xs = "[" <> intercalate ", " (map (represent PIDE) xs) <> "]"
  represent Console xs = "[" <> intercalate ", " (map (represent Console) xs) <> "]"
  represent Informal xs = "[" <> intercalate ", " (map (represent Informal) xs) <> "]"

instance (Representation a, Representation b) => Representation (a,b) where
  represent PIDE (x, y) = "(" <> represent PIDE x <> "," <> represent PIDE y <> ")"
  represent Console (x, y) = "(" <> represent Console x <> "," <> represent Console y <> ")"
  represent Informal (x, y) = "(" <> represent Informal x <> "," <> represent Informal y <> ")"

instance Representation a => Representation (Set a) where
  represent PIDE x =
    let xs = Set.toList x
    in "{" <> intercalate ", " (map (represent PIDE) xs) <> "}"
  represent Console x = 
    let xs = Set.toList x
    in "{" <> intercalate ", " (map (represent Console) xs) <> "}"
  represent Informal x =
    let xs = Set.toList x
    in "{" <> intercalate ", " (map (represent Informal) xs) <> "}"

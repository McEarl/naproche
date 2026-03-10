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

import Isabelle.Bytes


-- | Possible ways an expression can be formatted as.
-- Usefull to render formulas in different formats.
data Format = PIDE

class Representation a where
  represent :: Format -> a -> Bytes

instance Representation a => Representation [a] where
  represent PIDE [] = ""
  represent PIDE (x : xs) =
    "[" <> represent PIDE x <> "," <> represent PIDE xs <> "]"

instance (Representation a, Representation b) => Representation (a,b) where
  represent PIDE (x, y) =
    "(" <> represent PIDE x <> "," <> represent PIDE y <> ")"

instance Representation a => Representation (Set a) where
  represent PIDE x =
    let elements = Set.toList x
    in "{" <> represent PIDE elements <> "}"


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

import SAD.Helpers (failWithMessage)

import Isabelle.Bytes


-- | Possible ways an expression can be formatted as.
-- Usefull to render formulas in different formats.
data Format =
    PIDE
  | TPTP

class Representation a where
  represent :: Format -> a -> Bytes

instance Representation a => Representation [a] where
  -- PIDE
  represent PIDE [] = ""
  represent PIDE (x : xs) =
    "[" <> represent PIDE x <> "," <> represent PIDE xs <> "]"
  -- TPTP
  represent TPTP xs = failWithMessage "SAD.Export.Representation:represent" "TPTP format not implemented for \"[a]\""


instance (Representation a, Representation b) => Representation (a,b) where
  -- PIDE
  represent PIDE (x, y) =
    "(" <> represent PIDE x <> "," <> represent PIDE y <> ")"
  -- TPTP
  represent TPTP xs = failWithMessage "SAD.Export.Representation:represent" "TPTP format not implemented for \"(a,b)\""

instance Representation a => Representation (Set a) where
  -- PIDE
  represent PIDE x =
    let elements = Set.toList x
    in "{" <> represent PIDE elements <> "}"
  -- TPTP
  represent TPTP xs = failWithMessage "SAD.Export.Representation:represent" "TPTP format not implemented for \"Set a\""


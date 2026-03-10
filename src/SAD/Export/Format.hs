-- |
-- Module      : SAD.Export.Format
-- Copyright   : (c) 2026, Marcel Schütz
-- License     : GPL-3
--
-- Formatting Formulas

module SAD.Export.Format where

import Isabelle.Bytes


-- | Possible ways an expression can be formatted as.
-- Usefull to render formulas in different formats.
data Format = PIDE

class Formatable a where
  -- | Render an expression in a given format.
  format :: Format -> a -> Bytes


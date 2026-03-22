-- |
-- Module      : SAD.Export.Export
-- Copyright   : (c) 2026, Marcel Schütz
-- License     : GPL-3
--
-- Exporting blocks to different formats.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Export (
  ExportFormat(..),
  export
) where

import SAD.Data.Text.Block
import SAD.Export.Representation (Format(Console,Informal))
import SAD.Export.TPTP qualified as TPTP
import SAD.Helpers (failWithMessage)

import Isabelle.Bytes (Bytes)
import Isabelle.Library (make_bytes)

data ExportFormat =
    Symbolic
  | Verbal
  | TPTP

sectionToTptpRole :: Section -> TPTP.FormulaRole
sectionToTptpRole Definition = TPTP.Hypothesis
sectionToTptpRole Signature = TPTP.Hypothesis
sectionToTptpRole Axiom = TPTP.Hypothesis
sectionToTptpRole Theorem = TPTP.Conjecture
sectionToTptpRole section = failWithMessage "SAD.Data.Text.Block.showSection" $
  "TPTP format not implemented for \"" ++ show section ++ "\""

-- | Present a block in an export format.
export :: ExportFormat -> Block -> Bytes
export TPTP block@Block{body = b, name = n, kind = k} =
  TPTP.showFofAnnotated (TPTP.makeFofAnnotated (make_bytes n) (sectionToTptpRole k) (formulate block)) <> "\n"
export Symbolic block = showBlock Console 0 block
export Verbal block = showBlock Informal 0 block


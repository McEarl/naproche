-- |
-- Module      : SAD.Data.Rules
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Rules where

import SAD.Data.Formula
import SAD.Export.Representation
import SAD.Helpers (intercalate, failWithMessage)

import Data.Text.Lazy (Text)

import Isabelle.Library


data Rule = Rule {
  left      :: Formula,   -- left side
  right     :: Formula,   -- right side
  condition :: [Formula], -- conditions
  label     :: Text}   -- label

instance Representation Rule where
  -- PIDE
  represent PIDE rl =
    represent PIDE (left rl) <> " = " <> represent PIDE (right rl) <>
    ", Cond: " <> intercalate "," (map (represent PIDE) (condition rl)) <>
    ", Label: " <> make_bytes (label rl)
  -- Console
  represent Console rl =
    represent Console (left rl) <> " = " <> represent Console (right rl) <>
    ", Cond: " <> intercalate "," (map (represent Console) (condition rl)) <>
    ", Label: " <> make_bytes (label rl)
  -- TPTP
  represent TPTP xs = failWithMessage "SAD.Data.Rules:represent" "TPTP format not implemented for \"Rule\""

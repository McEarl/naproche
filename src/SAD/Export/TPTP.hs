-- |
-- Module      : SAD.Export.TPTP
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Print proof task in TPTP syntax.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Formula (Formula)
import SAD.Export.Representation

import Isabelle.Library


data Role =
    Axiom
  | Hypothesis
  | Definition
  | Assumption
  | Lemma
  | Theorem
  | Corollary
  | Conjecture
  | NegatedConjecture
  | Plain
  | Type
  | Interpretation
  | FiDomain
  | FiFunctors
  | FiPredicates
  | Unknown

-- | Render a role.
renderRole :: Role -> Text
renderRole Axiom = "axiom"
renderRole Hypothesis = "hypothesis"
renderRole Definition = "definition"
renderRole Assumption = "assumption"
renderRole Lemma = "lemma"
renderRole Theorem = "theorem"
renderRole Corollary = "corollary"
renderRole Conjecture = "conjecture"
renderRole NegatedConjecture = "negated_conjecture"
renderRole Plain = "plain"
renderRole Type = "type"
renderRole Interpretation = "interpretation"
renderRole FiDomain = "fi_domain"
renderRole FiFunctors = "fi_functors"
renderRole FiPredicates = "fi_predicates"
renderRole Unknown = "unknown"

type Sequent = ([Formula], [Formula])

-- | Render a formula.
renderLogicFormula :: Text -> Role -> Formula -> Text
renderLogicFormula name role formula =
  "fof(m"
  <> (if Text.null name then "_" else name)
  <> ", " <> renderRole role <> ", "
  <> Text.fromStrict (make_text (represent TPTP formula))
  <> ")."

-- | Render a sequent.
renderSequent :: Text -> Role -> Sequent -> Text
renderSequent name role (premises, conclusions) =
  "fof(m"
  <> (if Text.null name then "_" else name)
  <> ", " <> renderRole role <> ", ["
  <> Text.intercalate ", " (map (Text.fromStrict . make_text . represent TPTP) premises)
  <> "] --> ["
  <> Text.intercalate ", " (map (Text.fromStrict . make_text . represent TPTP) conclusions)
  <> "])."


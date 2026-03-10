-- |
-- Module      : SAD.Data.Tag
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Tag where

import SAD.Export.Representation

data Tag =
  Dig | DigMultiSubject | DigMultiPairwise | HeadTerm |
  InductionHypothesis | CaseHypothesis | EqualityChain |
  -- Tags to mark certain parts of map definitions
  GenericMark | Evaluation | Condition | Defined | Domain | Replacement |
  -- Tags to mark parts in map proof tasks
  DomainTask | ExistenceTask | UniquenessTask | ChoiceTask
  deriving (Eq, Ord)

instance Representation Tag where
  represent PIDE Dig = "Dig"
  represent PIDE DigMultiSubject = "DigMultiSublject"
  represent PIDE DigMultiPairwise = "DigMultiPairwise"
  represent PIDE HeadTerm = "HeadTerm"
  represent PIDE InductionHypothesis = "InductionHypothesis"
  represent PIDE CaseHypothesis = "CaseHypothesis"
  represent PIDE EqualityChain = "EqualityChain"
  represent PIDE GenericMark = "GenericMark"
  represent PIDE Evaluation = "Evaluation"
  represent PIDE Condition = "Condition"
  represent PIDE Defined = "Defined"
  represent PIDE Domain = "Domain"
  represent PIDE Replacement = "Replacement"
  represent PIDE DomainTask = "DomainTask"
  represent PIDE ExistenceTask = "ExistenceTask"
  represent PIDE UniquenessTask = "UniquenessTask"
  represent PIDE ChoiceTask = "ChoiceTask"

-- | whether a Tag marks a part in a map proof task
fnTag :: Tag -> Bool
fnTag DomainTask    = True; fnTag ChoiceTask     = True
fnTag ExistenceTask = True; fnTag UniquenessTask = True
fnTag _   = False

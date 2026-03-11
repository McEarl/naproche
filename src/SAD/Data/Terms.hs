-- |
-- Module      : SAD.Data.Terms
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Debug.Trace
import Data.Text.Lazy (Text)

import SAD.Export.Representation
import SAD.Helpers (failureMessage)

import Isabelle.Library


data TermName
  = TermName Text
  | TermSymbolic Text
  | TermNotion Text
  | TermThe Text
  | TermUnaryAdjective Text
  | TermMultiAdjective Text
  | TermUnaryVerb Text
  | TermMultiVerb Text
  | TermTask Int
  | TermEquality
  | TermLess
  | TermThesis
  | TermEmpty
  deriving (Eq, Ord, Show)

termFunction :: TermName
termFunction = TermNotion "Function"

termMap, termSet, termClass, termElement, termObject :: TermName
termMap = TermNotion "Map"
termSet = TermNotion "Set"
termClass = TermNotion "Class"
termObject = TermNotion "Object"
termElement = TermNotion "ElementOf"

termApplication, termDomain, termPair :: TermName
termApplication = TermSymbolic "dtlpdtrp" -- ".(.)"
termDomain = TermSymbolic "zDzozmlpdtrp"  -- "Dom(.)"
termPair = TermSymbolic "lpdtcmdtrp"      -- "(.,.)"

termSplit :: TermName -> (Text -> TermName, Text)
termSplit (TermNotion t) = (TermNotion, t)
termSplit (TermThe t) = (TermThe, t)
termSplit (TermUnaryAdjective t) = (TermUnaryAdjective, t)
termSplit (TermMultiAdjective t) = (TermMultiAdjective, t)
termSplit (TermUnaryVerb t) = (TermUnaryVerb, t)
termSplit (TermMultiVerb t) = (TermMultiVerb, t)
termSplit _ = undefined

instance Representation TermName where
  -- PIDE
  represent PIDE (TermName t) = make_bytes t
  represent PIDE (TermSymbolic t) = "s" <> make_bytes t
  represent PIDE (TermNotion t) = "a" <> make_bytes t
  represent PIDE (TermThe t) = "the" <> make_bytes t
  represent PIDE (TermUnaryAdjective t) = "is" <> make_bytes t
  represent PIDE (TermMultiAdjective t) = "mis" <> make_bytes t
  represent PIDE (TermUnaryVerb t) = "do" <> make_bytes  t
  represent PIDE (TermMultiVerb t) = "mdo" <> make_bytes t
  represent PIDE (TermTask n) = "tsk " <> make_bytes  (show n)
  represent PIDE TermEquality = "="
  represent PIDE TermLess  = "iLess"
  represent PIDE TermThesis = "#TH#"
  represent PIDE TermEmpty = ""
  -- Console
  represent Console t = represent PIDE t
  -- TPTP
  represent TPTP t = represent PIDE t 

data TermId
  = EqualityId
  | LessId
  | ThesisId
  | FunctionId
  | MapId
  | ApplicationId
  | DomainId
  | SetId
  | ClassId
  | ElementId
  | PairId
  | ObjectId
  | NewId -- ^ temporary id given to newly introduced symbols
  | SkolemId Int
  | SpecialId Int
  deriving (Eq, Ord, Show)

specialId :: Int -> TermId
specialId n =
  let msg = failureMessage "SAD.Data.Terms.TermId" "Invalid term ID."
  in case n of
  ( -1) -> trace msg EqualityId
  ( -2) -> trace msg LessId
  ( -3) -> trace msg ThesisId
  ( -4) -> trace msg FunctionId
  ( -5) -> trace msg ApplicationId
  ( -6) -> trace msg DomainId
  ( -7) -> trace msg SetId
  ( -8) -> trace msg ElementId
  ( -9) -> trace msg ClassId
  (-10) -> trace msg PairId
  (-11) -> trace msg ObjectId
  (-12) -> trace msg MapId
  (-15) -> trace msg NewId
  n -> SpecialId n

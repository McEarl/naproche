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
import Data.Text.Lazy qualified as Text

import SAD.Export.Representation
import SAD.Helpers (failureMessage, failWithMessage)

import Isabelle.Bytes (Bytes)
import Isabelle.Library


-- * Patterns

data Pattern =
    Word [Text]
  | Symbol Text
  | Vr
  | Nm
  deriving (Eq, Ord, Show)

instance Representation Pattern where
  represent _ (Word synonyms) = "Word(" <> make_bytes (Text.intercalate ", " synonyms) <> ")"
  represent _ (Symbol symbol) = "Symbol(" <> make_bytes symbol <> ")"
  represent _ Vr = "Variable"
  represent _ Nm = "Name"


-- ** Presenting Patterns Symbolically

showSymbolPatterns :: [Pattern] -> Bytes
showSymbolPatterns = foldr ((<>) . showSymbolPattern) ""

showSymbolPattern :: Pattern -> Bytes
showSymbolPattern (Word []) = failWithMessage "SAD.Data.Terms.showSymbolPattern" "Empty list of synonyms given."
showSymbolPattern (Word (word : _)) = make_bytes word
showSymbolPattern (Symbol symbol) = make_bytes symbol
showSymbolPattern Nm = "."
showSymbolPattern Vr = "."

showWordPatterns :: [Pattern] -> Bytes
showWordPatterns = foldr ((<>) . showWordPattern) ""

showWordPattern :: Pattern -> Bytes
showWordPattern (Word []) = failWithMessage "SAD.Data.Terms.showWordPattern" "Empty list of synonyms given."
showWordPattern (Word (word : _)) = make_bytes . Text.toTitle $ word
showWordPattern (Symbol symbol) = make_bytes symbol
showWordPattern Nm = ""
showWordPattern Vr = ""


-- * Presenting Patterns Verbally

verbalizeSymbolPatterns :: [Pattern] -> Bytes
verbalizeSymbolPatterns = foldr ((<>) . showSymbolPattern) ""

verbalizeSymbolPattern :: Pattern -> Bytes
verbalizeSymbolPattern (Word []) = failWithMessage "SAD.Data.Terms.verbalizeSymbolPattern" "Empty list of synonyms given."
verbalizeSymbolPattern (Word (word : _)) = make_bytes word
verbalizeSymbolPattern (Symbol symbol) = make_bytes symbol
verbalizeSymbolPattern Nm = "_"
verbalizeSymbolPattern Vr = "_"

verbalizeWordPatterns :: [Pattern] -> Bytes
verbalizeWordPatterns = foldr ((<>) . showWordPattern) " "

verbalizeWordPattern :: Pattern -> Bytes
verbalizeWordPattern (Word []) = failWithMessage "SAD.Data.Terms.verbalizeWordPattern" "Empty list of synonyms given."
verbalizeWordPattern (Word (word : _)) = make_bytes word
verbalizeWordPattern (Symbol symbol) = make_bytes symbol
verbalizeWordPattern Nm = "_"
verbalizeWordPattern Vr = "_"


-- * Term Names

data TermName
  = TermSymbolic [Pattern]
  | TermNotion [Pattern]
  | TermThe [Pattern]
  | TermUnaryAdjective [Pattern]
  | TermMultiAdjective [Pattern]
  | TermUnaryVerb [Pattern]
  | TermMultiVerb [Pattern]
  | TermTask Int
  | TermEquality
  | TermLess
  | TermThesis
  deriving (Eq, Ord, Show)

-- | Names of hard-coded notions and functions.
termFunction, termMap, termSet, termClass, termElement, termObject,
  termApplication, termDomain, termPair :: TermName
termFunction = TermNotion [Word ["function"], Nm]
termMap = TermNotion [Word ["map"], Nm]
termSet = TermNotion [Word ["set"], Nm]
termClass = TermNotion [Word ["class"], Nm]
termObject = TermNotion [Word ["object"], Nm]
termElement = TermNotion [Word ["element"], Nm, Word ["of"], Vr]
termApplication = TermThe [Word ["value"], Word["of"], Vr, Word ["under"], Vr]
termDomain = TermThe [Word ["domain"], Word["of"], Vr]
termPair = TermThe [Word ["ordered"], Word["pair"], Word["of"], Vr, Word ["and"], Vr]

instance Representation TermName where
  -- PIDE
  represent PIDE (TermSymbolic patterns) = showSymbolPatterns patterns
  represent PIDE (TermNotion patterns) = "a" <> showWordPatterns patterns
  represent PIDE (TermThe patterns) = "the" <> showWordPatterns patterns
  represent PIDE (TermUnaryAdjective patterns) = "is" <> showWordPatterns patterns
  represent PIDE (TermMultiAdjective patterns) = "mis" <> showWordPatterns patterns
  represent PIDE (TermUnaryVerb patterns) = "do" <> showWordPatterns patterns
  represent PIDE (TermMultiVerb patterns) = "mdo" <> showWordPatterns patterns
  represent PIDE (TermTask n) = "tsk_" <> make_bytes (show n)
  represent PIDE TermEquality = "="
  represent PIDE TermLess = "iLess"
  represent PIDE TermThesis = "thesis"
  -- Console
  represent Console (TermSymbolic patterns) = showSymbolPatterns patterns
  represent Console (TermNotion patterns) = "a" <> showWordPatterns patterns
  represent Console (TermThe patterns) = "the" <> showWordPatterns patterns
  represent Console (TermUnaryAdjective patterns) = "is" <> showWordPatterns patterns
  represent Console (TermMultiAdjective patterns) = "mis" <> showWordPatterns patterns
  represent Console (TermUnaryVerb patterns) = "do" <> showWordPatterns patterns
  represent Console (TermMultiVerb patterns) = "mdo" <> showWordPatterns patterns
  represent Console (TermTask n) = "tsk_" <> make_bytes (show n)
  represent Console TermEquality = "="
  represent Console TermLess = "iLess"
  represent Console TermThesis = "$thesis"
  -- TPTP
  represent TPTP (TermSymbolic patterns) = "symbolic_term_" <> (make_bytes . symEncode . Text.fromStrict . make_text . showSymbolPatterns $ patterns)
  represent TPTP (TermNotion patterns) = "a" <> showWordPatterns patterns
  represent TPTP (TermThe patterns) = "the" <> showWordPatterns patterns
  represent TPTP (TermUnaryAdjective patterns) = "is" <> showWordPatterns patterns
  represent TPTP (TermMultiAdjective patterns) = "mis" <> showWordPatterns patterns
  represent TPTP (TermUnaryVerb patterns) = "do" <> showWordPatterns patterns
  represent TPTP (TermMultiVerb patterns) = "mdo" <> showWordPatterns patterns
  represent TPTP (TermTask _) = failWithMessage "SAD.Data.Term.represent" "TPTP format not implemented for \"TermTask\"."
  represent TPTP TermEquality = "="
  represent TPTP TermLess = "iLess"
  represent TPTP TermThesis = failWithMessage "SAD.Data.Term.represent" "TPTP format not implemented for \"TermThesis\"."
  -- Informal
  represent Informal (TermSymbolic patterns) = verbalizeSymbolPatterns patterns
  represent Informal (TermNotion patterns) = verbalizeWordPatterns patterns
  represent Informal (TermThe patterns) = verbalizeWordPatterns patterns
  represent Informal (TermUnaryAdjective patterns) = verbalizeWordPatterns patterns
  represent Informal (TermMultiAdjective patterns) = verbalizeWordPatterns patterns
  represent Informal (TermUnaryVerb patterns) = verbalizeWordPatterns patterns
  represent Informal (TermMultiVerb patterns) = verbalizeWordPatterns patterns
  represent Informal (TermTask n) = "task #" <> make_bytes (show n)
  represent Informal TermEquality = "_ is equal to _"
  represent Informal TermLess = "_ is inductively less than _"
  represent Informal TermThesis = "the thesis"


-- * Term IDs

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

-- * Encoding Symbolic Term Names

-- | Encode a symbolic term name as a sequence of letters.
symEncode :: Text -> Text
symEncode = Text.concat . map chc . Text.chunksOf 1
  where
    chc :: Text -> Text
    chc "`" = "bq" ; chc "~"  = "tl" ; chc "!" = "ex"
    chc "@" = "at" ; chc "$"  = "dl" ; chc "%" = "pc"
    chc "^" = "cf" ; chc "&"  = "et" ; chc "*" = "as"
    chc "(" = "lp" ; chc ")"  = "rp" ; chc "-" = "mn"
    chc "+" = "pl" ; chc "="  = "eq" ; chc "[" = "lb"
    chc "]" = "rb" ; chc "{"  = "lc" ; chc "}" = "rc"
    chc ":" = "cl" ; chc "\'" = "qt" ; chc "\"" = "dq"
    chc "<" = "ls" ; chc ">"  = "gt" ; chc "/" = "sl"
    chc "?" = "qu" ; chc "\\" = "bs" ; chc "|" = "br"
    chc ";" = "sc" ; chc ","  = "cm" ; chc "." = "dt"
    chc "_" = "us" ; chc "#"  = "hs"
    chc c   = Text.cons 'z' c

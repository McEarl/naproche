-- |
-- Module      : SAD.Export.TPTP
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
--
-- Convert Naproche's representation of first-order formulas
-- to TPTP first-order formulas and linearize the latter.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP (
  makeFofAnnotated,
  makeFofLogicFormula,
  showFofAnnotated,
  showFofLogicFormula,
  FormulaRole(..)
) where

import Prelude hiding (Functor)

import SAD.Data.Formula (Formula(..), TermName(..), VariableName(..), showWordPatterns, showSymbolPatterns)
import SAD.Helpers (intercalate, failWithMessage)

import Naproche.TPTP (atomic_word)

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library (make_bytes)


-- * Converting Formulas to TPTP Expresions

makeFofAnnotated :: Bytes -> FormulaRole -> Formula -> FofAnnotated
makeFofAnnotated name role formula =
  FofAnnotated (makeName name) role (FofFormula_Formula . makeFofLogicFormula $ formula)

-- | Convert a formula to TPTP.
makeFofLogicFormula :: Formula -> FofLogicFormula
makeFofLogicFormula = makeFofLogicFormula' 0

makeFofLogicFormula' :: Int -> Formula -> FofLogicFormula
-- Universal Quantification
makeFofLogicFormula' d (All _ f) =
  FofLogicFormula_Unitary .
  FofUnitaryFormula_Quantified $
  FofQuantifiedFormula
    UniversalQuantification
    (FofVariableList_Unary $ makeBoundVariable d)
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' (d + 1) f)
-- Existential Quantification
makeFofLogicFormula' d (Exi _ f) =
  FofLogicFormula_Unitary .
  FofUnitaryFormula_Quantified $
  FofQuantifiedFormula
    ExistentialQuantification
    (FofVariableList_Unary $ makeBoundVariable d)
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' (d + 1) f)
-- Equivalence
makeFofLogicFormula' d (Iff f g) =
  FofLogicFormula_Binary .
  FofBinaryFormula_Nonassoc $
  FofBinaryNonassoc
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d f)
    Equivalence
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d g)
-- Implication
makeFofLogicFormula' d (Imp f g) =
  FofLogicFormula_Binary .
  FofBinaryFormula_Nonassoc $
  FofBinaryNonassoc
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d f)
    Implication
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d g)
-- Disjunction
makeFofLogicFormula' d (Or f g) =
  FofLogicFormula_Binary .
  FofBinaryFormula_Assoc .
  FofBinaryAssoc_Or $
  FofOrFormula_Binary
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d f)
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d g)
-- Conjunction
makeFofLogicFormula' d (And f g) =
  FofLogicFormula_Binary .
  FofBinaryFormula_Assoc .
  FofBinaryAssoc_And $
  FofAndFormula_Binary
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d f)
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d g)
-- Tagged Formulas
makeFofLogicFormula' d (Tag _ f) =
  makeFofLogicFormula' d f
-- Inequality
makeFofLogicFormula' d (Not t@Trm{trmName = TermEquality, trmArgs = args}) =
  case args of
    [l, r] ->
      FofLogicFormula_Unary .
      FofUnaryFormula_Infix $
      FofInfixUnary
        (makeFofTerm d l)
        Inequality
        (makeFofTerm d r)
    _ -> failWithMessage "SAD.Export.TPTP.makeFofLogicFormula'" "Invalid number of arguments for \"TermEquality\"."
-- Equality
makeFofLogicFormula' d t@Trm{trmName = TermEquality, trmArgs = args} =
  case args of
    [l, r] ->
      FofLogicFormula_Unitary .
      FofUnitaryFormula_Atomic .
      FofAtomicFormula_Defined .
      FofDefinedAtomicFormula_Infix $
      FofDefinedInfixFormula
        (makeFofTerm d l)
        (DefinedInfixPred Equality)
        (makeFofTerm d r)
    _ -> failWithMessage "SAD.Export.TPTP.makeFofLogicFormula'" "Invalid number of arguments for \"TermEquality\"."
-- Negation
makeFofLogicFormula' d (Not f) =
  FofLogicFormula_Unary $
  FofUnaryFormula_Prefix
    Negation
    (FofUnitFormula_Unitary . FofUnitaryFormula_Logic $ makeFofLogicFormula' d f)
-- Truth
makeFofLogicFormula' _ Top =
  FofLogicFormula_Unitary .
  FofUnitaryFormula_Atomic .
  FofAtomicFormula_Defined .
  FofDefinedAtomicFormula_Plain .
  FofDefinedPlainFormula_Prop $
  DefinedProposition_True
-- Falsity
makeFofLogicFormula' _ Bot =
  FofLogicFormula_Unitary .
  FofUnitaryFormula_Atomic .
  FofAtomicFormula_Defined .
  FofDefinedAtomicFormula_Plain .
  FofDefinedPlainFormula_Prop $
  DefinedProposition_False
-- Atomic Formulas
makeFofLogicFormula' d t@Trm{trmName = name, trmArgs = args}
  | null args =
      FofLogicFormula_Unitary .
      FofUnitaryFormula_Atomic .
      FofAtomicFormula_Plain .
      FofPlainAtomicFormula .
      FofPlainTerm_Constant .
      Constant .
      Functor $
      makeAtomicWord name
  | otherwise =
      FofLogicFormula_Unitary .
      FofUnitaryFormula_Atomic .
      FofAtomicFormula_Plain .
      FofPlainAtomicFormula $
      FofPlainTerm_Application
        (Functor . makeAtomicWord $ name)
        (makeFofArguments $ map (makeFofTerm d) args)
makeFofLogicFormula' _ Var{} =
  failWithMessage "SAD.Export.TPTP.makeFofLogicFormula'" "Unexpected \"Var\"."
makeFofLogicFormula' _ Ind{} =
  failWithMessage "SAD.Export.TPTP.makeFofLogicFormula'" "Unexpected \"Ind\"."
makeFofLogicFormula' _ ThisT =
  failWithMessage "SAD.Export.TPTP" "Unexpected \"ThisT\"."


makeFofTerm :: Int -> Formula -> FofTerm
makeFofTerm d t@Trm{trmName = name, trmArgs = args}
  | null args =
      FofTerm_FunctionTerm .
      FofFunctionTerm_Plain .
      FofPlainTerm_Constant .
      Constant .
      Functor $
      makeAtomicWord name
  | otherwise =
      FofTerm_FunctionTerm .
      FofFunctionTerm_Plain $
      FofPlainTerm_Application
        (Functor . makeAtomicWord $ name)
        (makeFofArguments $ map (makeFofTerm d) args)
makeFofTerm d Var{varName = v} =
  FofTerm_Variable $ makeFreeVariable v
makeFofTerm d Ind{indIndex = i} =
  FofTerm_Variable $ makeBoundVariable (d - 1 - i)
makeFofTerm d (Tag _ f) =
  makeFofTerm d f
makeFofTerm _ f = failWithMessage "SAD.Export.TPTP.makeFofTerm" "Unexpected formula."


-- * TPTP Expressions

-- ** Annotated Formulas

-- NOTE: The TPTP specification requires annotated formulas to have an
-- additional entry for optional annotations which we omitted here.

data FofAnnotated = FofAnnotated Name FormulaRole FofFormula

showFofAnnotated :: FofAnnotated -> Bytes
showFofAnnotated (FofAnnotated n r f) =
  "fof(" <> n <> "," <> showFormulaRole r <> "," <> showFofFormula f <> ")."


-- ** Names

type Name = Bytes

makeName :: Bytes -> Name
makeName bs = if Bytes.null bs
  then "_"
  else bs


-- ** Formula Roles

data FormulaRole =
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

showFormulaRole :: FormulaRole -> Bytes
showFormulaRole Axiom = "axiom"
showFormulaRole Hypothesis = "hypothesis"
showFormulaRole Definition = "definition"
showFormulaRole Assumption = "assumption"
showFormulaRole Lemma = "lemma"
showFormulaRole Theorem = "theorem"
showFormulaRole Corollary = "corollary"
showFormulaRole Conjecture = "conjecture"
showFormulaRole NegatedConjecture = "negated_conjecture"
showFormulaRole Plain = "plain"
showFormulaRole Type = "type"
showFormulaRole Interpretation = "interpretation"
showFormulaRole FiDomain = "fi_domain"
showFormulaRole FiFunctors = "fi_functors"
showFormulaRole FiPredicates = "fi_predicates"
showFormulaRole Unknown = "unknown"


-- ** Formulas

data FofFormula =
    FofFormula_Formula FofLogicFormula
  | FofFormula_Sequent FofSequent

showFofFormula :: FofFormula -> Bytes
showFofFormula (FofFormula_Formula f) = showFofLogicFormula f
showFofFormula (FofFormula_Sequent s) = showFofSequent s


-- ** Sequents

data FofSequent =
    FofSequent_Plain [FofLogicFormula] GentzenArrow [FofLogicFormula]
  | FofSequent_Grouped FofSequent

showFofSequent :: FofSequent -> Bytes
showFofSequent (FofSequent_Plain a g c) =
  "[" <> intercalate "," (map showFofLogicFormula a) <> "]" <>
  showGentzenArrow g <>
  "[" <> intercalate "," (map showFofLogicFormula c) <> "]"
showFofSequent (FofSequent_Grouped s) =
  "(" <> showFofSequent s <> ")"
  

-- ** Logic Formulas

data FofLogicFormula =
    FofLogicFormula_Binary FofBinaryFormula
  | FofLogicFormula_Unary FofUnaryFormula
  | FofLogicFormula_Unitary FofUnitaryFormula

-- | Show a TPTP formula.
showFofLogicFormula :: FofLogicFormula -> Bytes
showFofLogicFormula (FofLogicFormula_Binary f) = showFofBinaryFormula f
showFofLogicFormula (FofLogicFormula_Unary f) = showFofUnaryFormula f
showFofLogicFormula (FofLogicFormula_Unitary f) = showFofUnitaryFormula f


-- ** Binary Formulas

data FofBinaryFormula =
    FofBinaryFormula_Nonassoc FofBinaryNonassoc
  | FofBinaryFormula_Assoc FofBinaryAssoc

showFofBinaryFormula :: FofBinaryFormula -> Bytes
showFofBinaryFormula (FofBinaryFormula_Nonassoc f) = showFofBinaryNonassoc f
showFofBinaryFormula (FofBinaryFormula_Assoc f) = showFofBinaryAssoc f


-- ** Unary Formulas

data FofUnaryFormula =
    FofUnaryFormula_Prefix UnaryConnective FofUnitFormula
  | FofUnaryFormula_Infix FofInfixUnary

showFofUnaryFormula :: FofUnaryFormula -> Bytes
showFofUnaryFormula (FofUnaryFormula_Prefix c f) = showUnaryConnective c <> showFofUnitFormula f
showFofUnaryFormula (FofUnaryFormula_Infix f) = showFofInfixUnary f


-- ** Unitary Formulas

data FofUnitaryFormula =
    FofUnitaryFormula_Quantified FofQuantifiedFormula
  | FofUnitaryFormula_Atomic FofAtomicFormula
  | FofUnitaryFormula_Logic FofLogicFormula

showFofUnitaryFormula :: FofUnitaryFormula -> Bytes
showFofUnitaryFormula (FofUnitaryFormula_Quantified f) = showFofQuantifiedFormula f
showFofUnitaryFormula (FofUnitaryFormula_Atomic f) = showFofAtomicFormula f
showFofUnitaryFormula (FofUnitaryFormula_Logic f) =
  "(" <> showFofLogicFormula f <> ")"


-- ** Binary Non-Associative Formulas

data FofBinaryNonassoc = FofBinaryNonassoc FofUnitFormula NonassocConnective FofUnitFormula

showFofBinaryNonassoc :: FofBinaryNonassoc -> Bytes
showFofBinaryNonassoc (FofBinaryNonassoc l c r) =
  showFofUnitFormula l <> showNonassocConnective c <> showFofUnitFormula r


-- ** Binary Associative Formulas

data FofBinaryAssoc =
    FofBinaryAssoc_Or FofOrFormula
  | FofBinaryAssoc_And FofAndFormula

showFofBinaryAssoc :: FofBinaryAssoc -> Bytes
showFofBinaryAssoc (FofBinaryAssoc_Or f) = showFofOrFormula f
showFofBinaryAssoc (FofBinaryAssoc_And f) = showFofAndFormula f


-- ** Unit Formulas

data FofUnitFormula =
    FofUnitFormula_Unitary FofUnitaryFormula
  | FofUnitFormula_Unary FofUnaryFormula

showFofUnitFormula :: FofUnitFormula -> Bytes
showFofUnitFormula (FofUnitFormula_Unitary f) = showFofUnitaryFormula f
showFofUnitFormula (FofUnitFormula_Unary f) = showFofUnaryFormula f


-- ** Infix Unary Formulas

data FofInfixUnary = FofInfixUnary FofTerm InfixInequality FofTerm

showFofInfixUnary :: FofInfixUnary -> Bytes
showFofInfixUnary (FofInfixUnary l i r) =
  showFofTerm l <> showInfixInequality i <> showFofTerm r


-- ** Quantified Formulas

data FofQuantifiedFormula = FofQuantifiedFormula FofQuantifier FofVariableList FofUnitFormula

showFofQuantifiedFormula :: FofQuantifiedFormula -> Bytes
showFofQuantifiedFormula (FofQuantifiedFormula q vs f) =
  showFofQuantifier q <> " [" <> showFofVariableList vs <> "] : " <> showFofUnitFormula f


-- ** Atomic Formulas

data FofAtomicFormula =
    FofAtomicFormula_Plain FofPlainAtomicFormula
  | FofAtomicFormula_Defined FofDefinedAtomicFormula
  | FofAtomicFormula_System FofSystemAtomicFormula

showFofAtomicFormula :: FofAtomicFormula -> Bytes
showFofAtomicFormula (FofAtomicFormula_Plain f) = showFofPlainAtomicFormula f
showFofAtomicFormula (FofAtomicFormula_Defined f) = showFofDefinedAtomicFormula f
showFofAtomicFormula (FofAtomicFormula_System f) = showFofSystemAtomicFormula f


-- ** Disjunctions

data FofOrFormula =
    FofOrFormula_Binary FofUnitFormula FofUnitFormula
  | FofOrFormula_Multary FofOrFormula FofUnitFormula

showFofOrFormula :: FofOrFormula -> Bytes
showFofOrFormula (FofOrFormula_Binary l r) =
  showFofUnitFormula l <> " | " <> showFofUnitFormula r
showFofOrFormula (FofOrFormula_Multary f r) =
  showFofOrFormula f <> " | " <> showFofUnitFormula r


-- ** Conjunctions

data FofAndFormula =
    FofAndFormula_Binary FofUnitFormula FofUnitFormula
  | FofAndFormula_Multary FofAndFormula FofUnitFormula

showFofAndFormula :: FofAndFormula -> Bytes
showFofAndFormula (FofAndFormula_Binary l r) =
  showFofUnitFormula l <> " & " <> showFofUnitFormula r
showFofAndFormula (FofAndFormula_Multary f r) =
  showFofAndFormula f <> " & " <> showFofUnitFormula r


-- ** Terms

data FofTerm =
    FofTerm_FunctionTerm FofFunctionTerm
  | FofTerm_Variable Variable

showFofTerm :: FofTerm -> Bytes
showFofTerm (FofTerm_FunctionTerm t) = showFofFunctionTerm t
showFofTerm (FofTerm_Variable v) = showVariable v


-- ** Variable Lists

data FofVariableList =
    FofVariableList_Unary Variable
  | FofVariableList_Multary Variable FofVariableList

showFofVariableList :: FofVariableList -> Bytes
showFofVariableList (FofVariableList_Unary v) = showVariable v
showFofVariableList (FofVariableList_Multary v vs) =
  showVariable v <> "," <> showFofVariableList vs


-- ** Plain Atomic Formulas

newtype FofPlainAtomicFormula = FofPlainAtomicFormula FofPlainTerm

showFofPlainAtomicFormula :: FofPlainAtomicFormula -> Bytes
showFofPlainAtomicFormula (FofPlainAtomicFormula t) = showFofPlainTerm t


-- ** Defined Atomic Formulas

data FofDefinedAtomicFormula =
    FofDefinedAtomicFormula_Plain FofDefinedPlainFormula
  | FofDefinedAtomicFormula_Infix FofDefinedInfixFormula

showFofDefinedAtomicFormula :: FofDefinedAtomicFormula -> Bytes
showFofDefinedAtomicFormula (FofDefinedAtomicFormula_Plain f) = showFofDefinedPlainFormula f
showFofDefinedAtomicFormula (FofDefinedAtomicFormula_Infix f) = showFofDefinedInfixFormula f


-- ** System Atomic Formulas

newtype FofSystemAtomicFormula = FofSystemAtomicFormula FofSystemTerm

showFofSystemAtomicFormula :: FofSystemAtomicFormula -> Bytes
showFofSystemAtomicFormula (FofSystemAtomicFormula t) = showFofSystemTerm t


-- ** Function Terms

data FofFunctionTerm =
    FofFunctionTerm_Plain FofPlainTerm
  | FofFunctionTerm_Defined FofDefinedTerm
  | FofFunctionTerm_System FofSystemTerm

showFofFunctionTerm :: FofFunctionTerm -> Bytes
showFofFunctionTerm (FofFunctionTerm_Plain t) = showFofPlainTerm t
showFofFunctionTerm (FofFunctionTerm_Defined t) = showFofDefinedTerm t
showFofFunctionTerm (FofFunctionTerm_System t) = showFofSystemTerm t


-- ** Variables

type Variable = Bytes

showVariable :: Variable -> Bytes
showVariable = id

makeBoundVariable :: Int -> Variable
makeBoundVariable n = "W" <> make_bytes (show n)

makeFreeVariable :: VariableName -> Variable
makeFreeVariable (VarConstant s) = atomic_word (make_bytes s)
makeFreeVariable (VarGlobal s) = atomic_word (make_bytes s)
makeFreeVariable _ = failWithMessage "SAD.Export.TPTP.makeFreeVariable" "Unexpected variable name."


-- ** Plain Terms

data FofPlainTerm =
    FofPlainTerm_Constant Constant
  | FofPlainTerm_Application Functor FofArguments

showFofPlainTerm :: FofPlainTerm -> Bytes
showFofPlainTerm (FofPlainTerm_Constant c) = showConstant c
showFofPlainTerm (FofPlainTerm_Application f as) =
  showFunctor f <> "(" <> showFofArguments as <> ")"


-- ** Defined Plain Formulas

data FofDefinedPlainFormula =
    FofDefinedPlainFormula_Plain FofDefinedPlainTerm
  | FofDefinedPlainFormula_Prop DefinedProposition
  | FofDefinedPlainFormula_Pred DefinedPredicate FofArguments

showFofDefinedPlainFormula :: FofDefinedPlainFormula -> Bytes
showFofDefinedPlainFormula (FofDefinedPlainFormula_Plain t) = showFofDefinedPlainTerm t
showFofDefinedPlainFormula (FofDefinedPlainFormula_Prop p) = showDefinedProposition p
showFofDefinedPlainFormula (FofDefinedPlainFormula_Pred p as) =
  showDefinedPredicate p <> "(" <> showFofArguments as <> ")"


-- ** Defined Infix Formulas

data FofDefinedInfixFormula = FofDefinedInfixFormula FofTerm DefinedInfixPred FofTerm

showFofDefinedInfixFormula :: FofDefinedInfixFormula -> Bytes
showFofDefinedInfixFormula (FofDefinedInfixFormula l p r) =
  showFofTerm l <> showDefinedInfixPred p <> showFofTerm r


-- ** System Terms

data FofSystemTerm =
    FofSystemTerm_Constant SystemConstant
  | FofSystemTerm_Application SystemFunctor FofArguments

showFofSystemTerm :: FofSystemTerm -> Bytes
showFofSystemTerm (FofSystemTerm_Constant c) = showSystemConstant c
showFofSystemTerm (FofSystemTerm_Application f as) =
  showSystemFunctor f <> "(" <> showFofArguments as <> ")"


-- ** Defined Terms

data FofDefinedTerm =
    FofDefinedTerm_Term DefinedTerm
  | FofDefinedTerm_AtomicTerm FofDefinedAtomicTerm

showFofDefinedTerm :: FofDefinedTerm -> Bytes
showFofDefinedTerm (FofDefinedTerm_Term t) = showDefinedTerm t
showFofDefinedTerm (FofDefinedTerm_AtomicTerm t) = showFofDefinedAtomicTerm t


-- ** Constants

newtype Constant = Constant Functor

showConstant :: Constant -> Bytes
showConstant (Constant f) = showFunctor f


-- ** Functors

newtype Functor = Functor AtomicWord

showFunctor :: Functor -> Bytes
showFunctor (Functor w) = showAtomicWord w


-- ** Arguments

data FofArguments =
    FofArguments_Unary FofTerm
  | FofArguments_Multary FofTerm FofArguments

showFofArguments :: FofArguments -> Bytes
showFofArguments (FofArguments_Unary t) = showFofTerm t
showFofArguments (FofArguments_Multary t as) =
  showFofTerm t <> "," <> showFofArguments as

makeFofArguments :: [FofTerm] -> FofArguments
makeFofArguments [] = failWithMessage "SAD.Export.TPTP.makeFofArguments" "Empty argument list."
makeFofArguments [t] = FofArguments_Unary t
makeFofArguments (t : ts) = FofArguments_Multary t (makeFofArguments ts)


-- ** Defined Plain Terms

data FofDefinedPlainTerm =
    FofDefinedPlainTerm_Constant DefinedConstant
  | FofDefinedPlainTerm_Application DefinedFunctor FofArguments

showFofDefinedPlainTerm :: FofDefinedPlainTerm -> Bytes
showFofDefinedPlainTerm (FofDefinedPlainTerm_Constant c) = showDefinedConstant c
showFofDefinedPlainTerm (FofDefinedPlainTerm_Application f as) =
  showDefinedFunctor f <> "(" <> showFofArguments as <> ")"


-- ** Defined Propositions

data DefinedProposition =
    DefinedProposition_Pred DefinedPredicate
  | DefinedProposition_True
  | DefinedProposition_False

showDefinedProposition :: DefinedProposition -> Bytes
showDefinedProposition (DefinedProposition_Pred p) = showDefinedPredicate p
showDefinedProposition DefinedProposition_True = "$true"
showDefinedProposition DefinedProposition_False = "$false"


-- ** Defined Predicates

data DefinedPredicate =
    DefinedPredicate_Atomic AtomicDefinedWord
  | DefinedPredicate_Distinct
  | DefinedPredicate_Less
  | DefinedPredicate_Lesseq
  | DefinedPredicate_Greater
  | DefinedPredicate_Greatereq
  | DefinedPredicate_IsInt
  | DefinedPredicate_IsRat

showDefinedPredicate :: DefinedPredicate -> Bytes
showDefinedPredicate (DefinedPredicate_Atomic w) = showAtomicDefinedWord w
showDefinedPredicate DefinedPredicate_Distinct = "$distinct"
showDefinedPredicate DefinedPredicate_Less = "$less"
showDefinedPredicate DefinedPredicate_Lesseq = "$lesseq"
showDefinedPredicate DefinedPredicate_Greater = "$greater"
showDefinedPredicate DefinedPredicate_Greatereq = "$greatereq"
showDefinedPredicate DefinedPredicate_IsInt = "$is_int"
showDefinedPredicate DefinedPredicate_IsRat = "$is_rat"


-- ** Defined Infix Predicates

newtype DefinedInfixPred = DefinedInfixPred InfixEquality

showDefinedInfixPred :: DefinedInfixPred -> Bytes
showDefinedInfixPred (DefinedInfixPred e) = showInfixEquality e


-- ** System Constants

newtype SystemConstant = SystemConstant SystemFunctor

showSystemConstant :: SystemConstant -> Bytes
showSystemConstant (SystemConstant f) = showSystemFunctor f


-- ** System Functors

newtype SystemFunctor = SystemFunctor AtomicSystemWord

showSystemFunctor :: SystemFunctor -> Bytes
showSystemFunctor (SystemFunctor w) = showAtomicSystemWord w


-- ** Defined Terms

type DefinedTerm = Bytes

showDefinedTerm :: DefinedTerm -> Bytes
showDefinedTerm = id


-- ** Defined Atomic Terms

newtype FofDefinedAtomicTerm = FofDefinedAtomicTerm FofDefinedPlainTerm

showFofDefinedAtomicTerm :: FofDefinedAtomicTerm -> Bytes
showFofDefinedAtomicTerm (FofDefinedAtomicTerm t) = showFofDefinedPlainTerm t


-- ** Atomic Words

type AtomicWord = Bytes

showAtomicWord :: AtomicWord -> Bytes
showAtomicWord = id

makeAtomicWord :: TermName -> AtomicWord
makeAtomicWord (TermSymbolic patterns) =
  atomic_word . showSymbolPatterns $ patterns
makeAtomicWord (TermNotion patterns) =
  "a" <> showWordPatterns patterns
makeAtomicWord (TermThe patterns) =
  "the" <> showWordPatterns patterns
makeAtomicWord (TermUnaryAdjective patterns) =
  "is" <> showWordPatterns patterns
makeAtomicWord (TermBinaryAdjective patterns) =
  "are" <> showWordPatterns patterns
makeAtomicWord (TermUnaryVerb patterns) =
  "does" <> showWordPatterns patterns
makeAtomicWord (TermBinaryVerb patterns) =
  "do" <> showWordPatterns patterns
makeAtomicWord TermLess =
  "iLess"
makeAtomicWord (TermTask _) =
  failWithMessage "SAD.Export.TPTP.makeAtomicWord" "Unexpected \"TermTask\"."
makeAtomicWord TermEquality =
  failWithMessage "SAD.Export.TPTP.makeAtomicWord" "Unexpected \"TermEquality\"."
makeAtomicWord TermThesis =
  failWithMessage "SAD.Export.TPTP.makeAtomicWord" "Unexpected \"TermThesis\"."


-- ** Defined Constants

newtype DefinedConstant = DefinedConstant DefinedFunctor

showDefinedConstant :: DefinedConstant -> Bytes
showDefinedConstant (DefinedConstant f) = showDefinedFunctor f


-- ** Defined Functors

data DefinedFunctor =
    DefinedFunctor_Word AtomicDefinedWord
  | DefinedFunctor_Uminus
  | DefinedFunctor_Sum
  | DefinedFunctor_Difference
  | DefinedFunctor_Product
  | DefinedFunctor_Quotient
  | DefinedFunctor_QuotientE
  | DefinedFunctor_QuotientT
  | DefinedFunctor_QuotientF
  | DefinedFunctor_RemainderE
  | DefinedFunctor_RemainderT
  | DefinedFunctor_RemainderF
  | DefinedFunctor_Floor
  | DefinedFunctor_Ceiling
  | DefinedFunctor_Truncate
  | DefinedFunctor_Round
  | DefinedFunctor_ToInt
  | DefinedFunctor_ToRat
  | DefinedFunctor_ToReal

showDefinedFunctor :: DefinedFunctor -> Bytes
showDefinedFunctor (DefinedFunctor_Word w) = showAtomicDefinedWord w
showDefinedFunctor DefinedFunctor_Uminus = "$uminus"
showDefinedFunctor DefinedFunctor_Sum = "$sum"
showDefinedFunctor DefinedFunctor_Difference = "$difference"
showDefinedFunctor DefinedFunctor_Product = "$product"
showDefinedFunctor DefinedFunctor_Quotient = "$quotient"
showDefinedFunctor DefinedFunctor_QuotientE = "$quotient_e"
showDefinedFunctor DefinedFunctor_QuotientT = "$quotient_t"
showDefinedFunctor DefinedFunctor_QuotientF = "$quotient_f"
showDefinedFunctor DefinedFunctor_RemainderE = "$remainder_e"
showDefinedFunctor DefinedFunctor_RemainderT = "$remainder_t"
showDefinedFunctor DefinedFunctor_RemainderF = "$remainder_f"
showDefinedFunctor DefinedFunctor_Floor = "$floor"
showDefinedFunctor DefinedFunctor_Ceiling = "$ceiling"
showDefinedFunctor DefinedFunctor_Truncate = "$truncate"
showDefinedFunctor DefinedFunctor_Round = "$round"
showDefinedFunctor DefinedFunctor_ToInt = "$to_int"
showDefinedFunctor DefinedFunctor_ToRat = "$to_rat"
showDefinedFunctor DefinedFunctor_ToReal = "$to_real"


-- ** Atomic System Words

newtype AtomicSystemWord = AtomicSystemWord DollarDollarWord

showAtomicSystemWord :: AtomicSystemWord -> Bytes
showAtomicSystemWord (AtomicSystemWord w) = showDollarDollarWord w


-- ** Atomic Defined System Words

newtype AtomicDefinedWord = AtomicDefinedWord DollarWord

showAtomicDefinedWord :: AtomicDefinedWord -> Bytes
showAtomicDefinedWord (AtomicDefinedWord w) = showDollarWord w


-- ** Dollar Dollar Words

newtype DollarDollarWord = DollarDollarWord Bytes

showDollarDollarWord :: DollarDollarWord -> Bytes
showDollarDollarWord (DollarDollarWord bs) = "$$" <> bs


-- ** Dollar Words

newtype DollarWord = DollarWord Bytes

showDollarWord :: DollarWord -> Bytes
showDollarWord (DollarWord bs) = "$" <> bs

-- ** Primitives

data GentzenArrow = GentzenArrow

showGentzenArrow :: GentzenArrow -> Bytes
showGentzenArrow GentzenArrow = "-->"

data NonassocConnective =
    Equivalence
  | Implication
  | ReverseImplication
  | XOR
  | NOR
  | NAND

showNonassocConnective :: NonassocConnective -> Bytes
showNonassocConnective Equivalence = " <=> "
showNonassocConnective Implication = " => "
showNonassocConnective ReverseImplication = " <= "
showNonassocConnective XOR = " <~> "
showNonassocConnective NOR = " ~| "
showNonassocConnective NAND = " ~& "

data FofQuantifier =
    UniversalQuantification
  | ExistentialQuantification

showFofQuantifier :: FofQuantifier -> Bytes
showFofQuantifier UniversalQuantification = "!"
showFofQuantifier ExistentialQuantification = "?"

data UnaryConnective = Negation

showUnaryConnective :: UnaryConnective -> Bytes
showUnaryConnective Negation = "~"

data InfixInequality = Inequality

showInfixInequality :: InfixInequality -> Bytes
showInfixInequality Inequality = "!="

data InfixEquality = Equality

showInfixEquality :: InfixEquality -> Bytes
showInfixEquality Equality = "="


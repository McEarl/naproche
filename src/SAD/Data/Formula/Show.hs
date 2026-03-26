-- |
-- Module      : SAD.Data.Formula.Show
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Show instance for formulas.


{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation

import Isabelle.Position qualified as Position
import Isabelle.Bytes (Bytes)
import Isabelle.Library
import SAD.Helpers (failWithMessage, intercalate, parens, parensIf)


instance Representation Formula where
  represent :: Format -> Formula -> Bytes
  represent fmt = showFormula fmt 0

showFormula :: Format -> Int -> Formula -> Bytes
-- PIDE
--- Quantifier chain:
showFormula PIDE d (All _ f@(All _ _)) = "\\<forall>" <> showBindingVar PIDE d <> parens (showFormula PIDE (d + 1) f)
showFormula PIDE d (All _ f@(Exi _ _)) = "\\<forall>" <> showBindingVar PIDE d <> parens (showFormula PIDE (d + 1) f)
showFormula PIDE d (All _ f@(Not (Exi _ _))) = "\\<forall>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Exi _ f@(All _ _)) = "\\<exists>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Exi _ f@(Exi _ _)) = "\\<exists>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Exi _ f@(Not (Exi _ _))) = "\\<exists>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Not (Exi _ f@(All _ _))) = "\\<nexists>" <> showBindingVar  PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Not (Exi _ f@(Exi _ _))) = "\\<nexists>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (Not (Exi _ f@(Not (Exi _ _)))) = "\\<nexists>" <> showBindingVar  PIDE d <> showFormula PIDE (d + 1) f
--- Single quantifier:
showFormula PIDE d (All _ f) = "\\<forall>" <> showBindingVar  PIDE d <> parens (showFormula PIDE (d + 1) f)
showFormula PIDE d (Exi _ f) = "\\<exists>" <> showBindingVar PIDE d <> parens (showFormula PIDE (d + 1) f)
--- Negated existential quantifier:
showFormula PIDE d (Not (Exi _ f)) = "\\<nexists>" <> showBindingVar  PIDE d <> parens (showFormula PIDE (d + 1) f)
--- Equivalence:
showFormula PIDE d (Iff f g) = showFormulaL PIDE d f <> " \\<Longleftrightarrow> " <> showFormulaR PIDE d g
--- Implication:
showFormula PIDE d (Imp f g) = showFormulaL PIDE d f <> " \\<Longrightarrow> " <> showFormulaR PIDE d g
--- Disjunction chain:
showFormula PIDE d (Or f@(Or _ _) g) = showFormula PIDE d f <> " \\<or> " <> showFormulaR PIDE d g
showFormula PIDE d (Or f g@(Or _ _)) = showFormulaL PIDE d f <> " \\<or> " <> showFormula PIDE d g
--- Disjunction:
showFormula PIDE d (Or  f g) = showFormulaL PIDE d f <> " \\<or> " <> showFormulaR PIDE d g
--- Conjunction chain:
showFormula PIDE d (And f@(And _ _) g) = showFormula PIDE d f <> " \\<and> " <> showFormulaR PIDE d g
showFormula PIDE d (And f g@(And _ _)) = showFormulaL PIDE d f <> " \\<and> " <> showFormula PIDE d g
--- Conjunction:
showFormula PIDE d (And f g) = showFormulaL PIDE d f <> " \\<and> " <> showFormulaR PIDE d g
--- Tagged formula:
showFormula PIDE d (Tag a f) = represent PIDE a <> " \\<Colon> " <> showFormulaR PIDE d f
--- Inequality:
showFormula PIDE d (Not Trm{trmName = TermEquality, trmArgs = [l, r]}) = showFormula PIDE d l <> " \\<noteq> " <> showFormula PIDE d r
--- Negation:
showFormula PIDE d (Not f) = "\\<not>" <> showFormulaR PIDE d f
--- Truth:
showFormula PIDE d Top = "\\<top>"
--- Falsity:
showFormula PIDE d Bot = "\\<bottom>"
--- @ThisT@:
showFormula PIDE d ThisT = "ThisT"
--- Terms:
showFormula PIDE d Trm{trmName = name, trmArgs = args} = showTerm PIDE d name args
--- Free variables:
showFormula PIDE d Var{varName = VarConstant s} = make_bytes s
showFormula PIDE d Var{varName = vName} = make_bytes $ represent PIDE vName
--- De Brujin index:
showFormula PIDE d Ind{indIndex = i}
  | i < d = "v" <> make_bytes (show $ d - i - 1)
  | otherwise = "v?" <> make_bytes (show i)

-- Console
--- Quantifier:
showFormula Console d (All _ f) = "!" <> showBindingVar  Console d <> " " <> parens (showFormula Console (d + 1) f)
showFormula Console d (Exi _ f) = "?" <> showBindingVar Console d <> " " <> parens (showFormula Console (d + 1) f)
--- Equivalence:
showFormula Console d (Iff f g) = showFormulaL Console d f <> " <=> " <> showFormulaR Console d g
--- Implication:
showFormula Console d (Imp f g) = showFormulaL Console d f <> " => " <> showFormulaR Console d g
--- Disjunction chain:
showFormula Console d (Or f@(Or _ _) g) = showFormula Console d f <> " | " <> showFormulaR Console d g
showFormula Console d (Or f g@(Or _ _)) = showFormulaL Console d f <> " | " <> showFormula Console d g
--- Disjunction:
showFormula Console d (Or  f g) = showFormulaL Console d f <> " | " <> showFormulaR Console d g
--- Conjunction chain:
showFormula Console d (And f@(And _ _) g) = showFormula Console d f <> " & " <> showFormulaR Console d g
showFormula Console d (And f g@(And _ _)) = showFormulaL Console d f <> " & " <> showFormula Console d g
--- Conjunction:
showFormula Console d (And f g) = showFormulaL Console d f <> " & " <> showFormulaR Console d g
--- Tagged formula:
showFormula Console d (Tag a f) = represent Console a <> " :: " <> showFormulaR Console d f
--- Negation:
showFormula Console d (Not f) = "~ " <> showFormulaR Console d f
--- Truth:
showFormula Console d Top = "$true"
--- Falsity:
showFormula Console d Bot = "$false"
--- @ThisT@:
showFormula Console d ThisT = "$ThisT"
--- Terms:
showFormula Console d Trm{trmName = name, trmArgs = args} = showTerm Console d name args
--- Free variables:
showFormula Console d Var{varName = VarConstant s} = make_bytes s
showFormula Console d Var{varName = vName} = make_bytes $ represent Console vName
--- De Brujin index:
showFormula Console d Ind{indIndex = i}
  | i < d = "v" <> make_bytes (show $ d - i - 1)
  | otherwise = "v?" <> make_bytes (show i)

-- Informal
--- Quantifier:
showFormula Informal d (All _ f) = "for all " <> showBindingVar  Informal d <> ", " <> parens (showFormula Informal (d + 1) f)
showFormula Informal d (Exi _ f) = "for some " <> showBindingVar Informal d <> ", " <> parens (showFormula Informal (d + 1) f)
--- Equivalence:
showFormula Informal d (Iff f g) = showFormulaL Informal d f <> " iff " <> showFormulaR Informal d g
--- Implication:
showFormula Informal d (Imp f g) = "if " <> showFormula Informal d f <> " then " <> showFormulaR Informal d g
--- Disjunction chain:
showFormula Informal d (Or f@(Or _ _) g) = showFormula Informal d f <> " or " <> showFormulaR Informal d g
showFormula Informal d (Or f g@(Or _ _)) = showFormulaL Informal d f <> " or " <> showFormula Informal d g
--- Disjunction:
showFormula Informal d (Or  f g) = showFormulaL Informal d f <> " or " <> showFormulaR Informal d g
--- Conjunction chain:
showFormula Informal d (And f@(And _ _) g) = showFormula Informal d f <> " and " <> showFormulaR Informal d g
showFormula Informal d (And f g@(And _ _)) = showFormulaL Informal d f <> " and " <> showFormula Informal d g
--- Conjunction:
showFormula Informal d (And f g) = showFormulaL Informal d f <> " and " <> showFormulaR Informal d g
--- Tagged formula:
showFormula Informal d (Tag _ f) = showFormula Informal d f
--- Negation:
showFormula Informal d (Not f) = "it is wrong that " <> showFormulaR Informal d f
--- Truth:
showFormula Informal d Top = "truth holds"
--- Falsity:
showFormula Informal d Bot = "falsity holds"
--- @ThisT@:
showFormula Informal d ThisT = failWithMessage "SAD.Data.Formula.Show.showFormula" "Informal format not implemented for \"ThisT\""
--- Terms:
showFormula Informal d Trm{trmName = name, trmArgs = args} = showTerm Informal d name args
--- Free variables:
showFormula Informal d Var{varName = VarConstant s} = make_bytes s
showFormula Informal d Var{varName = vName} = make_bytes $ represent Informal vName
--- De Brujin index:
showFormula Informal d Ind{indIndex = i}
  | i < d = "v" <> make_bytes (show $ d - i - 1)
  | otherwise = "v?" <> make_bytes (show i)


showTerm :: Format -> Int -> TermName -> [Formula] -> Bytes
-- PIDE
showTerm PIDE d (TermSymbolic patterns) formulas = dive patterns formulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive [Symbol s] _ = make_bytes s
    dive (Symbol s : p@Symbol{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : p@Word{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : ps) fs = make_bytes s <> " " <> dive ps fs
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"Symbolic\" pattern."
    dive [Vr] (f : _) = showFormula PIDE d f
    dive (Vr : ps) (f : fs) = showFormula PIDE d f <> " " <> dive ps fs
    dive (Nm : ps) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermSymbolic\" term."
showTerm PIDE d t@(TermNotion patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE d t@(TermThe patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE d t@(TermUnaryAdjective patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE d t@(TermBinaryAdjective patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE d t@(TermUnaryVerb patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE d t@(TermBinaryVerb patterns) formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE _ t@(TermTask _) _ = represent PIDE t
showTerm PIDE d t@TermEquality [l, r] = showFormula PIDE d l <> " " <> represent PIDE t <> " " <> showFormula PIDE d r
showTerm PIDE _ t@TermEquality _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Invalid number of arguments for \"TermEquality\"."
showTerm PIDE d t@TermLess formulas = represent PIDE t <> showArguments PIDE d formulas
showTerm PIDE _ t@TermThesis _ = represent PIDE t
-- Console
showTerm Console d (TermSymbolic patterns) formulas = dive patterns formulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive [Symbol s] _ = make_bytes s
    dive (Symbol s : p@Symbol{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : p@Word{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : ps) fs = make_bytes s <> " " <> dive ps fs
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"Symbolic\" pattern."
    dive [Vr] (f : _) = showFormula Console d f
    dive (Vr : ps) (f : fs) = showFormula Console d f <> " " <> dive ps fs
    dive (Nm : ps) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermSymbolic\" term."
showTerm Console d t@(TermNotion patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console d t@(TermThe patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console d t@(TermUnaryAdjective patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console d t@(TermBinaryAdjective patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console d t@(TermUnaryVerb patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console d t@(TermBinaryVerb patterns) formulas = represent Console t <> showArguments Console d formulas
showTerm Console _ t@(TermTask _) _ = represent Console t
showTerm Console d t@TermEquality [l, r] = showFormula Console d l <> " " <> represent Console t <> " " <> showFormula Console d r
showTerm Console _ t@TermEquality _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Invalid number of arguments for \"TermEquality\"."
showTerm Console d t@TermLess formulas = represent Console t <> showArguments Console d formulas
showTerm Console _ t@TermThesis _ = represent Console t
-- Informal
showTerm Informal d (TermSymbolic patterns) formulas = dive patterns formulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive [Symbol s] _ = make_bytes s
    dive (Symbol s : p@Symbol{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : p@Word{} : ps) fs = make_bytes s <> dive (p : ps) fs
    dive (Symbol s : ps) fs = make_bytes s <> " " <> dive ps fs
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"Symbolic\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : ps) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermSymbolic\" term."
showTerm Informal d (TermNotion patterns) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermNotion\" term has no arguments."
showTerm Informal d (TermNotion patterns) (nameFormula : formulas) =
  showFormula Informal d nameFormula <>
  " is " <>
  (case patterns of
    (Word (w : _) : _) | beginsWithVowel w -> "an "
    _ -> "a ") <>
  dive patterns formulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive [Word (w : _), Nm] fs = make_bytes w
    dive (Word (w : _) : Nm : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermNotion\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermNotion\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : ps) fs = dive ps fs
    beginsWithVowel :: Text -> Bool
    beginsWithVowel t = case Text.uncons t of
      Nothing -> False
      Just (c, _) -> c `elem` ['a', 'e', 'i', 'o', 'u'] 
showTerm Informal d (TermThe patterns) formulas = "the " <> dive patterns formulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive [Word (w : _), Nm] fs = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermThe\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermThe\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : ps) fs = dive ps fs
showTerm Informal d (TermUnaryAdjective patterns) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermUnaryAdjective\" term has no arguments."
showTerm Informal d (TermUnaryAdjective patterns) (headFormula : tailFormulas) =
  showFormula Informal d headFormula <> " is " <> dive patterns tailFormulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermUnaryAdjective\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermUnaryAdjective\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermUnaryAdjective\" term."
showTerm Informal d (TermBinaryAdjective patterns) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermBinaryAdjective\" term has no arguments."
showTerm Informal d (TermBinaryAdjective patterns) [_] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermBinaryAdjective\" term has only one argument."
showTerm Informal d (TermBinaryAdjective patterns) (headFormula1 : headFormula2 : tailFormulas) =
  showFormula Informal d headFormula1 <> " and " <> showFormula Informal d headFormula2 <> " are " <> dive patterns tailFormulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermBinaryAdjective\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermBinaryAdjective\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermBinaryAdjective\" term."
showTerm Informal d (TermUnaryVerb patterns) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermUnaryVerb\" term has no arguments."
showTerm Informal d (TermUnaryVerb patterns) (headFormula : tailFormulas) =
  showFormula Informal d headFormula <> " " <> dive patterns tailFormulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermUnaryVerb\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermUnaryVerb\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermUnaryVerb\" term."
showTerm Informal d (TermBinaryVerb patterns) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermBinaryVerb\" term has no arguments."
showTerm Informal d (TermBinaryVerb patterns) [_] = failWithMessage "SAD.Data.Formula.Show.showTerm" "\"TermBinaryVerb\" term has only one argument."
showTerm Informal d (TermBinaryVerb patterns) (headFormula1 : headFormula2 : tailFormulas) =
  showFormula Informal d headFormula1 <> " and " <> showFormula Informal d headFormula2 <> " " <> dive patterns tailFormulas
  where
    dive :: [Pattern] -> [Formula] -> Bytes
    dive [] _ = ""
    dive (Word [] : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Empty list of synonyms in \"Word\" pattern."
    dive [Word (w : _)] _ = make_bytes w
    dive (Word (w : _) : ps) fs = make_bytes w <> " " <> dive ps fs
    dive (Symbol _ : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Symbol\" pattern in \"TermBinaryVerb\" term."
    dive (Vr : ps) [] = failWithMessage "SAD.Data.Formula.Show.showTerm" "Fewer arguments than variables in \"TermBinaryVerb\" pattern."
    dive [Vr] (f : _) = showFormula Informal d f
    dive (Vr : ps) (f : fs) = showFormula Informal d f <> " " <> dive ps fs
    dive (Nm : _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Unexpected \"Nm\" pattern in \"TermBinaryVerb\" term."
showTerm Informal _ (TermTask _) _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Informal format not implemented for \"TermTask _\"."
showTerm Informal d TermEquality [l, r] = showFormula Informal d l <> " is equal to " <> showFormula Informal d r
showTerm Informal _ TermEquality _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Invalid number of arguments for \"TermEquality\"."
showTerm Informal d TermLess [l, r] = showFormula Informal d l <> " is inductively less than " <> showFormula Informal d r
showTerm Informal _ TermLess _ = failWithMessage "SAD.Data.Formula.Show.showTerm" "Invalid number of arguments for \"TermLess\"."
showTerm Informal _ TermThesis _ = "the thesis holds"


-- | Show a formula that occurs on the left-hand side of a logical connective.
showFormulaL :: Format -> Int -> Formula -> Bytes
showFormulaL fmt d f = parensIf (isAll f || isExi f || isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula fmt d f)

-- | Show a formula that occurs on the right-hand side of a logical connective.
showFormulaR :: Format -> Int -> Formula -> Bytes
showFormulaR fmt d f = parensIf (isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula fmt d f)

-- | Show the arguments of a formula/term.
showArguments :: Format -> Int -> [Formula] -> Bytes
showArguments _ _ [] = ""
showArguments format d terms =
  let showTerm = showFormula format d
  in "(" <> intercalate "," (map showTerm terms) <> ")"

showBindingVar :: Format -> Int -> Bytes
showBindingVar fmt d = showFormula fmt (d + 1) (Ind 0 Position.none)


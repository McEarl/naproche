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

module SAD.Data.Formula.Show (
  symEncode,
  substitute
) where

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
import SAD.Helpers (failWithMessage, intercalate, parens, parensIf, isAsciiLetter)


instance Representation Formula where
  represent :: Format -> Formula -> Bytes
  represent fmt = showFormula fmt 0

showFormula :: Format -> Int -> Formula -> Bytes
-- PIDE
--- Quantifier chain:
showFormula PIDE d (All _ f@(All _ _)) = "\\<forall>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
showFormula PIDE d (All _ f@(Exi _ _)) = "\\<forall>" <> showBindingVar PIDE d <> showFormula PIDE (d + 1) f
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
--- Thesis:
showFormula PIDE d Trm{trmName = TermThesis} = "thesis"
--- Equality:
showFormula PIDE d Trm{trmName = TermEquality, trmArgs = [l, r]} = showFormula PIDE d l <> " = " <> showFormula PIDE d r
--- Symbolic formula/term:
showFormula PIDE d Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = make_bytes $ decode PIDE (Text.unpack tName) tArgs d ""
--- Non-symbolic formula/term:
showFormula PIDE d Trm{trmName = tName, trmArgs = tArgs} = represent PIDE tName <> showArguments PIDE d tArgs
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
showFormula Console d (Iff f g) = showFormulaL Console d f <> " => " <> showFormulaR Console d g
--- Implication:
showFormula Console d (Imp f g) = showFormulaL Console d f <> " <=> " <> showFormulaR Console d g
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
showFormula Console d (Not f) = "> " <> showFormulaR Console d f
--- Truth:
showFormula Console d Top = "$true"
--- Falsity:
showFormula Console d Bot = "$false"
--- @ThisT@:
showFormula Console d ThisT = "$ThisT"
--- Thesis:
showFormula Console d Trm{trmName = TermThesis} = "$thesis"
--- Equality:
showFormula Console d Trm{trmName = TermEquality, trmArgs = [l, r]} = showFormula Console d l <> " = " <> showFormula Console d r
--- Symbolic formula/term:
showFormula Console d Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = make_bytes $ decode Console (Text.unpack tName) tArgs d ""
--- Non-symbolic formula/term:
showFormula Console d Trm{trmName = tName, trmArgs = tArgs} = represent Console tName <> showArguments Console d tArgs
--- Free variables:
showFormula Console d Var{varName = VarConstant s} = make_bytes s
showFormula Console d Var{varName = vName} = make_bytes $ represent Console vName
--- De Brujin index:
showFormula Console d Ind{indIndex = i}
  | i < d = "v" <> make_bytes (show $ d - i - 1)
  | otherwise = "v?" <> make_bytes (show i)

-- TPTP
showFormula TPTP d (All _ f) =  "( ! " <> binder d f <> ")"
showFormula TPTP d (Exi _ f) = "( ? " <> binder d f <> ")"
showFormula TPTP d (Iff f g) = sinfix d " <=> " f g
showFormula TPTP d (Imp f g) = sinfix d " => " f g
showFormula TPTP d (Or  f g) = sinfix d " | " f g
showFormula TPTP d (And f g) = sinfix d " & " f g
showFormula TPTP d (Tag _ f) = showFormula TPTP d f
showFormula TPTP d (Not f) = "( ~ " <> showFormula TPTP d f <> ")"
showFormula TPTP d Top = "$true"
showFormula TPTP d Bot = "$false"
showFormula TPTP d Trm {trmName = TermEquality, trmArgs = args} =
  case args of
    [l, r] -> sinfix d " = " l r
    _ -> failWithMessage "SAD.Data.Formula.Show:showFormula" "Invalid number of arguments in equality expression"
showFormula TPTP d t@Trm {trmName = name, trmArgs = args}
  | null args = represent TPTP name
  | otherwise = represent TPTP name <> "(" <> intercalate "," (map (showFormula TPTP d) args) <> ")"
showFormula TPTP d Var {varName = v} = represent TPTP v
showFormula TPTP d Ind {indIndex = i} = "W" <> make_bytes (show (d - 1 - i))
showFormula TPTP d ThisT = failWithMessage "SAD.Data.Formula.Show:showFormula" "TPTP format not implemented for \"ThisT\""

sinfix :: Int -> Bytes -> Formula -> Formula -> Bytes
sinfix d o f g  = "(" <> showFormula TPTP d f <> o <> showFormula TPTP d g <> ")"

binder :: Int -> Formula -> Bytes
binder d f = "[" <> showFormula TPTP (d + 1) (Ind 0 Position.none) <> "] : " <> showFormula TPTP (d + 1) f

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

-- | Substitute all @.@ characters in a string by given terms.
substitute :: Format -> String -> [Formula] -> Int -> Bytes
substitute _ s [] _ = make_bytes s
substitute fmt s (t : ts) d = dec s
  where
    dec ('.' : cs) = parensIf (ambig t) (showFormula fmt d t) <> substitute fmt cs ts d
    dec (c : cs@('.' : _)) | isAsciiLetter c = make_bytes [c] <> " " <> dec cs
    dec (c : cs) = make_bytes [c] <> dec cs
    dec [] = ""

    ambig Trm {trmName = TermSymbolic tName} =
      ("." `Text.isPrefixOf` tName && Text.drop 2 tName /= "(.)") ||
      "." `Text.isSuffixOf` tName
    ambig _ = False



decode :: Format -> String -> [Formula] -> Int -> ShowS
decode _ s [] _ = showString (symDecode s)
decode fmt s (t:ts) d = dec s
  where
    dec ('b':'q':cs) = showChar '`' . dec cs
    dec ('t':'l':cs) = showChar '~' . dec cs
    dec ('e':'x':cs) = showChar '!' . dec cs
    dec ('a':'t':cs) = showChar '@' . dec cs
    dec ('d':'l':cs) = showChar '$' . dec cs
    dec ('p':'c':cs) = showChar '%' . dec cs
    dec ('c':'f':cs) = showChar '^' . dec cs
    dec ('e':'t':cs) = showChar '&' . dec cs
    dec ('a':'s':cs) = showChar '*' . dec cs
    dec ('l':'p':cs) = showChar '(' . dec cs
    dec ('r':'p':cs) = showChar ')' . dec cs
    dec ('m':'n':cs) = showChar '-' . dec cs
    dec ('p':'l':cs) = showChar '+' . dec cs
    dec ('e':'q':cs) = showChar '=' . dec cs
    dec ('l':'b':cs) = showChar '[' . dec cs
    dec ('r':'b':cs) = showChar ']' . dec cs
    dec ('l':'c':cs) = showChar '{' . dec cs
    dec ('r':'c':cs) = showChar '}' . dec cs
    dec ('c':'l':cs) = showChar ':' . dec cs
    dec ('q':'t':cs) = showChar '\'' . dec cs
    dec ('d':'q':cs) = showChar '"' . dec cs
    dec ('l':'s':cs) = showChar '<' . dec cs
    dec ('g':'t':cs) = showChar '>' . dec cs
    dec ('s':'l':cs) = showChar '/' . dec cs
    dec ('q':'u':cs) = showChar '?' . dec cs
    dec ('b':'s':cs) = showChar '\\' . dec cs
    dec ('b':'r':cs) = showChar '|' . dec cs
    dec ('s':'c':cs) = showChar ';' . dec cs
    dec ('c':'m':cs) = showChar ',' . dec cs
    dec ('u':'s':cs) = showChar '_' . dec cs
    dec ('h':'s':cs) = showChar '#' . dec cs
    dec ('d':'t':cs) =
      (\x -> make_string (parensIf (ambig t) (showFormula fmt d t)) ++ x) . decode fmt cs ts d
    dec ('z':c:cs@('d':'t':_)) = showChar c . showChar ' ' . dec cs
    dec ('z':c:cs)   = showChar c . dec cs
    dec cs@(':':_)   = showString cs
    dec []           = showString ""
    dec _            = showString s

    ambig Trm {trmName = TermSymbolic tName} | "dt" `Text.isPrefixOf` tName = not $ appPattern (Text.drop 3 tName)
    ambig Trm {trmName = TermSymbolic tName} =
      snd (Text.splitAt (Text.length tName - 2) tName) == "dt"
    ambig _ = False

    -- map application: "(.)"
    appPattern "lpdtrp" = True
    appPattern _ = False
-- Symbolic names

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

symDecode :: String -> String
symDecode s = sname [] s
  where
    sname ac ('b':'q':cs) = sname ('`':ac) cs
    sname ac ('t':'l':cs) = sname ('~':ac) cs
    sname ac ('e':'x':cs) = sname ('!':ac) cs
    sname ac ('a':'t':cs) = sname ('@':ac) cs
    sname ac ('d':'l':cs) = sname ('$':ac) cs
    sname ac ('p':'c':cs) = sname ('%':ac) cs
    sname ac ('c':'f':cs) = sname ('^':ac) cs
    sname ac ('e':'t':cs) = sname ('&':ac) cs
    sname ac ('a':'s':cs) = sname ('*':ac) cs
    sname ac ('l':'p':cs) = sname ('(':ac) cs
    sname ac ('r':'p':cs) = sname (')':ac) cs
    sname ac ('m':'n':cs) = sname ('-':ac) cs
    sname ac ('p':'l':cs) = sname ('+':ac) cs
    sname ac ('e':'q':cs) = sname ('=':ac) cs
    sname ac ('l':'b':cs) = sname ('[':ac) cs
    sname ac ('r':'b':cs) = sname (']':ac) cs
    sname ac ('l':'c':cs) = sname ('{':ac) cs
    sname ac ('r':'c':cs) = sname ('}':ac) cs
    sname ac ('c':'l':cs) = sname (':':ac) cs
    sname ac ('q':'t':cs) = sname ('\'':ac) cs
    sname ac ('d':'q':cs) = sname ('"':ac) cs
    sname ac ('l':'s':cs) = sname ('<':ac) cs
    sname ac ('g':'t':cs) = sname ('>':ac) cs
    sname ac ('s':'l':cs) = sname ('/':ac) cs
    sname ac ('q':'u':cs) = sname ('?':ac) cs
    sname ac ('b':'s':cs) = sname ('\\':ac) cs
    sname ac ('b':'r':cs) = sname ('|':ac) cs
    sname ac ('s':'c':cs) = sname (';':ac) cs
    sname ac ('c':'m':cs) = sname (',':ac) cs
    sname ac ('d':'t':cs) = sname ('.':ac) cs
    sname ac ('u':'s':cs) = sname ('_':ac) cs
    sname ac ('h':'s':cs) = sname ('#':ac) cs
    sname ac ('z':c:cs)   = sname (c:ac) cs
    sname ac cs@(':':_)   = reverse ac ++ cs
    sname ac []           = reverse ac
    sname _ _             = s

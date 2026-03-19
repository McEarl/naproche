-- |
-- Module      : SAD.Structures.StructureTree
-- Copyright   : (c) 2020, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module SAD.Structures.StructureTree where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Tree
import Data.Text.Lazy qualified as Text
import Data.List (foldl', uncons)

import SAD.Data.Formula as Formula
import SAD.Structures.Formula qualified as F
import SAD.Structures.Export qualified as E
import SAD.Structures.Translate qualified as T
import SAD.Data.Text.Block
import SAD.Data.Text.Decl
import SAD.Export.Representation

import Isabelle.Library


data ForthelExpr = ForthelExpr
  { forthelName :: Text
  , forthelAssumptions :: [Formula]
  , forthelTopLevel :: Bool
  , forthelNeedsProof :: Bool
  , forthelCanDeclare :: Bool
  , forthelFormula :: Formula
  } deriving (Eq)

extractBlocks :: ProofText -> Forest ForthelExpr
extractBlocks (ProofTextBlock b) =
  [ Node (ForthelExpr (name b) [] (isTopLevel b) (needsProof b) (canDeclare (kind b)) (formula b))
    (concatMap extractBlocks (body b))]
extractBlocks _ = []

toStatement :: Tree ForthelExpr -> Either Text ForthelExpr
toStatement (Node e xs) = (\(b, x, xs) -> e {forthelNeedsProof = b, forthelFormula = x, forthelAssumptions = xs}) <$> go xs
  where
    go :: Forest ForthelExpr -> Either Text (Bool, Formula, [Formula])
    go [] = Left "Empty theorem."
    go xs = let (ys,y) = unsnoc xs
      in if any (forthelNeedsProof . rootLabel) ys
        then Left "Multiple statements in a theorem are not supported!"
        else Right $
          ( forthelNeedsProof $ rootLabel y
          , forthelFormula $ rootLabel y
          , map (forthelFormula . rootLabel) ys)
    unsnoc xs = (init xs, last xs)

pattern (:\/), (:/\), (:->), (:<->), (:==) :: Formula -> Formula -> Formula
pattern a :\/ b = Or a b
pattern a :/\ b = And a b
pattern a :-> b = Imp a b
pattern a :<-> b = Iff a b
pattern a :== b <- Trm _ [a, b] _ EqualityId

-- TODO: By removing the de-brujin indices,
-- we might end up with wrong bindings of variables.
toDeclaration :: Format -> ForthelExpr -> F.Declaration
toDeclaration fmt (ForthelExpr {..}) =
  let work = go []
      go xs (All d f) = let v = T.pack . make_string . represent fmt $ declName d
        in F.All v (go (v:xs) f)
      go xs (Exi d f) = let v = T.pack . make_string . represent fmt $ declName d
        in F.Exists v (go (v:xs) f)
      go xs (Iff f g) = (go xs f) F.:<-> (go xs g)
      go xs (Imp f g) = (go xs f) F.:-> (go xs g)
      go xs (Or f g) = (go xs f) F.:\/ (go xs g)
      go xs (And f g) = (go xs f) F.:/\ (go xs g)
      go xs (Tag _ f) = go xs f
      go xs (Not f) = (F.Const "not") F.:@ (go xs f)
      go xs Top = F.Top
      go xs Bot = F.Bot
      go xs (Trm _ [f, g] _ EqualityId) = (go xs f) F.:== (go xs g)
      go xs (Trm t@(TermNotion name) args info id) =
        foldl' (F.:@) (F.TyPredicate $ termToText t) (map (go xs) args)
      go xs (Trm t@(TermUnaryAdjective name) args info id) =
        foldl' (F.:@) (F.Predicate $ termToText t) (map (go xs) args)
      go xs (Trm t@(TermMultiAdjective name) args info id) =
        foldl' (F.:@) (F.Predicate $ termToText t) (map (go xs) args)
      go xs (Trm t args info id) =
        foldl' (F.:@) (F.Const (termToText t)) (map (go xs) args)
      go xs (Var name info pos) = F.Variable (varToText fmt name)
      go xs (Ind idx pos) = F.Variable (xs !! idx)
      go xs ThisT = F.Const "ThisT"
  in case forthelNeedsProof of
    True -> F.Conjecture forthelName (map work forthelAssumptions) (work forthelFormula)
    False -> F.Hypothesis forthelName (map work (forthelAssumptions ++ [forthelFormula]))

varToText :: Format -> VariableName -> Text
varToText fmt (VarConstant t) = t
varToText fmt v = T.pack . make_string . represent fmt $ v

patternToText :: Pattern -> Text
patternToText (Word words) = maybe "" fst (uncons words)
patternToText (Symbol symbol) = symbol
patternToText Nm = ""
patternToText Vr = ""

termToText :: TermName -> Text
termToText (TermSymbolic t) = Text.concat $ map patternToText t
termToText (TermNotion t) = Text.concat $ map patternToText t
termToText (TermThe t) = Text.concat $ map patternToText t
termToText (TermUnaryAdjective t) = Text.concat $ map patternToText t
termToText (TermMultiAdjective t) = Text.concat $ map patternToText t
termToText (TermUnaryVerb t) = Text.concat $ map patternToText t
termToText (TermMultiVerb t) = Text.concat $ map patternToText t
termToText t = undefined

toLeanCode :: Format -> [ForthelExpr] -> Text
toLeanCode fmt fs = "axiom omitted {p : Prop} : p\n\n"
  <> E.export (T.translateDoc $ F.Document (map (toDeclaration fmt) fs))

ppForthelExpr :: Format -> ForthelExpr -> String
ppForthelExpr fmt (ForthelExpr {..}) =
  (if forthelNeedsProof then "T " else "A ")
  <> Text.unpack forthelName <> ": " <> make_string (represent fmt (foldr Imp forthelFormula forthelAssumptions))

parens :: String -> String
parens s = "(" ++ s ++ ")"

-- TODO:
-- Fix -> Top in Prime no square, tenth hypothesis
-- Statement after fails to translate

-- |
-- Module      : SAD.ForTheL.Extension
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Language extensions.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Extension (
  funVars,
  notionVars,
  prdVars,
  ignoreNames
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Formula
import SAD.ForTheL.Base
import SAD.Data.Text.Decl
import SAD.Export.Representation

import Isabelle.Library


-- well-formedness check

funVars :: Format -> (Formula, Formula) -> Maybe Text
funVars fmt (f, d) | not ifq   = prdVars fmt (f, d)
               | not idq   = Just $ Text.pack . make_string $ "illegal function alias: " <>  represent fmt d
               | otherwise = prdVars fmt (t {trmArgs = v:trmArgs t}, d)
  where
    ifq = isTrm f && trmName f == TermEquality && isTrm t
    idq = isTrm d && trmName d == TermEquality && not (u `occursIn` p)
    Trm {trmName = TermEquality, trmArgs = [v, t]} = f
    Trm {trmName = TermEquality, trmArgs = [u, p]} = d


notionVars :: Format -> (Formula, Formula) -> Maybe Text
notionVars fmt (f, d) | not isFunction = prdVars fmt (f, d)
               | otherwise      = prdVars fmt (t {trmArgs = v:vs}, d)
  where
    isFunction = isTrm f && trmName f == TermEquality && isTrm t
    Trm {trmName = TermEquality, trmArgs =  [v,t]} = f
    Trm {trmArgs = vs} = t


prdVars :: Format -> (Formula, Formula) -> Maybe Text
prdVars fmt (f, d) | not flat  = Just $ Text.pack . make_string $ "compound expression: " <> represent fmt f
               | otherwise = freeOrOverlapping fmt (fvToVarSet $ free f) d
  where
    flat      = isTrm f && allDistinctVars (trmArgs f)


allDistinctVars :: [Formula] -> Bool
allDistinctVars = disVs []
  where
    disVs ls (Var {varName = v@(VarHidden _)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs ls (Var {varName = v@(VarConstant _)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs _ [] = True
    disVs _ _ = False

ignoreNames :: Formula -> Formula
ignoreNames (All dcl f) = All dcl {declName = VarEmpty} $ ignoreNames f
ignoreNames (Exi dcl f) = Exi dcl {declName = VarEmpty} $ ignoreNames f
ignoreNames f@Trm{}   = f
ignoreNames f         = mapF ignoreNames f

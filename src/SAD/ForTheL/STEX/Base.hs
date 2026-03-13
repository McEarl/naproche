-- |
-- Module      : SAD.ForTheL.STEX.Base
-- Copyright   : (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- ForTheL state (sTeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.STEX.Base (
  addInits
) where

import Data.List (unionBy)

import SAD.Data.Formula
import SAD.ForTheL.Base


-- | Add primitive expressions to the state.
addInits :: FState -> FState
addInits state@FState{symbNotionExpr = sn, cfnExpr = cfn, rfnExpr = rfn, iprExpr = ipr} = state {
    symbNotionExpr = unionBy comparePatterns sn [
        equalSymbNotion,
        elementOfSymbNotion
      ],
    rfnExpr = unionBy comparePatterns rfn [
        applicationFunction
      ],
    cfnExpr = unionBy comparePatterns cfn [
        domFunction,
        pairFunction
      ],
    iprExpr = unionBy comparePatterns ipr [
        equalityPredicate,
        inequalityPredicate,
        inductionPredicate,
        inPredicate,
        notinPredicate
      ]
  }
  where
    -- "\Elem x"
    elementOfSymbNotion = ([Symbol "\\Elem", Vr], \(x:m:_) -> mkElem x m)
    -- "\Eq x"
    equalSymbNotion = ([Symbol "\\Eq", Vr], mkTrm EqualityId TermEquality)
    -- "\Dom(f)"
    domFunction = ([Symbol "\\Dom", Symbol "(", Vr, Symbol ")"], mkDom . head)
    -- "x \Eq y"
    equalityPredicate = ([Symbol "\\Eq"], mkTrm EqualityId TermEquality)
    -- "x \NotEq y"
    inequalityPredicate = ([Symbol "\\NotEq"], Not . mkTrm EqualityId TermEquality)
    -- "x \ILess y"
    inductionPredicate = ([Symbol "\\ILess"], mkTrm LessId TermLess)
    -- "x \Elem y"
    inPredicate = ([Symbol "\\Elem"], \(x:m:_) -> mkElem x m)
    -- "x \NotElem y"
    notinPredicate = ([Symbol "\\NotElem"], \(x:m:_) -> Not $ mkElem x m)
    -- "(x,y)"
    pairFunction = ([Symbol "(", Vr, Symbol ",", Vr, Symbol ")"], \(x:y:_) -> mkPair x y)
    -- "f(x)"
    applicationFunction = ([Symbol "(", Vr, Symbol ")"], \(f:x:_) -> mkApp f x)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'

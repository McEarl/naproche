{- generated by Isabelle -}

{-  Title:      Isabelle/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Support for Isabelle/Pure logic.

See "$ISABELLE_HOME/src/Pure/logic.ML".
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Pure (
  mk_forall, dest_forall, mk_equals, dest_equals, mk_implies, dest_implies
)
where

import qualified Isabelle.Name as Name
import Isabelle.Term

mk_forall :: Free -> Term -> Term; dest_forall :: Name.Context -> Term -> Maybe (Free, Term)
(mk_forall, dest_forall) = binder "Pure.all"

mk_equals :: Typ -> Term -> Term -> Term; dest_equals :: Term -> Maybe (Typ, Term, Term)
(mk_equals, dest_equals) = typed_op2 "Pure.eq"

mk_implies :: Term -> Term -> Term; dest_implies :: Term -> Maybe (Term, Term)
(mk_implies, dest_implies) = op2 "Pure.imp"

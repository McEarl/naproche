-- |
-- Module      : SAD.Data.VarName
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Data.VarName (
  VariableName(..),
  FV,
  unitFV,
  bindVar,
  excludeVars,
  excludeSet,
  IsVar(..),
  fvToVarSet,
  fvFromVarSet,
  isVarHole,
  PosVar(..)
) where

import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Magic (oneShot)
import Data.Text.Lazy (Text)
import Data.Function (on)

import SAD.Core.Message (show_position)
import SAD.Export.Representation
import SAD.Data.Terms (symEncode)
import SAD.Helpers (failWithMessage)

import Isabelle.Position qualified as Position
import Isabelle.Library


-- These names may not reflect what the constructors are used for..
data VariableName
  = VarConstant Text     -- ^ previously starting with x
  | VarHole Text         -- ^ previously starting with ?
  | VarSlot              -- ^ previously !
  | VarU Text            -- ^ previously starting with u
  | VarHidden Int        -- ^ previously starting with h
  | VarAssume Int        -- ^ previously starting with i
  | VarSkolem Int        -- ^ previously starting with o
  | VarTask VariableName -- ^ previously starting with c
  | VarZ Text            -- ^ previously starting with z
  | VarGlobal Text       -- ^ previously starting with w
  | VarEmpty             -- ^ previously ""
  | VarDefault Text      -- ^ everything else
  deriving (Eq, Ord)

isVarHole :: VariableName -> Bool
isVarHole (VarHole _) = True
isVarHole _ = False

instance Representation VariableName where
  -- PIDE
  represent PIDE (VarConstant s) = "x" <> make_bytes s
  represent PIDE (VarHole s) = "?" <> make_bytes s
  represent PIDE VarSlot = "!"
  represent PIDE (VarU s) = "u" <> make_bytes s
  represent PIDE (VarHidden n) = "h" <> make_bytes (show n)
  represent PIDE (VarAssume n) = "i" <> make_bytes (show n)
  represent PIDE (VarSkolem n) = "o" <> make_bytes (show n)
  represent PIDE (VarTask s) = "c" <> represent PIDE s
  represent PIDE (VarZ s) = "z" <> make_bytes s
  represent PIDE (VarGlobal s) = "w" <> make_bytes s
  represent PIDE VarEmpty = ""
  represent PIDE (VarDefault s) = make_bytes s
  -- Console
  represent Console var = represent PIDE var
  -- TPTP
  represent TPTP (VarConstant s) = "local_variable_" <> make_bytes (symEncode s)
  represent TPTP (VarGlobal s) = "global_variable_" <> make_bytes (symEncode s)
  represent TPTP _ = failWithMessage "SAD.Data.VarName.represent" "TPTP format not implemented for \"VariableName\"s other than \"VarConstant\" and \"VarGlobal\""
  -- Informal
  represent Informal (VarConstant s) = make_bytes s
  represent Informal (VarGlobal s) = "w" <> make_bytes s
  represent Informal _ = failWithMessage "SAD.Data.VarName.represent" "Informal format not implemented for \"VariableName\"s other than \"VarConstant\" and \"VarGlobal\""

data PosVar = PosVar
  { posVarName :: VariableName
  , posVarPosition :: Position.T
  }

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

instance Representation PosVar where
  -- PIDE
  represent PIDE (PosVar v pos) =
    "(" <> represent PIDE v <> ", " <> make_bytes (show_position pos) <> ")"
  -- Console
  represent Console (PosVar v pos) =
    "(" <> represent Console v <> ", " <> make_bytes (show_position pos) <> ")"
  -- TPTP
  represent TPTP _ = failWithMessage "SAD.Data.VarName.represent" "TPTP format not implemented for \"PosVar\""
  -- Informal
  represent Informal _ = failWithMessage "SAD.Data.VarName.represent" "Informal format not implemented for \"PosVar\""

class (Ord a, Representation a) => IsVar a where
  buildVar :: VariableName -> Position.T -> a

instance IsVar VariableName where
  buildVar = const

instance IsVar PosVar where
  buildVar = PosVar

-- Free variable traversals, see
-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html
-- for explanation

newtype FV a = FV
  { runFV :: Set VariableName  -- bound variable set
          -> Set a  -- the accumulator
          -> Set a  -- the result
  }

instance Monoid (FV a) where
  mempty = FV $ oneShot $ \_ acc -> acc

instance Semigroup (FV a) where
  fv1 <> fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv1 boundVars (runFV fv2 boundVars acc)

unitFV :: IsVar a => VariableName -> Position.T -> FV a
unitFV v pos = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  if Set.member v boundVars
  then acc
  else Set.insert (buildVar v pos) acc

bindVar :: Ord a => VariableName -> FV a -> FV a
bindVar v fv = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv (Set.insert v boundVars) acc

excludeVars :: Ord a => FV VariableName -> FV a -> FV a
excludeVars fv1 fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv2 (runFV fv1 mempty boundVars) acc

excludeSet :: IsVar a => FV a -> Set VariableName -> FV a
excludeSet fs vs = excludeVars (fvFromVarSet vs) fs

fvFromVarSet :: Ord a => Set a -> FV a
fvFromVarSet vs = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  acc `Set.union` vs

fvToVarSet :: Ord a => FV a -> Set a
fvToVarSet fv = runFV fv mempty mempty

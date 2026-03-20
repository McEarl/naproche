-- |
-- Module      : SAD.Data.Text.Block
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Text.Block (
  ProofText(..),
  Block(..),
  makeBlock,
  position,
  declaredNames,
  text,
  Section(..),
  showForm,
  formulate,
  compose,
  needsProof,
  isTopLevel,
  file,
  parseErrors,
  canDeclare
) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Maybe (fromMaybe)

import SAD.Data.Formula hiding (CaseHypothesis)
import SAD.Data.Instr
import SAD.Parser.Token
import SAD.Data.Text.Decl
import SAD.Parser.Error (ParseError)
import SAD.Export.Representation
import SAD.Helpers (indent)

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Position qualified as Position
import Isabelle.Library (make_text, make_bytes)


data ProofText =
    ProofTextBlock Block
  | ProofTextInstr Position.T Instr
  | ProofTextDrop Position.T Drop
  | ProofTextSynonym Position.T
  | ProofTextPretyping Position.T (Set PosVar)
  | ProofTextMacro Position.T
  | ProofTextError ParseError
  deriving (Eq, Ord)

instance Representation ProofText where
  represent fmt = showProofText fmt 0

showProofText :: Format -> Int -> ProofText -> Bytes
showProofText fmt p (ProofTextBlock block) = showBlock fmt p block
showProofText _ p (ProofTextInstr _ instr) = indent p . make_bytes $ show instr
showProofText _ p (ProofTextDrop _ instr) = indent p . make_bytes $ show instr
showProofText _ p (ProofTextError err) = indent p . make_bytes $ show err
showProofText _ _ _ = ""

data Block = Block {
  formula           :: Formula,
  body              :: [ProofText],
  kind              :: Section,
  declaredVariables :: Set Decl,
  name              :: Text,
  link              :: [Text],
  tokens            :: [Token] }
  deriving (Eq, Ord)

makeBlock :: Formula -> [ProofText] -> Section -> Text -> [Text] -> [Token] -> Block
makeBlock form body kind = Block form body kind mempty

position :: Block -> Position.T
position = Position.range_position . tokensRange . tokens

isTopLevel :: Block -> Bool
isTopLevel = isHole . formula

text :: Block -> Text
text Block {tokens} = composeTokens tokens

{- All possible types that a ForTheL block can have. -}
data Section =
  Definition | Signature | Axiom | Theorem | CaseHypothesis |
  Assumption | Choice | Affirmation | Posit | LowDefinition |
  ProofByContradiction
  deriving (Eq, Ord, Show)

instance Representation Section where
  represent _ Definition = "Definition"
  represent _ Signature = "Signature"
  represent _ Axiom = "Axiom"
  represent _ Theorem = "Theorem"
  represent _ CaseHypothesis = "Case hypothesis"
  represent _ Assumption = "Assumption"
  represent _ Choice = "Choice"
  represent _ Affirmation = "Affirmation"
  represent _ Posit = "Posit"
  represent _ LowDefinition = "Low-level definition"
  represent _ ProofByContradiction = "Proof by contradiction"


-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate block =
  if isTopLevel block then compose $ body block else formula block

compose :: [ProofText] -> Formula
compose = foldr comp Top
  where
    comp (ProofTextBlock block@Block{ declaredVariables = dvs }) f
      -- In this case, we give the formula 'exists x_1,...,x_n . (formulate block) ^ f'.
      | needsProof block || kind block == Posit =
          Set.foldr mkExi (blAnd (formulate block) f) $ Set.map declName dvs
      -- Otherwise, we give the formula 'forall x_1,...,x_n . (formulate block) => f'.
      | otherwise = Set.foldr mkAll (blImp (formulate block) f) $ Set.map declName dvs
    comp _ fb = fb



{- necessity of proof as derived from the block type -}
needsProof :: Block -> Bool
needsProof block = sign $ kind block
  where
    sign Definition = False
    sign Signature  = False
    sign Axiom      = False
    sign Assumption = False
    sign Posit      = False
    sign _          = True


{- which statements can declare variables -}
canDeclare :: Section -> Bool
canDeclare Assumption = True
canDeclare Choice = True
canDeclare LowDefinition = True
canDeclare _ = False


file :: Block -> Text
file = Text.fromStrict . make_text . fromMaybe Bytes.empty . Position.file_of . position

declaredNames :: Block -> Set VariableName
declaredNames = Set.map declName . declaredVariables


instance Representation Block where
  represent fmt = showBlock fmt 0

showBlock :: Format -> Int -> Block -> Bytes
showBlock fmt p block@Block{body = b, name = name, kind = kind}
  | null b = showForm fmt p block
  | isTopLevel block = represent fmt kind <> addName <> ":\n" <> showBlockForm fmt (p + 1) block <>
      (if needsProof block
        then if null b
          then indent p "Trivial:\n"
          else let proof = last b in
            case proof of
              ProofTextBlock proofBlock -> indent p "Proof:\n" <> showProof fmt (p + 1) (body proofBlock) <> indent p "Qed.\n"
              _ -> ""
        else "")
  | otherwise = showForm fmt p block <>
      indent p "Proof:\n" <> showProof fmt (p + 1) (body block) <> indent p "Qed.\n"
  where
    name' = make_bytes name
    addName = if Bytes.null name' then "" else " (" <> name' <> ")"

showForm :: Format -> Int -> Block -> Bytes
showForm fmt p block@Block{formula = formula, name = name} =
  indent p $ represent fmt formula <> "\n"

showBlockForm :: Format -> Int -> Block -> Bytes
showBlockForm fmt p block =
  indent p $ represent fmt (formulate block) <> "\n"

showProof :: Format -> Int -> [ProofText] -> Bytes
showProof fmt p = foldr (\pt bs -> showProofText fmt p pt <> bs) ""

parseErrors :: ProofText -> [ParseError]
parseErrors (ProofTextError err) = [err]
parseErrors (ProofTextBlock bl) = concatMap parseErrors (body bl)
parseErrors _ = []

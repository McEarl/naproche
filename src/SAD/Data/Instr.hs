{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Instruction datatype and core functions.
-}

module SAD.Data.Instr where

import SAD.Core.SourcePos (SourcePos, SourceRange(..), noSourcePos, noRange)


-- Position information

data Pos = Pos {start :: SourcePos, stop :: SourcePos, range :: SourceRange}

position :: Pos -> SourcePos
position p = let SourceRange a b = range p in a

noPos :: Pos
noPos = Pos noSourcePos noSourcePos noRange


-- Instruction types

data Instr =
    Command Command
  | LimitBy Limit Int
  | SetFlag Flag Bool
  | GetArgument Argument String
  | GetArguments Arguments [String]
  deriving (Show, Eq)

data Drop =
    DropCommand Command
  | DropLimit Limit
  | DropFlag Flag
  | DropArgument Argument
  deriving (Show, Eq)


-- Instructions

data Command =
    EXIT     -- exit
  | QUIT     -- exit
  | THESIS   -- print current thesis
  | CONTEXT  -- print current context
  | FILTER   -- print simplified top-level context
  | RULES
  deriving (Eq,Show)

data Limit =
    Timelimit   -- time limit per prover launch  (3 sec)
  | Depthlimit  -- number of reasoner iterations (7)
  | Checktime   -- time limit for checker's tasks (1 sec)
  | Checkdepth  -- depth limit for checker's tasks (3)
  deriving (Eq,Show)

data Flag =
    Prove          --  prove goals (yes)
  | Check          --  look for applicable definitions (yes)
  | Symsign        --  rename symbols with diverging defs (yes)
  | Info           --  accumulate evidences (yes)
  | Thesis         --  modify thesis (yes)
  | Filter         --  simplify the context (yes)
  | Skipfail       --  ignore failed goals (no)
  | Flat           --  do not descend into proofs (no)
  | Printgoal      --  print current goal (yes)
  | Printreason    --  print reasoner's log (no)
  | Printsection   --  print current sentence (no)
  | Printcheck     --  print definition checks (no)
  | Printprover    --  print prover's log (no)
  | Printunfold    --  print definition unfolds (no)
  | Printfulltask  --  print inference tasks (no)
  | Dump           --  print tasks in prover's syntax (no)
  | OnlyTranslate  --  translation only (comline only)
  | Verbose        --  verbosity control (comline only)
  | Help           --  print help (comline only)
  | Server         --  server mode (comline only)
  | Printsimp      --  print simplifier log (no)
  | Printthesis    --  print thesis development (no)
  | Ontored        --  use ontological reduction (no)
  | Unfold         --  general unfolding (on)
  | Unfoldsf       --  general unfolding of sets and functions
  | Unfoldlow      --  unfold the whole low level context (yes)
  | Unfoldlowsf    --  unfold set and function conditions in low level (no)
  | Checkontored   --  enable ontological reduction for checks (off)
  | Translation    --  print first-order translation of sentences
  deriving (Eq,Show)

data Argument =
    Init     --  init file (init.opt)
  | Text     --  literal text
  | File     --  read file
  | Read     --  read library file
  | Library  --  library directory
  | Provers  --  prover database
  | Prover   --  current prover
  deriving (Eq,Show)

data Arguments =
  Synonym
  deriving (Eq,Show)

-- Ask

askLimit :: Limit -> Int -> [Instr] -> Int
askLimit i d is  = head $ [ v | LimitBy j v <- is, i == j ] ++ [d]

askFlag :: Flag -> Bool -> [Instr] -> Bool
askFlag i d is  = head $ [ v | SetFlag j v <- is, i == j ] ++ [d]

askArgument :: Argument -> String -> [Instr] -> String
askArgument i d is  = head $ [ v | GetArgument j v <- is, i == j ] ++ [d]


-- Drop

-- | Drop an @Instr@ from the @[Instr]@ (assuming the latter doesn't contain duplicates)
dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropCommand m) (Command n : rs) | n == m = rs
dropInstr (DropLimit m) (LimitBy n _ : rs) | n == m = rs
dropInstr (DropFlag m) (SetFlag n _ : rs) | n == m = rs
dropInstr (DropArgument m) (GetArgument n _ : rs) | n == m = rs
dropInstr i (r : rs)  = r : dropInstr i rs
dropInstr _ _ = []


-- Keywords

keywordsCommand :: [(Command, String)]
keywordsCommand =
 [(EXIT, "exit"),
  (QUIT, "quit"),
  (THESIS, "thesis"),
  (CONTEXT, "context"),
  (FILTER, "filter"),
  (RULES, "rules")]

keywordsLimit :: [(Limit, String)]
keywordsLimit =
 [(Timelimit, "timelimit"),
  (Depthlimit, "depthlimit"),
  (Checktime, "checktime"),
  (Checkdepth, "checkdepth")]

keywordsFlag :: [(Flag, String)]
keywordsFlag =
 [(Prove, "prove"),
  (Check, "check"),
  (Symsign, "symsign"),
  (Info, "info"),
  (Thesis, "thesis"),
  (Filter, "filter"),
  (Skipfail, "skipfail"),
  (Flat, "flat"),
  (Printgoal, "printgoal"),
  (Printsection, "printsection"),
  (Printcheck, "printcheck"),
  (Printunfold, "printunfold"),
  (Printreason, "printreason"),
  (Printprover, "printprover"),
  (Printfulltask, "printfulltask"),
  (Dump, "dump"),
  (Printsimp, "printsimp"),
  (Printthesis, "printthesis"),
  (Ontored, "ontored"),
  (Unfold, "unfold"),
  (Unfoldsf, "unfoldsf"),
  (Unfoldlow, "unfoldlow"),
  (Unfoldlowsf, "unfoldlowsf"),
  (Checkontored, "checkontored"),
  (Translation, "translation")]

keywordsArgument :: [(Argument, String)]
keywordsArgument =
 [(Read, "read"),
  (Library, "library"),
  (Provers, "provers"),
  (Prover, "prover")]

keywordsArguments :: [(Arguments, String)]
keywordsArguments =
  [(Synonym, "synonym")]

-- distiguish between parser and verifier instructions 

isParserInstruction :: Instr -> Bool
isParserInstruction i = case i of
  Command EXIT -> True; Command QUIT -> True; GetArgument Read _ -> True;
  GetArguments Synonym _ -> True; _ -> False
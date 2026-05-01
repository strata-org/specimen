-- import Mathlib
import Plausible.Arbitrary
import Plausible.DeriveArbitrary

/-! Arithmetic expression compiler: syntax, semantics, and compilation from statements to stack machine instructions. -/

open Plausible Gen

-- -- -- -- -- -- -- -- -- --
-- HIGH-LEVEL SYNTAX
-- -- -- -- -- -- -- -- -- --

-- Arithmetic expressions
inductive AExpr : Type where
  | const : Int → AExpr
  | var : String → AExpr
  | add : AExpr → AExpr → AExpr
  | sub : AExpr → AExpr → AExpr
  | mul : AExpr → AExpr → AExpr
deriving Repr, DecidableEq, Arbitrary

-- Boolean expressions
inductive BExpr : Type where
  | littrue : BExpr
  | litfalse : BExpr
  | eq : AExpr → AExpr → BExpr
  | le : AExpr → AExpr → BExpr
  | and : BExpr → BExpr → BExpr
  | not : BExpr → BExpr
deriving Repr, DecidableEq, Arbitrary

-- Statements
inductive Stmt : Type where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | assign : String → AExpr → Stmt
  | condassign : BExpr → String → AExpr → Stmt
deriving Repr, DecidableEq, Arbitrary

-- -- -- -- -- -- -- -- -- --
-- LOW-LEVEL SYNTAX
-- -- -- -- -- -- -- -- -- --

-- Assembly instructions for a more realistic stack machine
inductive Instr : Type where
  -- Store
  | istore : String → Instr -- store from stack to variable
  | icondstore : String → Instr -- pop v, then c from stack; if c nonzero, then store v
  -- Calculational operations
  | iload : String → Instr  -- load variable value onto stack
  | iconst : Int → Instr    -- load literal integer onto stack
  | iadd : Instr
  | isub : Instr
  | imul : Instr
  -- Boolean operations
  | ieq : Instr    -- equality test
  | ile : Instr    -- less-than-or-equal test
  | inot : Instr   -- boolean negation
  | iand : Instr   -- boolean and
deriving Repr, DecidableEq, Arbitrary

-- Add Inhabited instance for Instr
instance : Inhabited Instr := ⟨Instr.iconst 0⟩

-- -- -- -- -- --
-- COMPILER
-- -- -- -- -- --

-- Compilation of arithmetic expressions
def compileAExpr : AExpr → List Instr
  | AExpr.const n => [Instr.iconst n]
  | AExpr.var x => [Instr.iload x]
  | AExpr.add e1 e2 => ((compileAExpr e1) ++ (compileAExpr e2)) ++ [Instr.iadd]
  | AExpr.sub e1 e2 => ((compileAExpr e1) ++ (compileAExpr e2)) ++ [Instr.isub]
  | AExpr.mul e1 e2 => ((compileAExpr e1) ++ (compileAExpr e2)) ++ [Instr.imul]

-- Compilation of boolean expressions
def compileBExpr : BExpr → List Instr
  | BExpr.littrue => [Instr.iconst 1]
  | BExpr.litfalse => [Instr.iconst 0]
  | BExpr.eq e1 e2 => ((compileAExpr e1) ++ (compileAExpr e2)) ++ [Instr.ieq]
  | BExpr.le e1 e2 => ((compileAExpr e1) ++ (compileAExpr e2)) ++ [Instr.ile]
  | BExpr.and b1 b2 => ((compileBExpr b1) ++ (compileBExpr b2)) ++ [Instr.iand]
  | BExpr.not b => (compileBExpr b) ++ [Instr.inot]

-- Compilation of statements
def compileStmt (stmt : Stmt) : List Instr :=
  match stmt with
  | Stmt.skip => []
  | Stmt.assign x e => (compileAExpr e) ++ [Instr.istore x]
  | Stmt.condassign b x e => ((compileBExpr b) ++ (compileAExpr e)) ++ [Instr.icondstore x]
  | Stmt.seq s1 s2 => (compileStmt s1) ++ (compileStmt s2)

-- -- -- -- -- -- -- -- -- --
-- HIGH-LEVEL SEMANTICS
-- -- -- -- -- -- -- -- -- --

-- Variable store (maps variable names to values)
-- def Store := String → Int

-- def update_store (x:String) (v:Int) (s:Store) : Store :=
--   (fun y => if y = x then v else s y)

-- def lookup_store (x:String) (s:Store) (v:Int) : Int :=
--   s x

def Store := List (String × Int)
deriving BEq, DecidableEq

def update_store (x:String) (v:Int) (s:Store) : Store :=
  (x,v)::s

def lookup_store (x:String) (s:Store) (v:Int) : Int :=
  s.foldr (fun (x',v') res => if x = x' then v' else res) v

-- Convert boolean to integer
def boolToInt : Bool → Int
  | true => 1
  | false => 0

-- Convert integer to boolean
def intToBool : Int → Bool
  | 0 => false
  | _ => true

-- Evaluation of arithmetic expressions
def evalA (store : Store) : AExpr → Int
  | AExpr.const n => n
  | AExpr.var x => lookup_store x store 0
  | AExpr.add e1 e2 => evalA store e1 + evalA store e2
  | AExpr.sub e1 e2 => evalA store e1 - evalA store e2
  | AExpr.mul e1 e2 => evalA store e1 * evalA store e2

-- Evaluation of boolean expressions
def evalB (store : Store) : BExpr → Bool
  | BExpr.littrue => true
  | BExpr.litfalse => false
  | BExpr.eq e1 e2 => evalA store e1 = evalA store e2
  | BExpr.le e1 e2 => evalA store e1 ≤ evalA store e2
  | BExpr.and b1 b2 => (evalB store b1) ∧ (evalB store b2)
  | BExpr.not b     => ¬ (evalB store b)

-- Semantics for assign
def evalAssign (store : Store) (x : String) (e : AExpr) : Store :=
  update_store x (evalA store e) store

-- Big-step operational semantics for statements
def evalStmt (store : Store) (stmt : Stmt) : Store :=
  match stmt with
  | Stmt.skip => store
  | Stmt.assign x e => (evalAssign store x e)
  | Stmt.condassign b x e =>
    if (evalB store b) then (evalAssign store x e) else store
  | Stmt.seq s1 s2 => evalStmt (evalStmt store s1) s2

-- -- -- -- -- -- -- -- -- --
-- LOW-LEVEL SEMANTICS
-- -- -- -- -- -- -- -- -- --

-- Stack type
def Stack := List Int
deriving BEq, DecidableEq

-- Stack machine state
structure MachineState where
  stack : Stack
  store : Store
deriving BEq, DecidableEq

-- Add Inhabited instance for MachineState
-- instance : Inhabited MachineState := ⟨{store:=(fun _ => 0), stack:=[]}⟩
instance : Inhabited MachineState := ⟨{store:=[], stack:=[]}⟩

-- State from store by using empty stack
def optStateFromStore (store : Store) : Option MachineState := some {store:=store, stack:=[]}

-- execution function for arith and boolean expressions
def execCalcInstr (store : Store) (instr : Instr) (s : Stack) : Stack :=
    match instr with
    | Instr.iconst n => n :: s
    | Instr.iload x => lookup_store x store 0 :: s
    | Instr.iadd =>
      match s with
      | n2 :: n1 :: rest => (n1 + n2) :: rest
      | _ => s
    | Instr.isub =>
      match s with
      | n2 :: n1 :: rest => (n1 - n2) :: rest
      | _ => s
    | Instr.imul =>
      match s with
      | n2 :: n1 :: rest => (n1 * n2) :: rest
      | _ => s
    | Instr.ieq =>
      match s with
      | n2 :: n1 :: rest => (if n1 = n2 then 1 else 0) :: rest
      | _ => s
    | Instr.ile =>
      match s with
      | n2 :: n1 :: rest => (if n1 ≤ n2 then 1 else 0) :: rest
      | _ => s
    | Instr.inot =>
      match s with
      | n :: rest => (if n = 0 then 1 else 0) :: rest
      | _ => s
    | Instr.iand =>
      match s with
      | n2 :: n1 :: rest => (if n1 ≠ 0 ∧ n2 ≠ 0 then 1 else 0) :: rest
      | _ => s
    | _ => s  -- Ignore other instructions

-- Execute a single instruction
def execInstr (instr : Instr) (maybestate : Option MachineState) : Option MachineState :=
  match maybestate with
  | none => none
  | some state =>
    match instr with
    ----
    | Instr.istore x =>
      match state.stack with
      | v :: rest => some {store:=(update_store x v state.store), stack:=rest}
      | _ => none -- Stack underflow
    | Instr.icondstore x =>
      match state.stack with
      | v :: c :: rest => some {store:=(if c=0 then state.store else (update_store x v state.store)), stack:=rest}
      | _ => none -- Stack underflow
    ----
    | Instr.iconst _
    | Instr.iload _
    | Instr.iadd
    | Instr.isub
    | Instr.imul
    | Instr.ieq
    | Instr.ile
    | Instr.inot
    | Instr.iand => some {state with stack:=(execCalcInstr state.store instr state.stack)}

-- Execute program
def execProg (prog : List Instr) (state0 : Option MachineState) : Option MachineState :=
  prog.foldl (fun s instr => execInstr instr s) state0

-- -- -- -- -- -- -- -- -- --
-- FUNCTIONS TO REASON ABOUT
-- -- -- -- -- -- -- -- -- --

def execConcat (pa pb : List Instr) (ss : Option MachineState) : Option MachineState :=
  execProg (pa ++ pb) ss

def execCompiledAExpr (e : AExpr) (store : Store) (stack : Stack) : Option MachineState :=
  execProg (compileAExpr e) (some {store:=store, stack:=stack})

def execCompiledBExpr (b : BExpr) (store : Store) (stack : Stack) : Option MachineState :=
  execProg (compileBExpr b) (some {store:=store, stack:=stack})

def execCompiledStmt (s : Stmt) (state : MachineState) : Option MachineState :=
  execProg (compileStmt s) (some state)

def underflowFlag (stmt : Stmt) (state : MachineState) : Bool :=
  match execCompiledStmt stmt state with
  | none => true
  | some _ => false

-- theorem preserve_value (stmt : Stmt) (store0 : Store) : execProg (compileStmt stmt) (optStateFromStore store0) = (optStateFromStore (evalStmt store0 stmt)) := by sorry

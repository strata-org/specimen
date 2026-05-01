/-! Extended arithmetic compiler with intentional bugs for testing Specimen's bug-finding capabilities. -/
-- import Batteries

-- ##########################
-- SYNTAX
-- ##########################

-- -- -- -- -- -- -- -- -- --
-- HIGH-LEVEL SYNTAX
-- -- -- -- -- -- -- -- -- --

-- Arithmetic expressions
inductive ArithExpr : Type where
  | const : Int → ArithExpr
  | var : String → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | sub : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
deriving Repr, DecidableEq

-- Boolean expressions
inductive BoolExpr : Type where
  | littrue : BoolExpr
  | litfalse : BoolExpr
  | eq : ArithExpr → ArithExpr → BoolExpr
  | le : ArithExpr → ArithExpr → BoolExpr
  | and : BoolExpr → BoolExpr → BoolExpr
  | not : BoolExpr → BoolExpr
deriving Repr, DecidableEq

-- Statements
inductive Stmt : Type where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | assign : String → ArithExpr → Stmt
  | ifthenelse : BoolExpr → Stmt → Stmt → Stmt
  | while : BoolExpr → Stmt → Stmt
deriving Repr, DecidableEq


-- -- -- -- -- -- -- -- -- --
-- LOW-LEVEL SYNTAX
-- -- -- -- -- -- -- -- -- --

-- Assembly instructions for a stack machine
inductive Instr : Type where
  -- Control Flow
  | inoop : Int → Instr   -- label-carrying noop
  | ihalt : Instr         -- cease computation
  | ijump : Int -> Instr  -- jump forward or backward given number of instrs
  | ibifz : Int -> Instr  -- pop from stack and jump IF that stack val was 0.
  -- Memory and Stack
  | idups : Instr -- duplicate top of stack
  | ipops : Instr -- pop from stack
  | isave : String → Instr   -- mem from stack to variable
  | iload : String → Instr  -- load variable value onto stack
  -- Calculation
  --   /arithmetic
  | iconst : Int → Instr    -- load literal integer onto stack
  | iadd : Instr
  | isub : Instr
  | imul : Instr
  --   /boolean
  | ieq : Instr    -- equality test
  | ile : Instr    -- less-than-or-equal test
  | inot : Instr   -- boolean negation
  | iand : Instr   -- boolean and
deriving Repr, DecidableEq

-- Instr is Inhabited
instance : Inhabited Instr := ⟨Instr.ihalt⟩

-- ObjCode is list of instructions
abbrev ObjCode := List Instr

-- ##########################
-- SEMANTICS
-- ##########################

-- -- -- -- -- -- -- -- -- --
-- HIGH-LEVEL SEMANTICS
-- -- -- -- -- -- -- -- -- --

-- Memory (association list mapping variable names to values)
def Mem := List (String × Int)
deriving BEq, DecidableEq, Repr

-- Lookup variable in memory with default value
def lookupMem (x : String) (m : Mem) (default : Int) : Int :=
  m.foldr (fun (x', v') res => if x = x' then v' else res) default

-- All-zeros Memory as example
def zerosMem : Mem := []

-- Change one variable value in Memory
def updateMem (x : String) (v : Int) (s : Mem) : Mem :=
  (x, v) :: s

-- Evaluate arithmetic expressions
def evalArith (mem : Mem) : ArithExpr → Int
  | ArithExpr.const n => n
  | ArithExpr.var x => lookupMem x mem 0
  | ArithExpr.add e1 e2 => evalArith mem e1 + evalArith mem e2
  | ArithExpr.sub e1 e2 => evalArith mem e1 - evalArith mem e2
  | ArithExpr.mul e1 e2 => evalArith mem e1 * evalArith mem e2

-- Evaluate boolean expressions
def evalBool (mem : Mem) : BoolExpr → Bool
  | BoolExpr.littrue => true
  | BoolExpr.litfalse => false
  | BoolExpr.eq e1 e2 => evalArith mem e1 = evalArith mem e2
  | BoolExpr.le e1 e2 => evalArith mem e1 ≤ evalArith mem e2
  | BoolExpr.and b1 b2 => (evalBool mem b1) ∧ (evalBool mem b2)
  | BoolExpr.not b     => ¬ (evalBool mem b)

-- Semantics for assign
def evalAssign (mem : Mem) (x : String) (e : ArithExpr) : Mem :=
  updateMem x (evalArith mem e) mem

-- Semantics as an inductive relation
inductive Eval : Mem → Stmt → Mem → Prop where
| ESkip : ∀ M,
    Eval M Stmt.skip M
| EAssign : ∀ M1 M2 x e,
    evalAssign M1 x e = M2 →
    Eval M1 (Stmt.assign x e) M2
| ESeq : ∀ M1 M2 M3 s1 s2,
    Eval M1 s1 M2 →
    Eval M2 s2 M3 →
    Eval M1 (Stmt.seq s1 s2) M3
| EIfThen : ∀ M1 M2 e s1 s2,
    evalBool M1 e = true →
    Eval M1 s1 M2 →
    Eval M1 (Stmt.ifthenelse e s1 s2) M2
| EIfElse : ∀ M1 M2 e s1 s2,
    evalBool M1 e = false →
    Eval M1 s2 M2 →
    Eval M1 (Stmt.ifthenelse e s1 s2) M2
| EWhileThen : ∀ M1 e s M2,
    evalBool M1 e = true →
    Eval M1 (Stmt.seq s (Stmt.while e s)) M2 →
    Eval M1 (Stmt.while e s) M2
| EWhileElse : ∀ M e s,
    evalBool M e = false →
    Eval M (Stmt.while e s) M

-- Fuel-bounded Big-step operational semantics for statements, as executable function
def pathStmt (stmt : Stmt) (fuel : Nat) (mi : Mem) : Option Mem :=
  match fuel with
  | 0 => none
  | fuel'+1 =>
    match stmt with
    | Stmt.skip => some mi
    | Stmt.assign x e => some (evalAssign mi x e)
    | Stmt.seq s1 s2 =>
      match pathStmt s1 fuel' mi with
      | none => none
      | some mm => pathStmt s2 fuel' mm
    | Stmt.ifthenelse cond s1 s2 =>
      if evalBool mi cond
        then pathStmt s1 fuel' mi
        else pathStmt s2 fuel' mi
    | Stmt.while cond s =>
      if evalBool mi cond
        then pathStmt (Stmt.seq s (Stmt.while cond s)) fuel' mi
        else some mi

-- Big-step operational semantics for statements, as relation
def pathStmtE (stmt : Stmt) (mi mf : Mem) : Prop :=
  ∃ (fuel : Nat), pathStmt stmt fuel mi = some mf

-- -- -- -- -- -- -- -- -- --
-- LOW-LEVEL SEMANTICS
-- -- -- -- -- -- -- -- -- --

-- Stack type
def Stack := List Int
deriving Repr

-- Stack machine state
structure HardwareState where
  mem : Mem
  stack : Stack
  pc : Int
deriving Repr

-- Add Inhabited instance for HardwareState
instance : Inhabited HardwareState := ⟨{mem:=zerosMem, stack:=[], pc:=0}⟩

-- Perform binary operation on stack machine
abbrev stackFromTops (stack : Stack) (process_tops : Int → Int → Int) : Option Stack :=
  match stack with
  | v2 :: v1 :: rest => some ((process_tops v1 v2) :: rest)
  | _ => none -- Stack underflow

-- execution function for arith and boolean expressions
abbrev execCalcInstr (mem : Mem) (instr : Instr) (stack : Stack) : Option Stack :=
    match instr with
    | Instr.iconst n => some (n :: stack)
    | Instr.iload x => some (lookupMem x mem 0 :: stack)
    | Instr.iadd => stackFromTops stack (fun n1 n2 ↦ n1+n2)
    | Instr.isub => stackFromTops stack (fun n1 n2 ↦ n1-n2)
    | Instr.imul => stackFromTops stack (fun n1 n2 ↦ n1*n2)
    | Instr.ieq => stackFromTops stack (fun n1 n2 ↦ (if n1 = n2 then 1 else 0))
    | Instr.ile => stackFromTops stack (fun n1 n2 ↦ (if n1 ≤ n2 then 1 else 0))
    | Instr.iand => stackFromTops stack (fun n1 n2 ↦ (if n1 ≠ 0 ∧ n2 ≠ 0 then 1 else 0))
    | Instr.inot =>
      match stack with
      | n :: rest => some ((if n = 0 then 1 else 0) :: rest)
      | _ => none
    | _ => none

-- Mutate hardware state based on assumed-non-empty stack
abbrev hStateFromTop (stack:Stack) (process_top : Int → Stack → HardwareState) : Option HardwareState :=
  match stack with
  | v :: rest => some (process_top v rest)
  | _ => none -- Stack underflow

-- Execute a single instruction
def execInstr (instr : Instr) (maybe_hstate : Option HardwareState) : Option HardwareState :=
  match maybe_hstate with
  | none => none
  | some ⟨mem,stack,pc⟩ =>
    match instr with
    | Instr.inoop _ => some {mem:=mem, stack:=stack, pc:=pc+1}
    | Instr.ihalt => some {mem:=mem, stack:=stack, pc:=pc}
    | Instr.ijump dpc => some {mem:=mem, stack:=stack, pc:=pc+dpc}
    | Instr.ibifz dpc => hStateFromTop stack (fun v rest ↦ {mem:=mem, stack:=rest, pc:=(if v=0 then pc+dpc else pc+1)})
    ----
    | Instr.idups   => hStateFromTop stack (fun v rest ↦ {mem:=mem, stack:=v::v::rest, pc:=pc+1})
    | Instr.ipops   => hStateFromTop stack (fun _ rest ↦ {mem:=mem, stack:=rest, pc:=pc+1})
    | Instr.isave x => hStateFromTop stack (fun v rest ↦ {mem:=(updateMem x v mem), stack:=rest, pc:=pc+1})
    ----
    | Instr.iload _
    | Instr.iconst _
    | Instr.iadd
    | Instr.isub
    | Instr.imul
    | Instr.ieq
    | Instr.ile
    | Instr.iand
    | Instr.inot =>
      match execCalcInstr mem instr stack with
      | some stack' => some {mem:=mem, stack:=stack', pc:=pc+1}
      | none => none

-- Execute program
def execCode (code : ObjCode) (steps : Nat) (maybe_hstate : Option HardwareState) : Option HardwareState :=
  match steps, maybe_hstate with
  | 0, _
  | _, none => maybe_hstate
  | steps'+1, some state0 =>
    match code[state0.pc.natAbs]? with
    | none => none
    | some instr =>
        let state1 := execInstr instr maybe_hstate
        execCode code steps' state1

-- ##########################
-- COMPILATION
-- ##########################

-- -- -- -- -- -- -- -- -- --
-- BASIC COMPILER (IS BACK-END FOR THE SUBSEQUENT FRONT-END OPTIMIZATIONS)
-- -- -- -- -- -- -- -- -- --

-- Compile arithmetic expressions
def compileArith : ArithExpr → ObjCode
  | ArithExpr.const n => [Instr.iconst n]
  | ArithExpr.var x => [Instr.iload x]
  | ArithExpr.add e1 e2 => ((compileArith e1) ++ (compileArith e2)) ++ [Instr.iadd]
  | ArithExpr.sub e1 e2 => ((compileArith e1) ++ (compileArith e2)) ++ [Instr.isub]
  | ArithExpr.mul e1 e2 => ((compileArith e1) ++ (compileArith e2)) ++ [Instr.imul]

-- Compile boolean expressions
def compileBool : BoolExpr → ObjCode
  | BoolExpr.littrue => [Instr.iconst 1]
  | BoolExpr.litfalse => [Instr.iconst 0]
  | BoolExpr.eq e1 e2 => ((compileArith e1) ++ (compileArith e2)) ++ [Instr.ieq]
  | BoolExpr.le e1 e2 => ((compileArith e1) ++ (compileArith e2)) ++ [Instr.ile]
  | BoolExpr.and b1 b2 => ((compileBool b1) ++ (compileBool b2)) ++ [Instr.iand]
  | BoolExpr.not b => (compileBool b) ++ [Instr.inot]

-- Compile high-level programs
def compileStmt (stmt : Stmt) : ObjCode :=
  match stmt with
  | Stmt.skip => []
  | Stmt.assign x e => (compileArith e) ++ [Instr.isave x]
  | Stmt.seq s1 s2 => (compileStmt s1) ++ (compileStmt s2)
  | Stmt.ifthenelse cond s1 s2 =>
    let condcode := compileBool cond
    let thencode := compileStmt s1
    let elsecode := compileStmt s2
    (condcode
     ++ [Instr.ibifz (1 +thencode.length +1)]
     ++ thencode
     ++ [Instr.ijump (1 +elsecode.length)]
     ++ elsecode
     )
  | Stmt.while cond s =>
    let condcode := compileBool cond
    let bodycode := compileStmt s
    (condcode
     ++ [Instr.ibifz (1 + bodycode.length + 1)]
     ++ bodycode
     ++ [Instr.ijump (-bodycode.length -1 -condcode.length)]
     )

def compileBasic (s : Stmt) : ObjCode :=
  (compileStmt s) ++ [Instr.ihalt]

-- -- -- -- -- -- -- -- -- --
-- LOCAL SIMPLIFIER HELPERS
-- -- -- -- -- -- -- -- -- --

def makePlusConst (e : ArithExpr) (n : Int) : ArithExpr :=
  match n with
  | 0 => e
  | _ =>
    match e with
    | ArithExpr.const c => ArithExpr.const (c+n)
    | ArithExpr.add e' (ArithExpr.const c) => ArithExpr.add e' (ArithExpr.const (c+n))
    | _ => ArithExpr.add e (ArithExpr.const n)

def makeTimesConst (e : ArithExpr) (n : Int) : ArithExpr :=
  match n with
  | 1 => e
  | 0 => ArithExpr.const 0
  | _ =>
    match e with
    | ArithExpr.const c => ArithExpr.const (c*n)
    | ArithExpr.mul e' (ArithExpr.const c) => ArithExpr.mul e' (ArithExpr.const (c*n))
    | _ => ArithExpr.mul e (ArithExpr.const n)

def makePlus (e1 e2 : ArithExpr) : ArithExpr :=
  match e1, e2 with
  | ArithExpr.const c, _ => makePlusConst e2 c
  | _, ArithExpr.const c => makePlusConst e1 c
  | ArithExpr.add e1' (ArithExpr.const c1), ArithExpr.add e2' (ArithExpr.const c2) => makePlusConst (ArithExpr.add e1' e2') (c1+c2)
  | ArithExpr.add e1' (ArithExpr.const c1), _ => makePlusConst (ArithExpr.add e1' e2) c1
  | _, ArithExpr.add e2' (ArithExpr.const c2) => makePlusConst (ArithExpr.add e1 e2') c2
  | ArithExpr.mul e11 e12, ArithExpr.mul e21 e22 =>
    if e11=e21 then ArithExpr.mul e11 (ArithExpr.add e12 e22) else
    if e11=e22 then ArithExpr.mul e11 (ArithExpr.add e12 e21) else
    if e12=e21 then ArithExpr.mul e12 (ArithExpr.add e11 e22) else
    if e12=e22 then ArithExpr.mul e12 (ArithExpr.add e11 e21) else ArithExpr.add e1 e2
  | _, _ => ArithExpr.add e1 e2

def makeMinus (e1 e2 : ArithExpr) : ArithExpr :=
  match e1, e2 with
  | _, ArithExpr.const c => makePlusConst e1 (-c)
  | ArithExpr.add e1' (ArithExpr.const c1), ArithExpr.add e2' (ArithExpr.const c2) => makePlusConst (ArithExpr.sub e1' e2') (c1-c2)
  | ArithExpr.add e1' (ArithExpr.const c1), _ => makePlusConst (ArithExpr.sub e1' e2) c1
  | _, ArithExpr.add e2' (ArithExpr.const c2) => makePlusConst (ArithExpr.sub e1 e2') (-c2)
  | ArithExpr.mul e11 e12, ArithExpr.mul e21 e22 =>
    if e11=e21 then ArithExpr.mul e11 (ArithExpr.sub e12 e22) else
    if e11=e22 then ArithExpr.mul e11 (ArithExpr.sub e12 e21) else
    if e12=e21 then ArithExpr.mul e12 (ArithExpr.sub e11 e22) else
    if e12=e22 then ArithExpr.mul e12 (ArithExpr.sub e11 e21) else ArithExpr.sub e1 e2
  | _, _ => ArithExpr.sub e1 e2

def makeTimes (e1 e2 : ArithExpr) : ArithExpr :=
  match e1, e2 with
  | _, ArithExpr.const c => makeTimesConst e1 c
  | ArithExpr.mul e1' (ArithExpr.const c1), ArithExpr.mul e2' (ArithExpr.const c2) => makeTimesConst (ArithExpr.mul e1' e2') (c1*c2)
  | ArithExpr.mul e1' (ArithExpr.const c1), _ => makeTimesConst (ArithExpr.mul e1' e2) c1
  | _, ArithExpr.mul e2' (ArithExpr.const c2) => makeTimesConst (ArithExpr.mul e1 e2') c2
  | _, _ => ArithExpr.mul e1 e2

def makeEq (e1 e2 : ArithExpr) : BoolExpr :=
  match e1, e2 with
  | ArithExpr.const c1, ArithExpr.const c2 => (if c1 = c2 then BoolExpr.littrue else BoolExpr.litfalse)
  | ArithExpr.add e1' (ArithExpr.const c1), ArithExpr.const c2 => BoolExpr.eq e1' (ArithExpr.const (c2-c1))
  | ArithExpr.const c1, ArithExpr.add e2' (ArithExpr.const c2) => BoolExpr.eq (ArithExpr.const (c1-c2)) e2'
  | _, _ => BoolExpr.eq e1 e2

def makeLe (e1 e2 : ArithExpr) : BoolExpr :=
  match e1, e2 with
  | ArithExpr.const c1, ArithExpr.const c2 => (if c1 ≤ c2 then BoolExpr.littrue else BoolExpr.litfalse)
  | ArithExpr.add e1' (ArithExpr.const c1), ArithExpr.const c2 => BoolExpr.le e1' (ArithExpr.const (c2-c1))
  | ArithExpr.const c1, ArithExpr.add e2' (ArithExpr.const c2) => BoolExpr.le (ArithExpr.const (c1-c2)) e2'
  | _, _ => BoolExpr.le e1 e2

def makeAnd (b1 b2 : BoolExpr) : BoolExpr :=
  match b1, b2 with
  | BoolExpr.littrue, _ => b2
  | _, BoolExpr.littrue => b1
  | BoolExpr.litfalse, _ => BoolExpr.litfalse
  | _, BoolExpr.litfalse => BoolExpr.litfalse
  | _, _ => BoolExpr.and b1 b2

def makeNot (b : BoolExpr) : BoolExpr :=
  match b with
  | BoolExpr.littrue => BoolExpr.litfalse
  | BoolExpr.litfalse => BoolExpr.littrue
  | BoolExpr.not b' => b'
  | _ => BoolExpr.not b

def makeIfThenElse (b : BoolExpr) (thenc elsec : Stmt) : Stmt :=
  match b with
  | BoolExpr.littrue => thenc
  | BoolExpr.litfalse => elsec
  | _ => Stmt.ifthenelse b thenc elsec

def makeWhile (b : BoolExpr) (body : Stmt) : Stmt :=
  match b with
  | BoolExpr.litfalse => Stmt.skip
  | _ => Stmt.while b body

-- -- -- -- -- -- -- -- -- --
-- COMPILER W/ LOCAL SIMPLIFICATION
-- -- -- -- -- -- -- -- -- --

def simplifyArith (e : ArithExpr) : ArithExpr :=
  match e with
  | ArithExpr.add e1 e2 => makePlus (simplifyArith e1) (simplifyArith e2)
  | ArithExpr.sub e1 e2 => makeMinus (simplifyArith e1) (simplifyArith e2)
  | ArithExpr.mul e1 e2 => makeTimes (simplifyArith e1) (simplifyArith e2)
  | _ => e


def simplifyBool (b : BoolExpr) : BoolExpr :=
  match b with
  | BoolExpr.eq a1 a2 => makeEq (simplifyArith a1) (simplifyArith a2)
  | BoolExpr.le a1 a2 => makeLe (simplifyArith a1) (simplifyArith a2)
  | BoolExpr.and b1 b2 => makeAnd (simplifyBool b1) (simplifyBool b2)
  | BoolExpr.not b => makeNot (simplifyBool b)
  | _ => b

def simplifyStmt (stmt : Stmt) : Stmt :=
  match stmt with
  | Stmt.assign v e => Stmt.assign v (simplifyArith e)
  | Stmt.ifthenelse b s1 s2 => makeIfThenElse (simplifyBool b) (simplifyStmt s1) (simplifyStmt s2)
  | Stmt.while b s => makeWhile (simplifyBool b) (simplifyStmt s)
  | Stmt.seq s1 s2 => Stmt.seq (simplifyStmt s1) (simplifyStmt s2)
  | _ => stmt

def compileSimplify (s : Stmt) : ObjCode :=
  compileBasic (simplifyStmt s)

-- -- -- -- -- -- -- -- -- --
-- ABSTRACT MEM
-- -- -- -- -- -- -- -- -- --

-- Abstract Memory (association list with known variable values)
abbrev AbsMem := Mem

abbrev absTop : AbsMem := []

abbrev absJoin (a b : AbsMem) : AbsMem :=
  let allKeys := (a.map (·.1) ++ b.map (·.1)).eraseDups
  allKeys.filterMap (fun v =>
    match a.lookup v, b.lookup v with
    | none, some val => some (v, val)
    | some val, none => some (v, val)
    | some val1, some val2 => if val1 = val2 then some (v, val1) else none
    | none, none => none)

abbrev absEq (a b : AbsMem) :=
  let allKeys := (a.map (·.1) ++ b.map (·.1)).eraseDups
  allKeys.all (fun k => a.lookup k = b.lookup k)

-- Change one variable value in abstract mem
def updateAbsMem (varname : String) (mx : Option Int) (s : AbsMem) : AbsMem :=
  match mx with
  | none => s.filter (fun (v, _) => v ≠ varname)
  | some x => (varname, x) :: s

-- Apply the MaybeMonad as a functor
abbrev lift2IntInt (op : Int → Int → Int) (a b : Option Int) : Option Int :=
  match a, b with
  | some a', some b' => some (op a' b')
  | _, _ => none
abbrev lift2IntBool (op : Int → Int → Bool) (a b : Option Int) : Option Bool :=
  match a, b with
  | some a', some b' => some (op a' b')
  | _, _ => none
abbrev lift2BoolBool (op : Bool → Bool → Bool) (a b : Option Bool) : Option Bool :=
  match a, b with
  | some a', some b' => some (op a' b')
  | _, _ => none
abbrev lift1BoolBool (op : Bool → Bool) (a : Option Bool) : Option Bool :=
  match a with
  | some a' => some (op a')
  | _ => none

-- Abstractly evaluate arithmetic expressions
def absEvalArith (am : AbsMem) : ArithExpr → Option Int
  | ArithExpr.const n => some n
  | ArithExpr.var x => am.lookup x
  | ArithExpr.add e1 e2 => lift2IntInt (fun a b ↦ a+b) (absEvalArith am e1) (absEvalArith am e2)
  | ArithExpr.sub e1 e2 => lift2IntInt (fun a b ↦ a-b) (absEvalArith am e1) (absEvalArith am e2)
  | ArithExpr.mul e1 e2 => lift2IntInt (fun a b ↦ a*b) (absEvalArith am e1) (absEvalArith am e2)

-- Abstractly evaluate boolean expressions
def absEvalBool (fmem : AbsMem) : BoolExpr → Option Bool
  | BoolExpr.littrue => true
  | BoolExpr.litfalse => false
  | BoolExpr.eq e1 e2 => lift2IntBool (fun a b ↦ a=b) (absEvalArith fmem e1) (absEvalArith fmem e2)
  | BoolExpr.le e1 e2 => lift2IntBool (fun a b ↦ a≤b) (absEvalArith fmem e1) (absEvalArith fmem e2)
  | BoolExpr.and b1 b2 => lift2BoolBool (fun a b ↦ a∧b) (absEvalBool fmem b1) (absEvalBool fmem b2)
  | BoolExpr.not b     => lift1BoolBool (fun a ↦ ¬a) (absEvalBool fmem b)

abbrev approxFixAMIters := 10
def approxFixAM (transform : AbsMem → AbsMem) (fuel : Nat) (m : AbsMem) : AbsMem :=
  match fuel with
  | 0 => absTop
  | fuel'+1 =>
    let m' := transform m
    if absEq m' m then m else approxFixAM transform fuel' m'

def absEvalStmt (stmt : Stmt) (am : AbsMem) : AbsMem :=
  match stmt with
  | Stmt.skip => am
  | Stmt.assign v e => updateAbsMem v (absEvalArith am e) am
  | Stmt.seq s1 s2 => absEvalStmt s2 (absEvalStmt s1 am)
  | Stmt.ifthenelse cond s1 s2 =>
    let thenam := (absEvalStmt s1 am)
    let elseam := (absEvalStmt s2 am)
    match absEvalBool am cond with
    | some true => thenam
    | some false => elseam
    | none => absJoin thenam elseam
  | Stmt.while _ s =>
    approxFixAM (fun am' => absJoin am (absEvalStmt s am')) approxFixAMIters am

-- -- -- -- -- -- -- -- -- --
-- COMPILER W/ CONSTANT PROPAGATION (AND LOCAL SIMPLIFICATION)
-- -- -- -- -- -- -- -- -- --

def propagateArith (am:AbsMem) (e : ArithExpr) : ArithExpr :=
  match e with
  | ArithExpr.var v =>
    match am.lookup v with
    | some val => ArithExpr.const val
    | none => ArithExpr.var v
  | ArithExpr.add e1 e2 => makePlus (propagateArith am e1) (propagateArith am e2)
  | ArithExpr.sub e1 e2 => makeMinus (propagateArith am e1) (propagateArith am e2)
  | ArithExpr.mul e1 e2 => makeTimes (propagateArith am e1) (propagateArith am e2)
  | _ => e

def propagateBool (am:AbsMem) (b : BoolExpr) : BoolExpr :=
  match b with
  | BoolExpr.eq a1 a2 => makeEq (propagateArith am a1) (propagateArith am a2)
  | BoolExpr.le a1 a2 => makeLe (propagateArith am a1) (propagateArith am a2)
  | BoolExpr.and b1 b2 => makeAnd (propagateBool am b1) (propagateBool am b2)
  | BoolExpr.not b => makeNot (propagateBool am b)
  | _ => b

def propagateStmt (am:AbsMem) (stmt : Stmt) : Stmt :=
  match stmt with
  | Stmt.assign v e => Stmt.assign v (propagateArith am e)
  | Stmt.seq s1 s2 => Stmt.seq (propagateStmt am s1) (propagateStmt (absEvalStmt s1 am) s2)
  | Stmt.ifthenelse b s1 s2 => makeIfThenElse (propagateBool am b) (propagateStmt am s1) (propagateStmt am s2)
  | Stmt.while b s =>
    let amfix := absEvalStmt (Stmt.while b s) am
    makeWhile (propagateBool amfix b) (propagateStmt amfix s)
  | _ => stmt

def compilePropagate (s : Stmt) : ObjCode :=
  compileBasic (propagateStmt absTop s)

-- -- -- -- -- -- -- -- -- --
-- LIVENESS ANALYSIS
-- -- -- -- -- -- -- -- -- --

abbrev IdentSet := List String

def free_vars_aexpr (e : ArithExpr) : IdentSet :=
  match e with
  | ArithExpr.const _ => []
  | ArithExpr.var v => [v]
  | ArithExpr.add e1 e2
  | ArithExpr.sub e1 e2
  | ArithExpr.mul e1 e2 => (free_vars_aexpr e1) ++ (free_vars_aexpr e2)

def free_vars_bexpr (b : BoolExpr) : IdentSet :=
  match b with
  | BoolExpr.littrue => []
  | BoolExpr.litfalse => []
  | BoolExpr.eq e1 e2
  | BoolExpr.le e1 e2 => (free_vars_aexpr e1) ++ (free_vars_aexpr e2)
  | BoolExpr.and b1 b2 => (free_vars_bexpr b1) ++ (free_vars_bexpr b2)
  | BoolExpr.not b1    => (free_vars_bexpr b1)

def free_vars_stmt (stmt : Stmt) : IdentSet :=
  match stmt with
  | Stmt.skip => []
  | Stmt.assign _ e => free_vars_aexpr e
  | Stmt.seq s1 s2 => (free_vars_stmt s1) ++ (free_vars_stmt s2)
  | Stmt.ifthenelse b s1 s2 => (free_vars_bexpr b) ++ ((free_vars_stmt s1) ++ (free_vars_stmt s2))
  | Stmt.while b s => (free_vars_bexpr b) ++ (free_vars_stmt s)

def all_vars_stmt (stmt : Stmt) : IdentSet :=
  match stmt with
  | Stmt.skip => []
  | Stmt.assign v e => [v] ++ free_vars_aexpr e
  | Stmt.seq s1 s2 => (all_vars_stmt s1) ++ (all_vars_stmt s2)
  | Stmt.ifthenelse b s1 s2 => (free_vars_bexpr b) ++ ((all_vars_stmt s1) ++ (all_vars_stmt s2))
  | Stmt.while b s => (free_vars_bexpr b) ++ (all_vars_stmt s)

abbrev approxFixDCIters := 10
def approxFixDCInner (transform : IdentSet → IdentSet) (fuel : Nat) (init : IdentSet) : IdentSet :=
  match fuel with
  | 0 => init
  | fuel'+1 => approxFixDCInner transform fuel' (transform init)
def approxFixDC (transform : IdentSet → IdentSet) (fuel : Nat) (default init : IdentSet) : IdentSet :=
  let approx := approxFixDCInner transform fuel init
  if approx = transform approx then approx else default

def live_thru (stmt : Stmt) (live_after : IdentSet) : IdentSet :=
  match stmt with
  | Stmt.skip => live_after
  | Stmt.assign v e => if v∈live_after then (live_after.eraseDups.erase v) ++ (free_vars_aexpr e) else live_after
  | Stmt.seq s1 s2 => live_thru s1 (live_thru s2 live_after)
  | Stmt.ifthenelse b s1 s2 => (free_vars_bexpr b) ++ ((live_thru s1 live_after) ++ (live_thru s2 live_after))
  | Stmt.while b s =>
    let live_after' := (free_vars_bexpr b) ++ live_after
    let default := (free_vars_stmt (Stmt.while b s)) ++ live_after -- TODO
    approxFixDC (fun ll ↦ live_after' ++ (live_thru s ll)) approxFixDCIters default []

-- -- -- -- -- -- -- -- -- --
-- COMPILER W/ DEADCODE REMOVAL (AND CONSTANT PROPAGATION AND LOCAL SIMPLIFICATION)
-- -- -- -- -- -- -- -- -- --

def buryStmt (vars_to_care_about : IdentSet) (stmt : Stmt) : Stmt :=
  match stmt with
  | Stmt.skip => Stmt.skip
  | Stmt.assign v e => if v ∈ vars_to_care_about then Stmt.assign v e else Stmt.skip
  | Stmt.seq s1 s2 => Stmt.seq (buryStmt (live_thru s2 vars_to_care_about) s1) (buryStmt vars_to_care_about s2)
  | Stmt.ifthenelse b s1 s2 => Stmt.ifthenelse b (buryStmt vars_to_care_about s1) (buryStmt vars_to_care_about s2)
  | Stmt.while b s => Stmt.while b (buryStmt (live_thru (Stmt.while b s) vars_to_care_about) s)

def compileBury (s : Stmt) : ObjCode :=
  compileBasic (propagateStmt absTop (buryStmt (all_vars_stmt s) s))

-- ##########################
-- CORRECTNESS
-- ##########################

-- -- -- -- -- -- -- -- -- --
-- OPTIMIZED COMPILER CORRECTNESS THEOREMS
-- -- -- -- -- -- -- -- -- --

abbrev absMatches (a : AbsMem) (b : Mem) :=
  a.all (fun (x, v) => lookupMem x b 0 = v)

abbrev agree (ll : IdentSet) (mem1 mem2 : Mem) :=
  ∀ x∈ll, lookupMem x mem1 0 = lookupMem x mem2 0

-- executing optimizingly-compiled code yields same result as high-level interpretation of source
-- theorem bury_preserve_value
--     (stmt : Stmt) (mem_init : Mem) (mem_final : Mem)
--     (hhigh : pathStmtE stmt mem_init mem_final) :
--     ∃ (steps:Nat) (pc:Nat),
--       execCode (compileBury stmt) steps (some {mem:=mem_init, stack:=[], pc:=0})
--       = (some {mem:=mem_final, stack:=[], pc:=pc}) := by
--   sorry

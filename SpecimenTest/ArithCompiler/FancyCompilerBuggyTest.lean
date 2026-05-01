import SpecimenTest.ArithCompiler.FancyCompilerBuggy
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Testable
import Specimen.GeneratorCombinators
import Specimen.EnumeratorCombinators
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveEnum
import Plausible.DeriveShrinkable

/-! Tests that use derived generators and checkers to find bugs in the buggy arithmetic compiler. -/

open Plausible
open Plausible.Arbitrary

deriving instance Arbitrary for ArithExpr
deriving instance Arbitrary for BoolExpr
deriving instance Arbitrary for Stmt

deriving instance Enum for ArithExpr
deriving instance Enum for BoolExpr
deriving instance Enum for Stmt
deriving instance Enum for Mem

def mem0 : Mem := []

def memEq (m1 m2 : Mem) : Bool :=
  let allKeys := (m1.map (·.1) ++ m2.map (·.1)).eraseDups
  allKeys.all (fun k => m1.lookup k == m2.lookup k)

def compiler_correct (stmt : Stmt) : Bool :=
  let steps := 1000
  let compiled := compileBury stmt
  let state := execCode compiled steps (some {mem := mem0, stack := [], pc := 0})
  let mstate := pathStmt stmt steps mem0
  match mstate,state with
  | _,none
  | none,_ =>
    dbg_trace "WARNING: success may be spurious due to running out of fuel"
    true
  | some ms, some finalState =>
    memEq finalState.mem ms

-- This is the big-step semantics from the inductive relation, derived to
-- be an enumerator: It will "run" Eval on m and s and produce m2.
#guard_msgs(drop info, drop warning) in
derive_enumerator (fun m s => ∃ m2, Eval m s m2)

-- This is our correctness statement from above, but using the enumerator
def compiler_correct_enum (stmt : Stmt) : Bool :=
  let steps := 1000
  let compiled := compileBury stmt
  let state := execCode compiled steps (some {mem := mem0, stack := [], pc := 0})
  let enumResult := EnumSizedSuchThat.enumSizedST (fun m2 => Eval mem0 stmt m2) steps
  let mstate := (LazyList.take 1 $ enumResult steps).head?.bind (·.toOption)
  match mstate,state with
  | _,none
  | none,_ =>
    -- the following is most likely to happen for loopy programs; will always
    -- happen for infinite loops (while true do s ...)
    -- dbg_trace "WARNING: success may be spurious due to running out of fuel"
    true
  | some ms, some finalState =>
    let result := memEq finalState.mem ms
    if !result then
      dbg_trace s!"FAILURE: stmt = {repr stmt}"
      dbg_trace s!"  finalState.mem = {repr finalState.mem}"
      dbg_trace s!"  ms = {repr ms}"
      dbg_trace s!"  finalState.stack = {repr finalState.stack}"
      dbg_trace s!"  finalState.pc = {repr finalState.pc}"
      result
    else
      result

-- The following shows the bug in the compiler (shrunk from a larger counterexample
-- found by Plausible, using the auto-derived Shrinkable instance for Stmt)
def s := Stmt.seq
  (Stmt.ifthenelse
    (BoolExpr.not (BoolExpr.eq (ArithExpr.const 0) (ArithExpr.add (ArithExpr.var "") (ArithExpr.const 1))))
    (Stmt.assign "" (ArithExpr.var ""))
    (Stmt.assign "" (ArithExpr.const 1)))
  (Stmt.assign "" (ArithExpr.var ""))

/--
info: false
-/
#guard_msgs in #eval compiler_correct s

deriving instance Shrinkable for ArithExpr, BoolExpr, Stmt

instance : SampleableExt Stmt := inferInstance

-- #eval Testable.check (∀ stmt : Stmt, compiler_correct_enum stmt)
--   (cfg := {numInst := 100, maxSize := 5, quiet := true})
  -- (cfg := {numInst := 10, maxSize := 5, quiet := false, traceSuccesses := true})

/-- Repeatedly shrink a failing input by picking the first shrink candidate that still
    fails, then recursing. This mirrors `Plausible.minimizeAux`: termination is guaranteed
    because `Shrinkable.shrink` produces strictly smaller values, but Lean can't prove
    this structurally so we mark it `partial`. -/
partial def shrinkLoop (test : Stmt → Bool) (s : Stmt) : Stmt :=
  match (Shrinkable.shrink s).find? (fun s' => !test s') with
  | some s' => shrinkLoop test s'
  | none => s

-- #eval do
--   let s' := shrinkLoop compiler_correct s
--   IO.println s!"Shrunk failing input:\n{repr s'}"

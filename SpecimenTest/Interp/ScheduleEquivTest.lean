import Specimen.Interp.FromCompiledAgreement
import SpecimenTest.Interp.BSTInterpTest

/-!
# What the schedule comparator must tell apart, and what it may equate

`Specimen.Interp.ScheduleEquiv.compareSchedules` decides whether an interpreter schedule and a compiled one are
the same generator. It is only useful if it is **sound**, so each case below that must come out
*different* is one a comparator taking an easier route calls equal:

* inputs swapped between two same-shaped matches, which alpha-renaming by first occurrence cannot see;
* outputs bound from different inputs, which only comparing what a schedule returns catches;
* a type argument at a polymorphic call, and an unconstrained `List Nat` against a `List String`, both
  invisible once `TyCtor`s are erased;
* a dictionary the interpreter passes as a value where the compiled code resolves an instance, which no
  syntactic comparator can see because both sides spell it identically.

The cases that must come out *the same* are the reasons a sound comparator still has to normalise:
reordered prologue matches, outputs made equal by an `Eq` check (Cedar's `Lub.ext`), constructor
parameters the deriver spells out, an abbreviation reified as a `FuncApp`, and each side's own name for
its recursive call.

Then, end to end: on `BST`, the closure built from the deriver's book agrees with the deriver on every
generator constructor they share.
-/

open Lean Schedules Specimen Specimen.Interp

namespace SpecimenTest.ScheduleEquiv

/-- A producer the hand-written schedules call: `EqvP x ys z`, with `z` the output. -/
inductive EqvP : Nat → List Nat → Nat → Prop where
  | mk : ∀ x ys, EqvP x ys 0

/-- Polymorphic, like Cedar's `SetContains`. -/
inductive EqvMem {α : Type} : α → List α → Prop where
  | here : ∀ x xs, EqvMem x (x :: xs)

/-- Polymorphic with a dictionary, like Cedar's `MapNotContainsKey`. -/
inductive EqvNotIn {α : Type} [DecidableEq α] : α → List α → Prop where
  | nil : ∀ k, EqvNotIn k []

/-- The modes under test. Their constructors do not matter, since the schedules are written by hand. -/
inductive EqvQ : List Nat → List Nat → Nat → Prop where
  | mk : ∀ a b, EqvQ a b 0

inductive EqvR : Option Nat → Option Nat → Option Nat → Prop where
  | mk : ∀ x, EqvR (some x) (some x) (some x)

inductive EqvS : Nat × Nat → Nat → Prop where
  | mk : ∀ p, EqvS (p, p) p

def shapes : Meta.MetaM ScheduleEquiv.Shapes :=
  ScheduleEquiv.Shapes.build [``List.cons, ``List.nil, ``Prod.mk, ``Option.some, ``Nat.succ]
    [``EqvP, ``EqvMem, ``EqvNotIn, ``EqvQ, ``EqvR, ``EqvS]

/-- The interpreter names argument `i` `<letter>_1` and the deriver `<letter>_7`. The spellings differ,
    so any agreement below comes from pinning by position. -/
def sides (rel : Name) (arity : Nat) (outs : List Nat) (trailing : List (Name × List Nat)) :
    ScheduleEquiv.Side × ScheduleEquiv.Side :=
  let letters := ["a", "b", "c", "d"]
  let names := fun (sfx : String) =>
    (List.range arity).map (fun i => Name.mkSimple s!"{letters.getD i "z"}_{sfx}")
  ({ reading := .interp, rel := rel, argNames := names "1", outputIndices := outs,
     selfFn := `aux_eqv, trailingLeaves := trailing },
   { reading := .compiled, rel := rel, argNames := names "7", outputIndices := outs,
     selfFn := `aux_arb })

def gen (outs : List ConstructorExpr) : ScheduleSort := .ProducerSchedule .Generator outs
def u (n : Name) : ConstructorExpr := .Unknown n
def pv (n : Name) : _root_.Pattern := .UnknownPattern n
def pc (c : Name) (ps : List _root_.Pattern) : _root_.Pattern := .CtorPattern c ps
def mt (v : Name) (p : _root_.Pattern) : ScheduleStep := .Match .allowImplicit v p
def mtx (v : Name) (p : _root_.Pattern) : ScheduleStep := .Match .allExplicit v p
def st (outs : List Name) (r : Name) (args : List ConstructorExpr) : ScheduleStep :=
  .SuchThat (outs.map (·, none)) (.NonRec (r, args)) .Generator
def recSt (outs : List Name) (f : Name) (args : List ConstructorExpr) : ScheduleStep :=
  .SuchThat (outs.map (·, none)) (.Rec f args) .Generator
def eqChk (args : List ConstructorExpr) : ScheduleStep := .Check (.NonRec (``Eq, args)) true
def unc (v : Name) (ty : HypothesisExpr) : ScheduleStep := .Unconstrained v (.NonRec ty) .Generator
def nat : ConstructorExpr := .TyCtor ``Nat []

structure Case where
  label : String
  rel : Name
  arity : Nat
  outs : List Nat
  interp : Schedule
  compiled : Schedule
  trailing : List (Name × List Nat) := []
  same : Bool

def consP (x xs : Name) : _root_.Pattern := pc ``List.cons [pv x, pv xs]

def cases : List Case := [
  { label := "inputs swapped between two same-shaped matches", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([mt `a_1 (consP `x `xs), mt `b_1 (consP `y `ys), st [`z] ``EqvP [u `x, u `ys, u `z]],
      gen [u `z]),
    compiled := ([mt `b_7 (consP `x `xs), mt `a_7 (consP `y `ys), st [`z] ``EqvP [u `x, u `ys, u `z]],
      gen [u `z]),
    same := false },
  { label := "the same prologue matches in the other order", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([mt `a_1 (consP `x `xs), mt `b_1 (consP `y `ys), st [`z] ``EqvP [u `x, u `ys, u `z]],
      gen [u `z]),
    compiled := ([mt `b_7 (consP `y `ys), mt `a_7 (consP `x `xs), st [`z] ``EqvP [u `x, u `ys, u `z]],
      gen [u `z]),
    same := true },
  { label := "outputs read from different inputs, made equal by a check (Lub.ext)", rel := ``EqvR,
    arity := 3, outs := [2],
    interp := ([mt `a_1 (pc ``Option.some [pv `x]), mt `b_1 (pc ``Option.some [pv `x_dup]),
        eqChk [u `x, u `x_dup]], gen [.Ctor ``Option.some [nat, u `x]]),
    compiled := ([mt `b_7 (pc ``Option.some [pv `x]), mt `a_7 (pc ``Option.some [pv `x_1]),
        eqChk [nat, u `x_1, u `x]], gen [.Ctor ``Option.some [u `x]]),
    same := true },
  { label := "outputs read from different inputs, with no check", rel := ``EqvR, arity := 3,
    outs := [2],
    interp := ([mt `a_1 (pc ``Option.some [pv `x]), mt `b_1 (pc ``Option.some [pv `x_dup])],
      gen [.Ctor ``Option.some [nat, u `x]]),
    compiled := ([mt `b_7 (pc ``Option.some [pv `x]), mt `a_7 (pc ``Option.some [pv `x_1])],
      gen [.Ctor ``Option.some [u `x]]),
    same := false },
  { label := "a dictionary passed as a value to an interpreted callee", rel := ``EqvQ, arity := 3,
    outs := [2],
    interp := ([st [`k] ``EqvNotIn [nat, .FuncApp ``instDecidableEqNat [], u `k, u `a_1]], gen [u `k]),
    compiled := ([st [`k] ``EqvNotIn [nat, .FuncApp ``instDecidableEqNat [], u `k, u `a_7]], gen [u `k]),
    same := false },
  { label := "the same dictionary, to a leaf that reads trailing arguments", rel := ``EqvQ, arity := 3,
    outs := [2],
    interp := ([st [`k] ``EqvNotIn [nat, .FuncApp ``instDecidableEqNat [], u `k, u `a_1]], gen [u `k]),
    compiled := ([st [`k] ``EqvNotIn [nat, .FuncApp ``instDecidableEqNat [], u `k, u `a_7]], gen [u `k]),
    trailing := [(``EqvNotIn, [2])], same := true },
  { label := "a polymorphic call at another type", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([st [`k] ``EqvMem [nat, u `k, u `a_1]], gen [u `k]),
    compiled := ([st [`k] ``EqvMem [.TyCtor ``String [], u `k, u `a_7]], gen [u `k]),
    same := false },
  { label := "a type argument the deriver reifies as a FuncApp", rel := ``EqvQ, arity := 3,
    outs := [2],
    interp := ([st [`k] ``EqvMem [nat, u `k, u `a_1]], gen [u `k]),
    compiled := ([st [`k] ``EqvMem [.FuncApp ``Nat [], u `k, u `a_7]], gen [u `k]),
    same := true },
  { label := "a type argument the interpreter reifies as a FuncApp, and so passes as a value",
    rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([st [`k] ``EqvMem [.FuncApp ``Nat [], u `k, u `a_1]], gen [u `k]),
    compiled := ([st [`k] ``EqvMem [nat, u `k, u `a_7]], gen [u `k]),
    same := false },
  { label := "a repeated variable the interpreter leaves non-linear (binaryAppEqLitSame)",
    rel := ``EqvS, arity := 2, outs := [1],
    interp := ([mt `a_1 (pc ``Prod.mk [pv `p, pv `p])], gen [u `p]),
    compiled := ([mtx `a_7 (pc ``Prod.mk [pc ``Nat [], pc ``Nat [], pv `p_1, pv `p]),
        eqChk [nat, u `p_1, u `p]], gen [u `p]),
    same := false },
  { label := "the same repeated variable, linearised with an Eq check", rel := ``EqvS, arity := 2,
    outs := [1],
    interp := ([mt `a_1 (pc ``Prod.mk [pv `p, pv `p_dup]), eqChk [u `p, u `p_dup]], gen [u `p]),
    compiled := ([mtx `a_7 (pc ``Prod.mk [pc ``Nat [], pc ``Nat [], pv `p_1, pv `p]),
        eqChk [nat, u `p_1, u `p]], gen [u `p]),
    same := true },
  { label := "unconstrained List Nat against List String", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([unc `x (``List, [nat])], gen [u `x]),
    compiled := ([unc `x (``List, [.TyCtor ``String []])], gen [u `x]),
    same := false },
  { label := "unconstrained at the same type", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([unc `x (``List, [nat])], gen [u `x]),
    compiled := ([unc `x (``List, [nat])], gen [u `x]),
    same := true },
  { label := "each side's own name for its recursive call", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([recSt [`z] `aux_eqv [u `a_1, u `b_1]], gen [u `z]),
    compiled := ([recSt [`z] `aux_arb [u `a_7, u `b_7]], gen [u `z]),
    same := true },
  { label := "a call to some other function", rel := ``EqvQ, arity := 3, outs := [2],
    interp := ([recSt [`z] `aux_other [u `a_1, u `b_1]], gen [u `z]),
    compiled := ([recSt [`z] `aux_arb [u `a_7, u `b_7]], gen [u `z]),
    same := false },
  { label := "constructor parameters spelled out in an allExplicit match", rel := ``EqvQ, arity := 3,
    outs := [2],
    interp := ([mt `a_1 (consP `h `t)], gen [u `h]),
    compiled := ([mtx `a_7 (pc ``List.cons [pc ``Nat [], pv `h, pv `t])], gen [u `h]),
    same := true } ]

/-- info: [schedule-equiv] 16 cases, each as expected -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let sh ← Elab.Command.liftTermElabM shapes
  let mut bad : List String := []
  for c in cases do
    let (i, k) := sides c.rel c.arity c.outs c.trailing
    let v := ScheduleEquiv.compareSchedules sh i k c.interp c.compiled
    let ok := match v with
      | .same => c.same
      | .differ .. => !c.same
      | .outside _ => false
    unless ok do bad := bad ++ [s!"{c.label}: {repr v}"]
  unless bad.isEmpty do
    throwError "comparator verdicts changed:\n{"\n".intercalate bad}"
  IO.println s!"[schedule-equiv] {cases.length} cases, each as expected"

open SpecimenTest.InterpBST in
-- End to end on `BST`. This is the same closure `FromCompiledTest` checks by raw equality, now read by
-- each side's evaluator and with the returned outputs compared too. `Between`'s `LE.le` check carries a
-- `Nat` and an `instLENat`, and it agrees only because the `LE.le` leaf reads its trailing arguments.
/-- info: [schedule-equiv] BST closure: 4 of 4 compared generator constructor(s) agree with the deriver -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let choice ← deriveChoice bstKey
  let sh ← Elab.Command.liftTermElabM (choice.shapes specs)
  match leaves.deriveClosureWith specs [bstKey] choice.generatorBook with
  | .error e => throwError "the closure from the deriver's book did not build: {e}"
  | .ok env =>
    let a := choice.agreement sh leaves env specs
    unless a.differ.isEmpty && a.outside.isEmpty && a.compared == 4 do
      throwError a.render
    IO.println s!"[schedule-equiv] BST closure: {a.agree} of {a.compared} compared generator \
      constructor(s) agree with the deriver"

end SpecimenTest.ScheduleEquiv

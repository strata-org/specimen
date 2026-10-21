import SpecimenTest.BasaltPort.GradedRuleAdequacy
import Specimen.Schedules
import Specimen.Interp.Value

/-!
# `Schedules.ScheduleStep → RuleShape.Body`, as a real Lean function

`GradedRuleAdequacy.lean` proves adequacy for rules presented as `Body ι α` data, and its module
docstring carries the `ScheduleStep → Body` correspondence as a **hand-checked table**. Its own
closing section names writing that table as a Lean function as the next step. This file writes it,
and then says precisely how much of "the `Body` denotes the same relation the schedule was derived
from" is provable and how much is not.

The answer is worse than the table suggests, in one specific way that is worth stating before any of
the code: **the grading rows of that table are not an erasure of anything Specimen emits.** They are
a design proposal. See §6.1. Everything else in the table does check out, and §3–§5 check it.

## What is here

* §1 Total re-implementations of the interpreter helpers `translate` needs
  (`evalConstructorExpr`, `isTypeOrDict`, `matchPattern`), because the shipped ones are `partial def`
  and therefore *opaque* — see §6.2. Differential `#guard`s against the shipped ones.
* §2 `TransEnv`, the semantic environment the translation cannot do without, and why.
* §3 `stepBody` / `translate` / `translateRule` / `translateRules`: the translation, on the real
  `Schedules.ScheduleStep`, as a `List.foldr` in the same shape as `MExp.scheduleToMExp`.
* §4 `SatStep` / `Sat`, a declarative reading of a step list that mentions no `Grade`, no `pay` and
  no carrier, and `holdsR_translate`, which says the translation agrees with it. This is the
  faithfulness statement that *is* provable, and §4's preamble says exactly how much it buys.
* §5 The non-circular fragment: for schedules built only from `.Check` and `.Match`,
  `denoteL_checkOnly` equates the graded denotation of the translated body with an independently
  written three-valued checker walk in the shape of `CheckEnum.runCheckSteps`. §5.1 runs a worked
  two-constructor schedule end to end through `enumL`, so that none of this is vacuous.
* §6 Where it breaks. Six obstructions, each named, each with whatever mechanical evidence can be
  given for it.
* §7 The obligations `translate` discharges: `BodySound`/`BodyComplete` for a translated schedule
  reduce to per-name obligations on `TransEnv`, so a schedule plus a verified environment gives
  `adequateL` its `hs`/`hc` for free.

## Target choice

`Body ι α` is instantiated at `ι := Name × List Val` and `α := List Val`:

* `α = List Val` because that is the interpreter's own producer result type
  (`ExceptT GenError Enumerator (List Val)`) and because `.SuchThat` binds a *list* of outputs, which
  a single-output `call` could not deliver without tupling at every call site.
* `ι = Name × List Val` — the callee's function name together with its evaluated **input**
  arguments. `Preschedule.lowerPremise` builds `.Rec f inputArgs` / `.MutRec f inputArgs` with the
  output positions already filtered out, so the input arguments are exactly what identifies the
  recursive sub-goal. This matches `GradedStlcAdequacy`'s `Ix = List type × type`, which is also the
  relation's inputs.

`Val` is the *real* `Specimen.Interp.Val` and `ValEnv` the *real* `Std.HashMap Unknown Val`; nothing
about the untyped value domain is re-modelled here. That is deliberate: the interesting failure is
that `Val` is untyped, and substituting a nicer domain would hide it.
-/

open Basalt RuleShape Schedules Specimen.Interp
open Lean (Name Literal)

namespace ScheduleTranslate

/-! # §1 Total replacements for the interpreter's opaque helpers

`Specimen.Interp.evalConstructorExpr`, `matchPattern` and `isTypeOrDict` (in
`Specimen/Interp/Value.lean`) are all written with `partial def` — nested `List.mapM`/`filter` recursion that Lean's
structural checker does not see through, even though each is in fact structural. A `partial def`
elaborates to an **`opaque` constant**: `#print` shows `opaque f : …`, there are no equation lemmas,
and `unfold`/`simp [f]` fail. So they cannot appear in a theorem.

The functions below are structurally-recursive transcriptions, with the list recursion made explicit.
They are *not* proved equal to the shipped ones — that is impossible, for exactly the reason above —
so they are followed by differential `#guard`s, which do run the shipped code. `bindVarsT` and
`collapse` are transcriptions of `Interp.Gen.bindVars`/`collapseOutputs` for a different reason: those
are already total, but live in a module that pulls in `Plausible.Gen`.
-/

mutual
/-- `Specimen.Interp.isTypeOrDict`, total. The shipped version tests
`(valueArgs args).all (isTypeOrDict funcs)`; since every `isTypeLevel` expression passes the test in
the fallback branch, that is the same as `args.all (isTypeOrDict funcs)`, which removes the `filter`
and makes the recursion structural. -/
def isTOD (funcs : FuncTable) : ConstructorExpr → Bool
  | .FuncApp f args => !funcs.contains f && isTODs funcs args
  | e => isTypeLevel e
/-- List companion of `isTOD`. -/
def isTODs (funcs : FuncTable) : List ConstructorExpr → Bool
  | [] => true
  | e :: es => isTOD funcs e && isTODs funcs es
end

mutual
/-- `Specimen.Interp.evalConstructorExpr`, total. -/
def evalCE (funcs : FuncTable) (ρ : ValEnv) : ConstructorExpr → Except String Val
  | .Unknown u =>
    match ρ[u]? with
    | some v => .ok v
    | none => match funcs[u]? with
      | some f => f []
      | none => .error s!"unbound variable '{u}'"
  | .Lit l => .ok (.lit l)
  | .Ctor c args => (Val.mkCtor c) <$> evalCEs funcs ρ args
  | .TyCtor c args => (Val.mkCtor c) <$> evalCEs funcs ρ args
  | .FuncApp f args =>
    match funcs[f]? with
    | some fn => evalCEs funcs ρ args >>= fn
    | none =>
      if isTODs funcs args then .ok (.ctor f [])
      else .error s!"no interpretation registered for function '{f}'"
  | .CSort _ => .error "cannot evaluate a sort to a runtime value"
  | .Hole => .error "cannot evaluate a hole to a runtime value"
/-- List companion of `evalCE`. Drops the type-level positions inline, which is what makes the
recursion structural: `(valueArgs args).mapM f` is not a structural call, `evalCEs args` is. -/
def evalCEs (funcs : FuncTable) (ρ : ValEnv) : List ConstructorExpr → Except String (List Val)
  | [] => .ok []
  | e :: es =>
    if isTypeLevel e then evalCEs funcs ρ es
    else match evalCE funcs ρ e with
      | .error m => .error m
      | .ok v => (v :: ·) <$> evalCEs funcs ρ es
end

mutual
/-- `Specimen.Interp.matchPattern`, total. -/
def matchPat : Pattern → Val → ValEnv → Option ValEnv
  | .UnknownPattern u, v, ρ => if u == `_ then some ρ else some (ρ.insert u v)
  | .LitPattern l, v, ρ => if v == .lit l then some ρ else none
  | .CtorPattern c ps, v, ρ =>
    match c, ps, v with
    | ``Nat.zero, [], .lit (.natVal 0) => some ρ
    | ``Nat.succ, [p'], .lit (.natVal (n + 1)) => matchPat p' (.lit (.natVal n)) ρ
    | _, _, .ctor c' args =>
      if c == c' && ps.length == args.length then matchPats ps args ρ else none
    | _, _, _ => none
/-- List companion of `matchPat`. -/
def matchPats : List Pattern → List Val → ValEnv → Option ValEnv
  | [], [], ρ => some ρ
  | p :: ps, v :: vs, ρ =>
    match matchPat p v ρ with
    | some ρ' => matchPats ps vs ρ'
    | none => none
  | _, _, _ => none
end

/-- `Interp.Gen.bindVars`, total (it already was; restated so this file does not import `Gen`,
which pulls in `Plausible.Gen`). -/
def bindVarsT (names : List Name) (vals : List Val) (ρ : ValEnv) : Option ValEnv :=
  if names.length = vals.length then
    some ((names.zip vals).foldl (fun acc (n, v) => acc.insert n v) ρ)
  else none

/-- `Interp.Gen.collapseOutputs`: what an `.Unconstrained` step binds when its source returned
several values. -/
def collapse : List Val → Val
  | [v] => v
  | vs => Val.tuple vs

/-! ### Differential tests against the shipped `partial def`s

Not proofs — `#guard` runs the compiled code. This is the only check available on the transcription,
and it is the honest one to offer. -/

private def ρ₀ : ValEnv := (∅ : ValEnv).insert `x (.lit (.natVal 3)) |>.insert `y (.ctor `A [])
private def f₀ : FuncTable := ∅

-- `evalCE` agrees with the shipped `evalConstructorExpr` on a spread of shapes: variables,
-- literals, constructors (with the `Nat` normalisation), type-level arguments that must be dropped,
-- nullary unregistered `FuncApp`s that become opaque atoms, and the two error cases.
#guard (evalCE f₀ ρ₀ (.Unknown `x)).toOption == (evalConstructorExpr f₀ ρ₀ (.Unknown `x)).toOption
#guard (evalCE f₀ ρ₀ (.Unknown `z)).toOption == (evalConstructorExpr f₀ ρ₀ (.Unknown `z)).toOption
#guard (evalCE f₀ ρ₀ (.Lit (.natVal 7))).toOption
        == (evalConstructorExpr f₀ ρ₀ (.Lit (.natVal 7))).toOption
#guard (evalCE f₀ ρ₀ (.Ctor ``Nat.succ [.Lit (.natVal 4)])).toOption
        == (evalConstructorExpr f₀ ρ₀ (.Ctor ``Nat.succ [.Lit (.natVal 4)])).toOption
#guard (evalCE f₀ ρ₀ (.Ctor ``List.cons [.TyCtor ``Nat [], .Unknown `x, .Ctor ``List.nil []])).toOption
        == (evalConstructorExpr f₀ ρ₀
              (.Ctor ``List.cons [.TyCtor ``Nat [], .Unknown `x, .Ctor ``List.nil []])).toOption
#guard (evalCE f₀ ρ₀ (.FuncApp `instLENat [])).toOption
        == (evalConstructorExpr f₀ ρ₀ (.FuncApp `instLENat [])).toOption
#guard (evalCE f₀ ρ₀ (.FuncApp `List.length [.Unknown `y])).toOption
        == (evalConstructorExpr f₀ ρ₀ (.FuncApp `List.length [.Unknown `y])).toOption
#guard (evalCE f₀ ρ₀ .Hole).toOption == (evalConstructorExpr f₀ ρ₀ .Hole).toOption

-- `matchPat` agrees with the shipped `matchPattern`: variable binding, the wildcard, literal
-- patterns, constructor patterns, arity mismatch, and the `Nat.succ`-against-literal case.
private def sameMatch (p : Pattern) (v : Val) : Bool :=
  let l := (matchPat p v ρ₀).map (fun ρ => (ρ[`n]?, ρ[`m]?))
  let r := (matchPattern p v ρ₀).map (fun ρ => (ρ[`n]?, ρ[`m]?))
  l == r
#guard sameMatch (.UnknownPattern `n) (.lit (.natVal 9))
#guard sameMatch (.UnknownPattern `_) (.lit (.natVal 9))
#guard sameMatch (.LitPattern (.natVal 9)) (.lit (.natVal 9))
#guard sameMatch (.LitPattern (.natVal 8)) (.lit (.natVal 9))
#guard sameMatch (.CtorPattern ``Nat.succ [.UnknownPattern `n]) (.lit (.natVal 9))
#guard sameMatch (.CtorPattern ``Nat.zero []) (.lit (.natVal 0))
#guard sameMatch (.CtorPattern ``Nat.zero []) (.lit (.natVal 1))
#guard sameMatch (.CtorPattern `Pair [.UnknownPattern `n, .UnknownPattern `m])
        (.ctor `Pair [.lit (.natVal 1), .lit (.natVal 2)])
#guard sameMatch (.CtorPattern `Pair [.UnknownPattern `n]) (.ctor `Pair [.lit (.natVal 1)])
#guard sameMatch (.CtorPattern `Pair [.UnknownPattern `n])
        (.ctor `Pair [.lit (.natVal 1), .lit (.natVal 2)])
#guard sameMatch (.CtorPattern `Other [.UnknownPattern `n]) (.ctor `Pair [.lit (.natVal 1)])

/-! # §2 The semantic environment, and why `translate` cannot do without one

`Body`'s `aux` premise carries an **executable producer** `p : Nat → Lv β`, a **host type** `β`, and
a **`Prop`** `P : β → Prop`. A `.NonRec` step carries none of those: it carries a `Name` and a
`List ConstructorExpr`. Recovering a type from a `Name` is an `Environment` lookup — a `MetaM`
operation, not a pure function — and recovering a `Prop` is worse, because `ConstructorExpr` is
untyped and the `Prop` it spells may not even be well-formed. The same holds for `.Check`: `Body`'s
`check` wants a `V` and a `Prop`, and `.Check` gives a `Source`.

So there is no function `Schedule → Body ι α`. There is a function

    Schedule → (interpretation of names) → ValEnv → Body ι α

and `TransEnv` is that interpretation. This is not a defect of the translation; it is the same
factoring `Specimen.Correctness.Reflect`'s `RelSpec` uses (`Vars : Type`, `side : Vars → Prop` —
host types and host `Prop`s supplied from outside) and the same one `Interp.InterpEnv` uses at
runtime (`enumProducers`, `checkers`, `funcs` — all registered, none derived from the IR). What it
*does* mean is that `translate` is faithful only relative to `TransEnv`, and that `TransEnv`'s
fields are where the untyped-to-typed gap lives. §6.3 is precise about it.

`β` is taken to be `Val` for a leaf producer and `List Val` for a constrained sub-producer, matching
the interpreter (`lookupEnum : … → Enumerator Val`, `interpEnumConstrained : … → Enumerator (List
(Name × Val))`). Nothing forces that — `aux`'s `β` is existential per node, so a `TransEnv` could
supply host-typed producers instead; it just could not supply them *from the IR*.
-/

/-- A producer-call index: the callee's function name plus its evaluated input arguments. -/
abbrev RelIx := Name × List Val

/-- The interpretation of names that the translation needs. Each field corresponds to a lookup the
runtime interpreter performs in `Interp.InterpEnv`, lifted to the graded carrier. -/
structure TransEnv where
  /-- `InterpEnv.funcs`: interpretations of `ConstructorExpr.FuncApp` heads. -/
  funcs : FuncTable
  /-- The inductive whose schedule this is. `countSizeConsumingCalls` measures against it. -/
  target : Name
  /-- `InterpEnv.lookupEnum`: the leaf enumeration for an *unconstrained* premise of type `hyp`,
  lifted to `Lv` and indexed by leaf budget. `none` is the interpreter's "no enumerator registered"
  misconfiguration error. -/
  leaf : HypothesisExpr → Option (Nat → Lv Val)
  /-- What `leaf hyp` claims to produce: `aux`'s `P`. Read off the *name*, not the code, which is
  the one place where a `TransEnv` can lie; `RuleShape.specOf` is the alternative that cannot, at
  the cost of saying nothing about the relation. -/
  leafSpec : HypothesisExpr → Val → Prop
  /-- `Interp.interpEnumConstrained`: solve `hyp` for `vars` under the current bindings. Covers the
  cross-SCC case, the other-mode case, and the built-in `Eq` producer (which the interpreter
  special-cases to a one-element enumeration; see `detP` in §6.1). -/
  sub : HypothesisExpr → List Name → ValEnv → Option (Nat → Lv (List Val))
  /-- What `sub hyp vars ρ` claims: this tuple of solutions satisfies the premise. -/
  subSpec : HypothesisExpr → List Name → ValEnv → List Val → Prop
  /-- `Interp.checkSourceIn`, as a Kleene verdict. `.ok true`/`.ok false`/`.error` map onto
  `V.yes`/`V.no`/`V.inconclusive`. -/
  verdict : Source → ValEnv → V
  /-- The proposition the verdict decides. -/
  verdictSpec : Source → ValEnv → Prop
  /-- The deriver's grading choice for auxiliary producers. `.sized` is the only sound-and-complete
  option; see §6.1 and `not_unsized_detP`. -/
  grade : Grade := .sized

/-! ### Polarity, and Kleene conjunction

`.Check src polarity` with `polarity = false` is the interpreter's `DecOpt.negOpt verdict`; `negV`
is that on `V`. `andV` is `DecOpt.andOpt` on `V` — needed in §5, not by `translate`. -/

/-- `DecOpt.negOpt` on verdicts: `yes ↔ no`, `inconclusive` fixed. -/
def negV : V → V
  | .yes => .no
  | .no => .yes
  | .inconclusive => .inconclusive

/-- `DecOpt.andOpt` on verdicts: Kleene strong conjunction. -/
def andV : V → V → V
  | .yes, b => b
  | .no, _ => .no
  | .inconclusive, .no => .no
  | .inconclusive, _ => .inconclusive

/-- The verdict a `.Check` step actually contributes. -/
def polV : Bool → V → V
  | true, v => v
  | false, v => negV v

/-- The proposition a `.Check` step actually asserts. -/
def polP : Bool → Prop → Prop
  | true, P => P
  | false, P => ¬ P

/-! # §3 The translation -/

/-- The index a `.Rec`/`.MutRec` source names, once its input arguments are evaluated. -/
def ixOf (E : TransEnv) (f : Name) (args : List ConstructorExpr) (ρ : ValEnv) : Option RelIx :=
  match evalCEs E.funcs ρ args with
  | .ok vals => some (f, vals)
  | .error _ => none

/-- The epilogue: `MExp.scheduleToMExp`'s `epilogue`, at `Body`.

A `.ProducerSchedule` returns its evaluated conclusion outputs; a `.CheckerSchedule` returns the
empty tuple, matching `CheckEnum.runEnumSteps`' `enumPure []`; a `.TheoremSchedule` is the
interpreter's "theorem schedule reached in producer position" error and so `.fail`. -/
def epilogue (E : TransEnv) : ScheduleSort → ValEnv → Body RelIx (List Val)
  | .ProducerSchedule _ outs, ρ =>
    match evalCEs E.funcs ρ outs with
    | .ok vals => .ret vals
    | .error _ => .fail
  | .CheckerSchedule, _ => .ret []
  | .TheoremSchedule .., _ => .fail

/-- Bind a step's output names, or kill the branch on an arity mismatch. -/
def bindK (vars : List Name) (vals : List Val) (ρ : ValEnv)
    (k : ValEnv → Body RelIx (List Val)) : Body RelIx (List Val) :=
  match bindVarsT vars vals ρ with
  | some ρ' => k ρ'
  | none => .fail

/-- **One `ScheduleStep`, as one `Body` node.** The continuation `k` is `CheckEnum`'s
`continueWith`; the shape is `MExp.scheduleStepToMExp`'s, with `MBind` replaced by the graded
operation the docstring table assigns.

Two places where information is lost, both flagged: a misconfiguration (`none` from a `TransEnv`
lookup, an unevaluable argument, an arity mismatch, an unbound scrutinee) becomes `.fail`, which
`Body` cannot distinguish from "this rule does not apply" — see §6.5; and `ProducerSort` and
`Explicit` are dropped, as the runtime interpreter also drops them. -/
def stepBody (E : TransEnv) (step : ScheduleStep) (ρ : ValEnv)
    (k : ValEnv → Body RelIx (List Val)) : Body RelIx (List Val) :=
  match step with
  | .Unconstrained v src _ =>
    match src with
    | .NonRec hyp =>
      match E.leaf hyp with
      | some p => .aux E.grade p (E.leafSpec hyp) (fun val => k (ρ.insert v val))
      | none => .fail
    | .Rec f args | .MutRec f args =>
      match ixOf E f args ρ with
      | some i => .call i (fun outs => k (ρ.insert v (collapse outs)))
      | none => .fail
  | .SuchThat outs src _ =>
    match src with
    | .NonRec hyp =>
      match E.sub hyp (outs.map Prod.fst) ρ with
      | some p =>
        .aux E.grade p (E.subSpec hyp (outs.map Prod.fst) ρ)
          (fun vals => bindK (outs.map Prod.fst) vals ρ k)
      | none => .fail
    | .Rec f args | .MutRec f args =>
      match ixOf E f args ρ with
      | some i => .call i (fun vals => bindK (outs.map Prod.fst) vals ρ k)
      | none => .fail
  | .Check src polarity =>
    .check (polV polarity (E.verdict src ρ)) (polP polarity (E.verdictSpec src ρ)) (k ρ)
  | .Match _ scrutinee pattern =>
    match ρ[scrutinee]? with
    | none => .fail
    | some v =>
      match matchPat pattern v ρ with
      | some ρ' => k ρ'
      | none => .fail

/-- **A step list, as a `Body`.** Literally `MExp.scheduleToMExp`'s `List.foldrM` with `stepBody`
for `scheduleStepToMExp` and `epilogue` for `epilogue`. The continuation type is `ValEnv → Body`
because `Body` has no environment: a schedule's `Unknown`s are resolved at translation time, which
is what turns the IR's deep binding structure into Lean's. -/
def translate (E : TransEnv) (sort : ScheduleSort) (steps : List ScheduleStep) :
    ValEnv → Body RelIx (List Val) :=
  steps.foldr (fun step k ρ => stepBody E step ρ k) (epilogue E sort)

@[simp] theorem translate_nil (E : TransEnv) (sort : ScheduleSort) :
    translate E sort [] = epilogue E sort := rfl

@[simp] theorem translate_cons (E : TransEnv) (sort : ScheduleSort) (step : ScheduleStep)
    (rest : List ScheduleStep) (ρ : ValEnv) :
    translate E sort (step :: rest) ρ = stepBody E step ρ (translate E sort rest) := rfl

/-- One rule application's worth of level, iff the schedule consumes size.

This is the row of the table with the least justification, and it is stated here rather than hidden:
`Schedules.countSizeConsumingCalls` is what `interpEnumRelSchedule` uses to bucket schedules into
`baseScheds`/`recScheds`, and a `recSched` is offered only at `size' + 1`. `Graded.pay` also shifts
by one. The two agree on *which* rules are unavailable at level 0 and on nothing else; see §6.1. -/
def payIf : Bool → Body RelIx (List Val) → Body RelIx (List Val)
  | true, b => .pay b
  | false, b => b

@[simp] theorem holdsR_payIf (R : RelIx → List Val → Prop) (t : Bool)
    (b : Body RelIx (List Val)) (a : List Val) : HoldsR R (payIf t b) a ↔ HoldsR R b a := by
  cases t <;> simp [payIf, HoldsR]

@[simp] theorem bodySound_payIf (t : Bool) (b : Body RelIx (List Val)) :
    BodySound (payIf t b) ↔ BodySound b := by cases t <;> simp [payIf, BodySound]

@[simp] theorem bodyComplete_payIf (t : Bool) (b : Body RelIx (List Val)) :
    BodyComplete (payIf t b) ↔ BodyComplete b := by cases t <;> simp [payIf, BodyComplete]

/-- One constructor's `Schedule`, as one `Body`. -/
def translateRule (E : TransEnv) (sched : Schedule) (ρ : ValEnv) : Body RelIx (List Val) :=
  payIf (0 < countSizeConsumingCalls E.target sched.1) (translate E sched.2 sched.1 ρ)

/-- A relation's schedules plus the input names its conclusion binds
(`Interp.RelSchedule.inputNames`). -/
structure RelSig where
  /-- One `Schedule` per constructor. -/
  schedules : List Schedule
  /-- The names the relation's value-level input positions bind. -/
  inputNames : List Name

/-- **A `RuleSet` from schedules.** The index's `Val` list is bound to the relation's input names,
exactly as `RelSchedule.bindInputs` does, and then each constructor's schedule is translated under
those bindings. An unknown function name contributes no rules. -/
def translateRules (E : TransEnv) (sig : Name → Option RelSig) : RuleSet RelIx (List Val) :=
  fun i =>
    match sig i.1 with
    | none => []
    | some s => s.schedules.map fun sched =>
        match bindVarsT s.inputNames i.2 ∅ with
        | some ρ => translateRule E sched ρ
        | none => .fail

/-! # §4 The faithfulness statement that is provable

The theorem below is `HoldsR R (translate …) a ↔ Sat E R … a`, where `Sat` is a declarative reading
of a step list — existentials for producers, conjunctions for checks, environment threading for
matches — that mentions **no `Grade`, no `pay`, no `Lv`, no `V` and no level**.

Be clear about what this is and is not.

*It is not* a proof that the translation is correct against the deriver. It cannot be: the deriver's
semantics is emitted Lean *source text* (`MExp` → `TSyntax` → elaboration), and the closest thing to
a semantics in the repository is `Specimen/Interp/`, which is `partial def` and hence opaque
(§6.2).

*It is not* deep either. `Sat` and `translate` recurse over the same list in the same order, so the
proof is one `simp` per step kind. Two functions defined by the same recursion agreeing is close to
a tautology.

*It is* the statement that separates the two things the exercise conflates. `Sat` is what the
generic theorem's `hvalid`/`hgen` obligations are really about, and it is grading-blind; `denote` is
where grading lives. Having them provably separate means the grading discussion in §6.1 cannot be
answered by "the relation compensates". And it does catch the class of translation bug that is easy
to make and hard to see: a dropped step, a swapped polarity, a binder inserted under the wrong
name, an output list bound in the wrong order — each of those breaks this `↔`.
-/

/-- The declarative content of one step: what must hold for the branch to reach its continuation.
`R` stands in for the recursive sub-goals, as in `RuleShape.HoldsR`. -/
def SatStep (E : TransEnv) (R : RelIx → List Val → Prop) (step : ScheduleStep) (ρ : ValEnv)
    (C : ValEnv → Prop) : Prop :=
  match step with
  | .Unconstrained v src _ =>
    match src with
    | .NonRec hyp =>
      match E.leaf hyp with
      | some _ => ∃ val, E.leafSpec hyp val ∧ C (ρ.insert v val)
      | none => False
    | .Rec f args | .MutRec f args =>
      match ixOf E f args ρ with
      | some i => ∃ outs, R i outs ∧ C (ρ.insert v (collapse outs))
      | none => False
  | .SuchThat outs src _ =>
    match src with
    | .NonRec hyp =>
      match E.sub hyp (outs.map Prod.fst) ρ with
      | some _ =>
        ∃ vals, E.subSpec hyp (outs.map Prod.fst) ρ vals ∧
          ∃ ρ', bindVarsT (outs.map Prod.fst) vals ρ = some ρ' ∧ C ρ'
      | none => False
    | .Rec f args | .MutRec f args =>
      match ixOf E f args ρ with
      | some i =>
        ∃ vals, R i vals ∧ ∃ ρ', bindVarsT (outs.map Prod.fst) vals ρ = some ρ' ∧ C ρ'
      | none => False
  | .Check src polarity => polP polarity (E.verdictSpec src ρ) ∧ C ρ
  | .Match _ scrutinee pattern =>
    ∃ v, ρ[scrutinee]? = some v ∧ ∃ ρ', matchPat pattern v ρ = some ρ' ∧ C ρ'

/-- The declarative content of a step list plus its epilogue. -/
def Sat (E : TransEnv) (R : RelIx → List Val → Prop) (sort : ScheduleSort) :
    List ScheduleStep → ValEnv → List Val → Prop
  | [], ρ, a => HoldsR R (epilogue E sort ρ) a
  | step :: rest, ρ, a => SatStep E R step ρ (fun ρ' => Sat E R sort rest ρ' a)

private theorem holdsR_bindK {R : RelIx → List Val → Prop} {vars vals ρ k a} :
    HoldsR R (bindK vars vals ρ k) a
      ↔ ∃ ρ', bindVarsT vars vals ρ = some ρ' ∧ HoldsR R (k ρ') a := by
  unfold bindK
  cases h : bindVarsT vars vals ρ with
  | none => simp [HoldsR]
  | some ρ' => simp

/-- One step of the translation agrees with its declarative reading. All four constructors, all
sub-cases; no fragment restriction. -/
theorem holdsR_stepBody (E : TransEnv) (R : RelIx → List Val → Prop) (step : ScheduleStep)
    (ρ : ValEnv) (k : ValEnv → Body RelIx (List Val)) (a : List Val) :
    HoldsR R (stepBody E step ρ k) a ↔ SatStep E R step ρ (fun ρ' => HoldsR R (k ρ') a) := by
  cases step with
  | Unconstrained v src _ =>
    cases src with
    | NonRec hyp =>
      simp only [stepBody, SatStep]
      cases E.leaf hyp <;> simp [HoldsR]
    | Rec f args =>
      simp only [stepBody, SatStep]
      cases ixOf E f args ρ <;> simp [HoldsR]
    | MutRec f args =>
      simp only [stepBody, SatStep]
      cases ixOf E f args ρ <;> simp [HoldsR]
  | SuchThat outs src _ =>
    cases src with
    | NonRec hyp =>
      simp only [stepBody, SatStep]
      cases E.sub hyp (outs.map Prod.fst) ρ <;> simp [HoldsR, holdsR_bindK]
    | Rec f args =>
      simp only [stepBody, SatStep]
      cases ixOf E f args ρ <;> simp [HoldsR, holdsR_bindK]
    | MutRec f args =>
      simp only [stepBody, SatStep]
      cases ixOf E f args ρ <;> simp [HoldsR, holdsR_bindK]
  | Check src polarity => simp [stepBody, SatStep, HoldsR]
  | Match e s p =>
    cases h : ρ[s]? with
    | none => simp [stepBody, SatStep, h, HoldsR]
    | some v =>
      cases h' : matchPat p v ρ with
      | none => simp [stepBody, SatStep, h, h', HoldsR]
      | some ρ' => simp [stepBody, SatStep, h, h']

/-- **Faithfulness, for the grading-blind reading.** The relation a translated schedule defines is
the declarative reading of that schedule. Total in the step kinds. -/
theorem holdsR_translate (E : TransEnv) (R : RelIx → List Val → Prop) (sort : ScheduleSort) :
    ∀ (steps : List ScheduleStep) (ρ : ValEnv) (a : List Val),
      HoldsR R (translate E sort steps ρ) a ↔ Sat E R sort steps ρ a := by
  intro steps
  induction steps with
  | nil => intro ρ a; simp [Sat]
  | cons step rest ih =>
    intro ρ a
    rw [translate_cons, holdsR_stepBody]
    simp only [Sat]
    constructor
    · intro h; exact (satStep_congr (fun ρ' => (ih ρ' a).mp)) h
    · intro h; exact (satStep_congr (fun ρ' => (ih ρ' a).mpr)) h
where
  /-- `SatStep` is monotone in its continuation. -/
  satStep_congr {E R step ρ} {C D : ValEnv → Prop} (h : ∀ ρ', C ρ' → D ρ') :
      SatStep E R step ρ C → SatStep E R step ρ D := by
    cases step with
    | Unconstrained v src _ =>
      cases src with
      | NonRec hyp =>
        simp only [SatStep]
        cases E.leaf hyp
        · exact fun h => h.elim
        · exact fun ⟨x, hx, hc⟩ => ⟨x, hx, h _ hc⟩
      | Rec f args =>
        simp only [SatStep]
        cases ixOf E f args ρ
        · exact fun h => h.elim
        · exact fun ⟨x, hx, hc⟩ => ⟨x, hx, h _ hc⟩
      | MutRec f args =>
        simp only [SatStep]
        cases ixOf E f args ρ
        · exact fun h => h.elim
        · exact fun ⟨x, hx, hc⟩ => ⟨x, hx, h _ hc⟩
    | SuchThat outs src _ =>
      cases src with
      | NonRec hyp =>
        simp only [SatStep]
        cases E.sub hyp (outs.map Prod.fst) ρ
        · exact fun h => h.elim
        · exact fun ⟨x, hx, ρ', hρ, hc⟩ => ⟨x, hx, ρ', hρ, h _ hc⟩
      | Rec f args =>
        simp only [SatStep]
        cases ixOf E f args ρ
        · exact fun h => h.elim
        · exact fun ⟨x, hx, ρ', hρ, hc⟩ => ⟨x, hx, ρ', hρ, h _ hc⟩
      | MutRec f args =>
        simp only [SatStep]
        cases ixOf E f args ρ
        · exact fun h => h.elim
        · exact fun ⟨x, hx, ρ', hρ, hc⟩ => ⟨x, hx, ρ', hρ, h _ hc⟩
    | Check src polarity => exact fun ⟨hp, hc⟩ => ⟨hp, h _ hc⟩
    | Match e s p => exact fun ⟨v, hv, ρ', hρ, hc⟩ => ⟨v, hv, ρ', hρ, h _ hc⟩

/-- …and `pay` is invisible to it, so the same holds of a whole rule. -/
theorem holdsR_translateRule (E : TransEnv) (R : RelIx → List Val → Prop) (sched : Schedule)
    (ρ : ValEnv) (a : List Val) :
    HoldsR R (translateRule E sched ρ) a ↔ Sat E R sched.2 sched.1 ρ a := by
  rw [translateRule, holdsR_payIf, holdsR_translate]

/-! # §5 The non-circular fragment: `.Check`/`.Match` schedules

§4's theorem compares two functions written by the same recursion. This section compares two
functions written *differently*: the graded denotation `denoteL` of a translated body, versus
`refCheck`, a direct three-valued walk in the shape of `CheckEnum.runCheckSteps`, folding
`DecOpt.andOpt` (here `andV`) over the steps. They share no code.

The fragment is `.Check`/`.Match` only, which is exactly the fragment in which no producer, no leaf
budget and no level appear — so it is the fragment where the *un*provable part of §6 is absent, not
a fragment chosen for convenience. Within it the theorem does real work:

* it pins `.Check`'s row of the table including the `V.inconclusive` behaviour. `Graded.guard` keeps
  an `inconclusive` element (with the conclusiveness flag `false`, which `denote` then projects
  away); if it dropped it instead, the equality below fails whenever an inconclusive check is
  followed by a succeeding rest.
* it pins `.Check`'s polarity handling against `negV` = `DecOpt.negOpt`.
* it pins `.Match`'s row: the binder must be threaded into the continuation, and both a missing
  scrutinee and a non-matching pattern must kill the branch.
* it pins the `.CheckerSchedule` epilogue against `runEnumSteps`' `enumPure []`.

It says nothing about `pay`, `call` or `aux`, because the fragment contains none of them.
-/

/-- The one carrier fact §5 needs: a `guard` by a *constant* verdict either drops the whole level
(`.no`) or keeps it unchanged (`.yes`, `.inconclusive`). That `.inconclusive` keeps it is `guard`'s
contract, and it is what makes the theorem below a real check on the `.Check` row. -/
private theorem guard_gmap_const {α : Type} (v : V) (x : Lv α) (n : Nat) :
    (Graded.gmap Prod.fst (GradedBind.guard (fun _ : α => v) x) : Lv α) n
      = (if v = .no then [] else x n) := by
  simp only [Lv.gmap_apply, Lv.guard_apply]
  generalize x n = l
  cases v <;> induction l <;> simp_all

/-- The Kleene arithmetic §5 needs: prefixing a verdict `u` to a walk that answered `w` refutes
exactly when `u` refutes or `w` did. Stated as the list identity the proof consumes. -/
private theorem check_step_eq {γ : Type} (u w : V) (n : Nat) (z : γ) :
    (if u = .no then [] else if n = 0 ∧ w ≠ .no then [z] else [])
      = (if n = 0 ∧ andV u w ≠ .no then [z] else []) := by
  cases u <;> cases w <;> by_cases hn : n = 0 <;> simp [andV, hn]

/-- Whether every step is a `.Check` or a `.Match`. -/
def isCheckOnly : List ScheduleStep → Bool
  | [] => true
  | .Check .. :: rest => isCheckOnly rest
  | .Match .. :: rest => isCheckOnly rest
  | _ :: _ => false

/-- A direct three-valued checker walk over a `.Check`/`.Match` step list, in the shape of
`CheckEnum.runCheckSteps`: `andV` (= `DecOpt.andOpt`) for a check, environment threading for a
match, `.no` for a non-matching pattern (`runCheckSteps` returns `.ok false` there — "refuted, not
unknown"), `.yes` at the end. A producer step is out of fragment and answers `.inconclusive`. -/
def refCheck (E : TransEnv) : List ScheduleStep → ValEnv → V
  | [], _ => .yes
  | .Check src polarity :: rest, ρ => andV (polV polarity (E.verdict src ρ)) (refCheck E rest ρ)
  | .Match _ s p :: rest, ρ =>
    match ρ[s]? with
    | none => .no
    | some v => match matchPat p v ρ with
      | some ρ' => refCheck E rest ρ'
      | none => .no
  | _ :: _, _ => .inconclusive

/-- **The fragment theorem.** For a `.Check`/`.Match` schedule in checker sort, the graded
enumeration of the translated body is the singleton `[[]]` at level 0 exactly when the direct
three-valued walk does not refute, and empty at every other level. Independent of the leaf budget
`L` and of the recursive occurrence `rec`, since the fragment uses neither. -/
theorem denoteL_checkOnly (E : TransEnv) (L : Nat) (rec : RelIx → Lv (List Val)) :
    ∀ (steps : List ScheduleStep), isCheckOnly steps = true → ∀ (ρ : ValEnv) (n : Nat),
      denoteL L rec (translate E .CheckerSchedule steps ρ) n
        = (if n = 0 ∧ refCheck E steps ρ ≠ .no then [([] : List Val)] else []) := by
  intro steps
  induction steps with
  | nil =>
    intro _ ρ n
    simp only [translate_nil, epilogue, denoteL_ret, refCheck]
    cases n <;> simp
  | cons step rest ih =>
    intro hco ρ n
    cases step with
    | Unconstrained => simp [isCheckOnly] at hco
    | SuchThat => simp [isCheckOnly] at hco
    | Check src polarity =>
      have hco' : isCheckOnly rest = true := by simpa [isCheckOnly] using hco
      simp only [translate_cons, stepBody, denoteL_check, refCheck]
      rw [guard_gmap_const, ih hco' ρ n]
      exact check_step_eq _ _ n []
    | Match e s p =>
      have hco' : isCheckOnly rest = true := by simpa [isCheckOnly] using hco
      cases h : ρ[s]? with
      | none => simp [translate_cons, stepBody, refCheck, h]
      | some v =>
        cases h' : matchPat p v ρ with
        | none => simp [translate_cons, stepBody, refCheck, h, h']
        | some ρ' =>
          simp only [translate_cons, stepBody, refCheck, h, h']
          exact ih hco' ρ' n

/-! ## §5.1 A worked instance, so that none of this is vacuous

Two `Schedules.Schedule`s in the shape `Preschedule.lowerPremise` produces for

    inductive Ev : Nat → Prop
      | zero : Ev 0
      | succ : Ev n → Ev (n + 2)

derived as an *enumerator* of the single output. The second constructor's premise is a `.Rec` call at
the same mode with no input arguments, so `countSizeConsumingCalls` counts it and `translateRule`
pays for it.

The `#eval`s below run `enumL (translateRules …)` — the executable graded carrier — through
`translate`. They are the check that `stepBody` composes into something that actually enumerates,
and that the `.pay`/`call` grading puts `2 * k` at level `k`. -/

/-- `Ev.zero`: no premises, conclusion `0`. -/
def evZero : Schedule := ([], .ProducerSchedule .Enumerator [.Lit (.natVal 0)])

/-- `Ev.succ`: one recursive premise binding `n`, conclusion `n.succ.succ`. -/
def evSucc : Schedule :=
  ([.SuchThat [(`n, none)] (.Rec `aux_enum_Ev []) .Enumerator],
   .ProducerSchedule .Enumerator [.Ctor ``Nat.succ [.Ctor ``Nat.succ [.Unknown `n]]])

/-- An interpretation for `Ev`. It needs no leaves and no checkers: every premise is a `.Rec` call,
which `Body.call` discharges against the recursive occurrence. -/
def evEnv : TransEnv where
  funcs := ∅
  target := `Ev
  leaf := fun _ => none
  leafSpec := fun _ _ => False
  sub := fun _ _ _ => none
  subSpec := fun _ _ _ _ => False
  verdict := fun _ _ => .no
  verdictSpec := fun _ _ => False

/-- `Ev`'s two schedules, under the name its `.Rec` steps use. -/
def evSig : Name → Option RelSig := fun n =>
  if n = `aux_enum_Ev then some ⟨[evZero, evSucc], []⟩ else none

private def evAt (l n : Nat) : List (List String) :=
  (enumL (translateRules evEnv evSig) 0 l (`aux_enum_Ev, []) n).map (·.map toString)

-- `Ev.succ` is paid for, so level `k` holds exactly `2 * k` — once the iteration count reaches `k`.
#guard evAt 5 0 == [["0"]]
#guard evAt 5 1 == [["2"]]
#guard evAt 5 2 == [["4"]]
#guard evAt 5 3 == [["6"]]
#guard evAt 5 4 == [["8"]]
-- …and not before: reaching level `k` takes `k + 1` iterations of the step, since each `pay`ing rule
-- consumes one level and one iteration. (Each answer is a one-element *output tuple*, `α = List Val`.)
#guard evAt 3 3 == []
#guard evAt 4 3 == [["6"]]
#guard evAt 0 0 == []

/-! # §6 Where it breaks

Six obstructions. The first is the one that matters.

## 6.1 The grading rows of the table are a proposal, not an erasure

`Body`'s `call` is `bindC`: level `n` of the result draws the sub-goal from level `i` and the
continuation from level `n - i`, for every `i ≤ n` — a convolution. `pay` shifts by one. That is
Feat's/Basalt's *graded* discipline, with exact levels.

Specimen's emitted enumerators do not work that way: the deriver contains no graded combinator —
nothing under `Specimen/` references `bindC`, `GradedBind` or `Graded.pay`. What
`MExp.scheduleToMExp` emits instead is:

* `sizeExpr := if numSizeCalls ≤ 1 then size' else Nat.div size' numSizeCalls` — every recursive
  call gets the *same* reduced budget `size' / k`. This is not a convolution; it is a fixed split,
  and it is also not exhaustive over splits.
* `.MBind` for every premise, which is the underlying monad's ordinary `bind` (`LazyList.bind`,
  `Gen.bind`) at one budget — not `bindC`, and not `bind`-in-the-`GradedBind`-sense either, because
  there is no level index to preserve: `enumSized size` is *cumulative*, not level-exact.
* level 0 / level `n+1` bucketing at the *rule set* level (`interpEnumRelSchedule`: `baseScheds` at
  size 0, `baseScheds ++ recScheds` at `size' + 1`) and nowhere else. `payIf` above reproduces which
  rules are unavailable at level 0 and nothing more, because a graded `pay` makes levels exact
  whereas `enumSized` re-offers every base schedule at every size.

`Specimen/Correctness/ProducerInterp.lean` is the honest existing model of the emitted discipline:
`EnumStep A := List A → List A` with `enumRel step (fuel+1) = step (enumRel step fuel)` — a
cumulative fuel iteration with *no level structure at all*.

So `translate`'s `call ↦ bindC`, `aux ↦ bindC`, `pay ↦ pay` rows describe the enumerator Specimen
*would* have under the Basalt port, and `GradedRuleAdequacy`'s adequacy theorem is a theorem about
that enumerator. It is not an erasure of shipped code. Nothing in this file can close that gap,
because the thing on the other side of it does not exist yet. What this file does do is make the
claim checkable once it does: `translate` is the place a change of discipline would have to be
written down.

One positive by-product. The table's `.NonRec (Eq,..) ↦ deterministic, no budget` row is often read
as "so the grading choice does not matter there". It does: a producer concentrated at level 0 is
`Covers` but not `Unsized`, so even the built-in equality producer must be `.sized`. -/

/-- A deterministic producer: one value, at level 0, at every budget. The built-in `Eq` enumerator's
shape (`interpEnumConstrained`'s `enumPure [(u, v)]`). -/
def detP {β : Type} (v : β) : Nat → Lv β := fun _ => Graded.single v

theorem covers_detP {β : Type} (v : β) : Covers (detP v) (fun b => b = v) := by
  intro b hb; subst hb; exact ⟨0, 0, by simp [detP, Graded.single]⟩

/-- **Even a deterministic premise must be `.sized`.** `bind` reads the producer at the *same* level
as the continuation, so at level 1 and up a level-0-concentrated producer contributes nothing and
the rule produces nothing. So the table's "deterministic, no budget" is about *cost*, not about the
grading operation. -/
theorem not_unsized_detP {β : Type} (v : β) : ¬ Unsized (detP v) (fun b => b = v) := by
  intro h
  obtain ⟨L, hL⟩ := h v rfl
  have := hL L (Nat.le_refl L) 1
  simp [detP, Graded.single] at this

/-! ## 6.2 The runtime interpreter is `opaque`, so nothing can be proved against it

`Specimen/Interp/CheckEnum.lean`'s `runEnumSteps`, `runCheckSteps`, `interpEnumRelSchedule` and
`interpEnumCall`, and `Specimen/Interp/Value.lean`'s `evalConstructorExpr`, `matchPattern`,
`isTypeOrDict` and `Val.toStr`, are all `partial def`. A `partial def` elaborates to an **`opaque`
constant**: `#print` shows `opaque f : …`, there are no equation lemmas, and `unfold`/`simp [f]`
fail. So the sentence "the `Body` denotes the same relation the schedule was derived from" has no
Lean-expressible right-hand side if the right-hand side is meant to be the interpreter.

This is why §1 exists and why its only justification is `#guard`. It is also why §5 compares against
`refCheck` — a total function written to the shape of `runCheckSteps` — rather than against
`runCheckSteps`. The gap is not a proof obligation anyone has skipped; it is a property of
`partial def`.

Closing it would mean making the interpreter's walk total. `runEnumSteps` is structural in `steps`
and its non-structural recursion is all in the fuel-decrementing calls, so `fuel` is a
well-founded measure and the walk is plausibly totalisable; `evalConstructorExpr` and `matchPattern`
are structural already and are `partial` only because of nested `mapM`. That is a real, bounded
piece of work, and it is the prerequisite for any statement stronger than §4 and §5.

## 6.3 `ConstructorExpr` is untyped, so `TransEnv` cannot be derived from the IR

`aux` needs a host type `β`, an executable producer `Nat → Lv β` and a `Prop`. `.NonRec hyp` supplies
a `Name` and a `List ConstructorExpr`. Getting from one to the other is:

* a `Name → Expr` environment lookup (`MetaM`, not a pure function), and
* a re-typechecking denotation for `ConstructorExpr`, because the IR admits ill-typed trees:
  `.Ctor c args` records no arity and no argument types, `.Hole` stands for an argument that only
  elaboration can recover, `.FuncApp f args` may name a function with dependent argument types, and
  `valueArgs` has already *deleted* the type and instance arguments that would be needed to
  reconstruct them. The `isTypeOrDict` heuristic — "an unregistered application of nothing but types
  and dictionaries is a dictionary" — is a load-bearing guess, not a typing rule.

This is the same wall the abandoned deep-reflection attempt hit, and it is why
`Specimen/Correctness/Reflect.lean`'s `RelSpec` keeps `Vars : Type` and `side : Vars → Prop` as host
data, and why `InterpProto.CheckPlan` is indexed by the real `Prop`. `TransEnv` is this file's
version of the same concession. The consequence for faithfulness is precise: §4's theorem is
relative to `TransEnv`, so `leafSpec`/`subSpec`/`verdictSpec` being the propositions the schedule's
names actually denote is an assumption, per name, discharged outside Lean.

## 6.4 `Sat` is an untyped relation, so the last step is per-relation

Even granting a correct `TransEnv`, §4 gives `Sat E R : RelIx → List Val → Prop` over untyped
values. The statement anyone wants is about the host inductive — `typing Γ e τ`, Cedar's
`typeOf`. Bridging requires an embedding `host → Val` and a per-relation adequacy proof
`Sat E R (f, inputs) outputs ↔ HostRel …`, i.e. exactly the "residual per-relation duty" that
`Reflect.lean`'s docstring names and that `EvSlice.lean` discharges by hand for one relation. It is
not generic and this file does not attempt it. `GradedStlcAdequacy`/`GradedCedarRuleAdequacy` are
what that duty looks like when it is paid.

## 6.5 `Body` conflates misconfiguration with branch failure, and drops conclusiveness

`translate` maps every interpreter *error* — no registered enumerator, an unevaluable argument, an
arity mismatch, an unbound match scrutinee, a `.TheoremSchedule` in producer position — to `.fail`,
because `.fail` is all `Body` has. The runtime interpreter distinguishes these from
`Gen.genericFailure` on purpose (see `runEnumSteps`' comment: a definite refutation must be skipped
rather than poison an enclosing checker). A rule set that silently `fail`s on a misconfigured
environment is *sound* and quietly incomplete, which is the failure mode hardest to notice.

Relatedly, `Body.check` drops `guard`'s conclusiveness flag, which `GradedRuleAdequacy`'s own
limitations section already records. That has a sharp consequence for a *negative-polarity* `.Check`,
which Specimen emits whenever `Preschedule.peelNot` finds a negated premise. `BodySound` for
`.check v P k` demands `v ≠ .no → P`, so: -/

/-- `BodySound` forces an `inconclusive` verdict to assert its proposition. -/
theorem bodySound_check_inconclusive {ι α : Type} {P : Prop} {k : Body ι α}
    (h : BodySound (Body.check .inconclusive P k)) : P := h.1 (by decide)

/-- And because `negV .inconclusive = .inconclusive`, an inconclusive verdict under a *negative*
polarity is forced to assert the *negation*. So the same premise cannot be `BodySound` at both
polarities unless its checker is **decisive**: a genuinely three-valued checker under a `¬` — which
is exactly what `Preschedule.peelNot` produces whenever a negated premise is delegated to a
`DecOpt` — has no faithful `Body.check` node. This is not a limitation of `translate`; it is a
limitation of `Body` that writing `translate` exposes. -/
theorem check_inconclusive_not_both_polarities {ι α : Type} {P : Prop} {k : Body ι α}
    (hsP : BodySound (Body.check (polV true .inconclusive) (polP true P) k))
    (hsN : BodySound (Body.check (polV false .inconclusive) (polP false P) k)) : False :=
  (hsN.1 (by decide)) (hsP.1 (by decide))

/-! ## 6.6 What `translate` drops, and what that costs

`ProducerSort` (enumerator vs generator) and `Explicit` are dropped, as the runtime interpreter also
drops them — but `ProducerSort` is not inert in the *emitted* code: a `.Generator` premise becomes
`ArbitrarySizedSuchThat` (or, under `specimen.emitBasalt`, `BacktrackGenFor`) with a weight
function and randomised backtracking, and `Lv`/`SetE` model neither weights nor randomness.
`GradedStlcTest.lean` already records that the counting carrier `Cnt` cannot interpret `bind`, so
`Body` has no leg that could carry a probability. So `translate` is a translation of the
**enumerator** reading of a schedule only; the generator reading needs `Basalt/SPMF`, not `Graded`.

The `.Rec`/`.MutRec` distinction is also dropped, and this one is genuinely harmless at `Body`:
`MExp.scheduleStepToMExp` emits `recCall f fuelPrimeName sizeExpr args` for both, so they differ
only in which function name `f` is — which `RelIx`'s first component records.

# §7 The obligations, discharged structurally

The payoff of §3 is that `adequateL`'s two grading hypotheses become per-*name* obligations on
`TransEnv`, discharged once by induction over steps rather than once per schedule. The two
relational hypotheses (`hvalid`, `hgen`) do **not** become structural — they are §6.4, the
per-relation duty.
-/

/-- A verdict *decides* a proposition: `.yes` exactly when it holds and `.no` exactly when it does
not, hence never `.inconclusive`. Decisiveness is not a convenience — it is forced, by
`check_inconclusive_not_both_polarities`, as soon as a schedule checks a premise at both polarities,
and `Body.check` offers nothing weaker. -/
def Decides (v : V) (P : Prop) : Prop := (P → v = .yes) ∧ (¬ P → v = .no)

/-- Per-name soundness of an interpretation. -/
structure EnvSound (E : TransEnv) : Prop where
  /-- Every leaf only offers values its specification admits. -/
  leaf : ∀ hyp p, E.leaf hyp = some p → Sound p (E.leafSpec hyp)
  /-- Likewise for constrained sub-producers. -/
  sub : ∀ hyp vars ρ p, E.sub hyp vars ρ = some p → Sound p (E.subSpec hyp vars ρ)
  /-- Every check decides its specification; see §6.5 for why nothing weaker will do. -/
  verdict : ∀ src ρ, Decides (E.verdict src ρ) (E.verdictSpec src ρ)

/-- Per-name completeness of an interpretation. -/
structure EnvComplete (E : TransEnv) : Prop where
  /-- Leaves are monotone in the budget. -/
  leafMono : ∀ hyp p, E.leaf hyp = some p → MonoL p
  /-- …and cover their specification, at the grade `E` declares. -/
  leafCov : ∀ hyp p, E.leaf hyp = some p →
    match E.grade with
    | .sized => Covers p (E.leafSpec hyp)
    | .flat => Unsized p (E.leafSpec hyp)
  /-- Likewise for constrained sub-producers. -/
  subMono : ∀ hyp vars ρ p, E.sub hyp vars ρ = some p → MonoL p
  /-- Likewise. -/
  subCov : ∀ hyp vars ρ p, E.sub hyp vars ρ = some p →
    match E.grade with
    | .sized => Covers p (E.subSpec hyp vars ρ)
    | .flat => Unsized p (E.subSpec hyp vars ρ)
  /-- The same decisiveness requirement. -/
  verdict : ∀ src ρ, Decides (E.verdict src ρ) (E.verdictSpec src ρ)

private theorem polV_ne_no_iff {pol : Bool} {P : Prop} {v : V} (hv : Decides v P) :
    polV pol v ≠ .no ↔ polP pol P := by
  by_cases hP : P
  · rw [hv.1 hP]; cases pol <;> simp [polV, polP, negV, hP]
  · rw [hv.2 hP]; cases pol <;> simp [polV, polP, negV, hP]

theorem bodySound_stepBody (E : TransEnv) (h : EnvSound E) (step : ScheduleStep) (ρ : ValEnv)
    (k : ValEnv → Body RelIx (List Val)) (hk : ∀ ρ', BodySound (k ρ')) :
    BodySound (stepBody E step ρ k) := by
  cases step with
  | Unconstrained v src _ =>
    cases src with
    | NonRec hyp =>
      simp only [stepBody]
      cases hp : E.leaf hyp with
      | none => exact trivial
      | some p => exact ⟨h.leaf hyp p hp, fun _ => hk _⟩
    | Rec f args => simp only [stepBody]; cases ixOf E f args ρ
                    · exact trivial
                    · exact fun _ => hk _
    | MutRec f args => simp only [stepBody]; cases ixOf E f args ρ
                       · exact trivial
                       · exact fun _ => hk _
  | SuchThat outs src _ =>
    have hbk : ∀ vals, BodySound (bindK (outs.map Prod.fst) vals ρ k) := by
      intro vals; unfold bindK
      cases bindVarsT (outs.map Prod.fst) vals ρ
      · exact trivial
      · exact hk _
    cases src with
    | NonRec hyp =>
      simp only [stepBody]
      cases hp : E.sub hyp (outs.map Prod.fst) ρ with
      | none => exact trivial
      | some p => exact ⟨h.sub hyp _ ρ p hp, fun _ => hbk _⟩
    | Rec f args => simp only [stepBody]; cases ixOf E f args ρ
                    · exact trivial
                    · exact fun _ => hbk _
    | MutRec f args => simp only [stepBody]; cases ixOf E f args ρ
                       · exact trivial
                       · exact fun _ => hbk _
  | Check src polarity =>
    exact ⟨(polV_ne_no_iff (h.verdict src ρ)).mp, hk ρ⟩
  | Match e s p =>
    simp only [stepBody]
    split
    · exact trivial
    · split <;> first | exact trivial | exact hk _

theorem bodyComplete_stepBody (E : TransEnv) (h : EnvComplete E) (step : ScheduleStep)
    (ρ : ValEnv) (k : ValEnv → Body RelIx (List Val)) (hk : ∀ ρ', BodyComplete (k ρ')) :
    BodyComplete (stepBody E step ρ k) := by
  cases step with
  | Unconstrained v src _ =>
    cases src with
    | NonRec hyp =>
      simp only [stepBody]
      cases hp : E.leaf hyp with
      | none => exact trivial
      | some p =>
        have hm := h.leafMono hyp p hp
        have hc := h.leafCov hyp p hp
        cases hg : E.grade <;> rw [hg] at hc <;> simp only [BodyComplete] <;>
          exact ⟨hm, hc, fun _ => hk _⟩
    | Rec f args => simp only [stepBody]; cases ixOf E f args ρ
                    · exact trivial
                    · exact fun _ => hk _
    | MutRec f args => simp only [stepBody]; cases ixOf E f args ρ
                       · exact trivial
                       · exact fun _ => hk _
  | SuchThat outs src _ =>
    have hbk : ∀ vals, BodyComplete (bindK (outs.map Prod.fst) vals ρ k) := by
      intro vals; unfold bindK
      cases bindVarsT (outs.map Prod.fst) vals ρ
      · exact trivial
      · exact hk _
    cases src with
    | NonRec hyp =>
      simp only [stepBody]
      cases hp : E.sub hyp (outs.map Prod.fst) ρ with
      | none => exact trivial
      | some p =>
        have hm := h.subMono hyp _ ρ p hp
        have hc := h.subCov hyp _ ρ p hp
        cases hg : E.grade <;> rw [hg] at hc <;> simp only [BodyComplete] <;>
          exact ⟨hm, hc, fun _ => hbk _⟩
    | Rec f args => simp only [stepBody]; cases ixOf E f args ρ
                    · exact trivial
                    · exact fun _ => hbk _
    | MutRec f args => simp only [stepBody]; cases ixOf E f args ρ
                       · exact trivial
                       · exact fun _ => hbk _
  | Check src polarity =>
    exact ⟨fun hP => (polV_ne_no_iff (h.verdict src ρ)).mpr hP, hk ρ⟩
  | Match e s p =>
    simp only [stepBody]
    split
    · exact trivial
    · split <;> first | exact trivial | exact hk _

theorem bodySound_translate (E : TransEnv) (h : EnvSound E) (sort : ScheduleSort) :
    ∀ (steps : List ScheduleStep) (ρ : ValEnv), BodySound (translate E sort steps ρ) := by
  intro steps
  induction steps with
  | nil =>
    intro ρ
    simp only [translate_nil]
    cases sort <;> simp only [epilogue]
    · cases evalCEs E.funcs ρ _ <;> exact trivial
    · exact trivial
    · exact trivial
  | cons step rest ih => intro ρ; exact bodySound_stepBody E h step ρ _ ih

theorem bodyComplete_translate (E : TransEnv) (h : EnvComplete E) (sort : ScheduleSort) :
    ∀ (steps : List ScheduleStep) (ρ : ValEnv), BodyComplete (translate E sort steps ρ) := by
  intro steps
  induction steps with
  | nil =>
    intro ρ
    simp only [translate_nil]
    cases sort <;> simp only [epilogue]
    · cases evalCEs E.funcs ρ _ <;> exact trivial
    · exact trivial
    · exact trivial
  | cons step rest ih => intro ρ; exact bodyComplete_stepBody E h step ρ _ ih

theorem bodySound_translateRule (E : TransEnv) (h : EnvSound E) (sched : Schedule) (ρ : ValEnv) :
    BodySound (translateRule E sched ρ) := by
  rw [translateRule, bodySound_payIf]; exact bodySound_translate E h sched.2 sched.1 ρ

theorem bodyComplete_translateRule (E : TransEnv) (h : EnvComplete E) (sched : Schedule)
    (ρ : ValEnv) : BodyComplete (translateRule E sched ρ) := by
  rw [translateRule, bodyComplete_payIf]; exact bodyComplete_translate E h sched.2 sched.1 ρ

theorem bodySound_translateRules (E : TransEnv) (h : EnvSound E) (sig : Name → Option RelSig) :
    ∀ i, ∀ b ∈ translateRules E sig i, BodySound b := by
  intro i b hb
  simp only [translateRules] at hb
  cases hs : sig i.1 with
  | none => rw [hs] at hb; simp at hb
  | some s =>
    rw [hs] at hb
    simp only [List.mem_map] at hb
    obtain ⟨sched, _, rfl⟩ := hb
    cases bindVarsT s.inputNames i.2 ∅ with
    | none => exact trivial
    | some ρ => exact bodySound_translateRule E h sched ρ

theorem bodyComplete_translateRules (E : TransEnv) (h : EnvComplete E)
    (sig : Name → Option RelSig) : ∀ i, ∀ b ∈ translateRules E sig i, BodyComplete b := by
  intro i b hb
  simp only [translateRules] at hb
  cases hs : sig i.1 with
  | none => rw [hs] at hb; simp at hb
  | some s =>
    rw [hs] at hb
    simp only [List.mem_map] at hb
    obtain ⟨sched, _, rfl⟩ := hb
    cases bindVarsT s.inputNames i.2 ∅ with
    | none => exact trivial
    | some ρ => exact bodyComplete_translateRule E h sched ρ

/-- **The statement this file exists to make.** For any set of real `Schedules.Schedule`s and any
interpretation of their names that is sound and complete per name, the graded enumeration of the
translated rule set is adequate for any relation the schedules present and generate.

Read the hypotheses carefully, because they are where everything from §6 lives:

* `hs`, `hc` — discharged structurally from `EnvSound`/`EnvComplete` above, i.e. from obligations on
  the *leaves and checkers*, not on the schedule. This is the part translating buys you.
* `hvalid`, `hgen` — **not** discharged here. `holdsR_translate` rewrites `hvalid` into an
  obligation about `Sat`, which is a relation over untyped `Val`; relating it to a host inductive is
  §6.4, per relation, by hand.
* the conclusion is about `enumL`, which is `bindC`-graded — §6.1. It is a statement about the
  enumerator the Basalt port would emit, not about the one Specimen emits today. -/
theorem schedules_adequateL (E : TransEnv) (hsE : EnvSound E) (hcE : EnvComplete E)
    (sig : Name → Option RelSig) {R : RelIx → List Val → Prop}
    (hvalid : ∀ i, ∀ b ∈ translateRules E sig i, ∀ a, HoldsR R b a → R i a)
    (hgen : ∀ i a, R i a → Derives (translateRules E sig) i a) (i : RelIx) (a : List Val) :
    R i a ↔ ∃ L l n, a ∈ enumL (translateRules E sig) L l i n :=
  adequateL (bodySound_translateRules E hsE sig) (bodyComplete_translateRules E hcE sig)
    hvalid hgen i a

/-! # Axiom audit -/

#print axioms holdsR_translate
#print axioms holdsR_translateRule
#print axioms denoteL_checkOnly
#print axioms not_unsized_detP
#print axioms check_inconclusive_not_both_polarities
#print axioms schedules_adequateL

end ScheduleTranslate

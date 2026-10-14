import Specimen.Interp
import SpecimenTest.Interp.BSTInterpTest
import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.FunctionCallInConclusion

/-!
# Extracting `RelSpec`s from real declarations

`SpecimenTest.Interp.BSTInterpTest` writes its `RelSpec`s by hand, which is how the runtime scheduler
was pinned against the compile-time one. This file checks that `derive_relspec` — which reads the
inductive declaration instead — produces the same thing, and then does the same for relations too
awkward to write out: STLC's `typing`, whose `TApp` and `TAbs` are the reason
`outputInputNotUnderSameConstructor` exists, and `square_of`, whose conclusion contains a function
application and so has to be linearized.

The interesting content is **when an unconstrained generation is necessary**. Three situations force
one, and all three appear here:

| Situation | Where |
| --- | --- |
| Nothing produces it — an output no premise mentions | `BST[1,2]`'s `BstLeaf` needs its upper bound |
| A premise could only produce it from under a function application | `square_of`'s flattened `unk_0 = n * n`, if scheduled backwards |
| A premise argument mixes it with an already-bound variable | `typing`'s `TAbs` at mode `[1,2]`: `τ1 :: Γ` holds an unbound `τ1` beside a bound `Γ` |

Each is reported by `reschedule` with the variables that would unblock it, `repair` inserts the
generation immediately before the premise that needs it, and `requiredInstVars` answers the question
directly.
-/

open Plausible Schedules Specimen Specimen.Interp

namespace SpecimenTest.InterpExtract

/-! ## The extracted specs agree with the hand-written ones

    `BSTInterpTest` pins its hand-written specs against the schedules `derive_mutual` chooses. Pinning
    the *extracted* specs against those hand-written ones therefore pins extraction against the
    pipeline too, transitively — which is the point, since a differently-spelled premise would
    schedule differently. -/

derive_relspec Between
derive_relspec BST

/-- The extracted spec, renamed to the hand-written one's conventions. `argNames` and `recFnName` are
    internal to a schedule and freely chosen, so they are the one thing that legitimately differs. -/
def align (hand extracted : RelSpec) : RelSpec :=
  { extracted with argNames := hand.argNames, recFnName := hand.recFnName }

-- Extraction reproduces the hand-written specs exactly, modulo the freely-chosen names.
/-- info: (true, true) -/
#guard_msgs in
#eval
  (align InterpBST.betweenSpec betweenRelSpec == InterpBST.betweenSpec,
   align InterpBST.bstSpec bstRelSpec == InterpBST.bstSpec)

-- And therefore derives the same schedules — the transitive pin to `derive_mutual`.
/-- info: (true, true) -/
#guard_msgs in
#eval
  let same := fun (hand ext : RelSpec) (key : SpecKey) =>
    match hand.deriveMode key, (align hand ext).deriveMode key with
    | .ok a, .ok b => a.allSchedules == b.allSchedules
    | _, _ => false
  (same InterpBST.betweenSpec betweenRelSpec InterpBST.betweenKey,
   same InterpBST.bstSpec bstRelSpec InterpBST.bstKey)

-- The generated names are the conventional ones, so `derive_relspec R` is predictable.
/-- info: (`aux_between, `aux_bst, [`a_1, `b_1, `c_1]) -/
#guard_msgs in
#eval (betweenRelSpec.recFnName, bstRelSpec.recFnName, bstRelSpec.argNames)

/-! ## A conclusion containing a function application is linearized

    `square_of n (n * n)` cannot be matched against an input: there is no pattern for `n * n`. The
    pipeline's `linearizeAndFlatten` lifts the application into a fresh variable plus an equality
    premise, and `CtorSpec.linearize` does the same to the extracted spec. Without it the conclusion
    would be unschedulable. -/

derive_relspec square_of

-- After linearization the conclusion is two bare variables, the multiplication has become an
-- equality premise, and the fresh variable is typed from the argument position it replaced — so it
-- can be generated if a plan ever needs to.
/-- info: ([`n, `unk_0], [Nat, Nat], ["n", "unk_0"], 1) -/
#guard_msgs in
#eval match square_ofRelSpec.ctors.head? with
  | none => ([], [], [], 0)
  | some c =>
    (c.vars.map VarSpec.name, c.vars.map VarSpec.ty,
     c.conclusionArgs.map ppConstructorExpr, c.hypotheses.length)

-- The premise is an equality on the fresh variable, which the built-in equality producer can solve
-- for — so `square_of[1]` (given `n`, produce `n * n`) schedules with no leaf beyond `*` itself.
/-- info: (true, "unk_0 = (hMul Nat Nat Nat (instHMul Nat instMulNat) n n)") -/
#guard_msgs in
#eval match square_ofRelSpec.ctors.head?.bind (fun c => c.hypotheses.head?) with
  | none => (false, "")
  | some h => (h.1 == ``Eq, ppHypothesisExpr h)

/-- `square_of` generating its second argument. -/
def squareKey : SpecKey :=
  { inductiveName := ``square_of, outputIndices := [1], deriveSort := .Generator }

-- `n * n` reifies with a *nested* `instHMul Nat (instMulNat)` dictionary — an applied `FuncApp` that
-- `valueArgs` cannot drop. It needs no registration: an unregistered application of nothing but types
-- and dictionaries is itself a dictionary, and evaluates to an opaque atom. Only `HMul.hMul` has to
-- be registered, and it reads its two operands off the end of the argument list.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  let leaves := (({} : InterpEnv).withArbitrary ``Nat Nat).withFunc2 ``HMul.hMul
    (fun a b : Nat => a * b)
  match leaves.deriveClosure [square_ofRelSpec] [squareKey] with
  | .error _ => return (false, false)
  | .ok env => do
    let s ← env.sample squareKey 4 [toVal 7] 50 50
    let squares := s.samples.filterMap (fun vals =>
      match vals with | [v] => v.asNat? | _ => none)
    return (env.check.isEmpty, squares.length == 50 && squares.all (· == 49))

/-! ## STLC: the relation the "output under the same constructor" rule exists for -/

derive_relspec typing
derive_relspec lookup

/-- Both STLC relations, for `deriveClosure` to draw on. -/
def stlcSpecs : List RelSpec := [typingRelSpec, lookupRelSpec]

/-- `typing` generating a well-typed term for a given context and type. -/
def typingKey : SpecKey :=
  { inductiveName := ``typing, outputIndices := [1], deriveSort := .Generator }

/-- `typing.TApp`, whose second premise `typing Γ e₁ (.Fun τ₁ τ₂)` is the motivating example in
    `outputInputNotUnderSameConstructor`'s docstring. -/
def tapp : CtorSpec :=
  (typingRelSpec.ctors.find? (fun c => c.ctorName == ``typing.TApp)).getD default

/-- `typing.TAbs`, whose premise reads `τ₁ :: Γ`. -/
def tabs : CtorSpec :=
  (typingRelSpec.ctors.find? (fun c => c.ctorName == ``typing.TAbs)).getD default

instance : ToVal type where
  toVal := fun t =>
    let rec go : type → Val
      | .Nat => .ctor ``type.Nat []
      | .Fun a b => .ctor ``type.Fun [go a, go b]
    go t

instance : OfVal type where
  ofVal := fun v =>
    let rec go : Val → Except String type
      | .ctor ``type.Nat [] => .ok .Nat
      | .ctor ``type.Fun [a, b] => do return .Fun (← go a) (← go b)
      | w => .error s!"expected a `type`, got `{w}`"
    go v

instance : ToVal term where
  toVal := fun t =>
    let rec go : term → Val
      | .Const n => .ctor ``term.Const [.lit (.natVal n)]
      | .Var n => .ctor ``term.Var [.lit (.natVal n)]
      | .Add a b => .ctor ``term.Add [go a, go b]
      | .App a b => .ctor ``term.App [go a, go b]
      | .Abs τ e => .ctor ``term.Abs [toVal τ, go e]
    go t

/-- Reads a `Val` back as a `term`. -/
partial def toTerm : Val → Except String term
  | .ctor ``term.Const [n] => (term.Const ·) <$> ofVal n
  | .ctor ``term.Var [n] => (term.Var ·) <$> ofVal n
  | .ctor ``term.Add [a, b] => do return .Add (← toTerm a) (← toTerm b)
  | .ctor ``term.App [a, b] => do return .App (← toTerm a) (← toTerm b)
  | .ctor ``term.Abs [τ, e] => do return .Abs (← ofVal τ) (← toTerm e)
  | v => .error s!"expected a `term`, got `{v}`"

/-- An independent typechecker, so a generated term is judged by something other than the
    interpreter that produced it. -/
def typeOf (Γ : List type) : term → Option type
  | .Const _ => some .Nat
  | .Var x => Γ[x]?
  | .Add a b => do
    let ta ← typeOf Γ a
    let tb ← typeOf Γ b
    if ta == .Nat && tb == .Nat then some .Nat else none
  | .Abs τ e => (type.Fun τ ·) <$> typeOf (τ :: Γ) e
  | .App f a => do
    match ← typeOf Γ f with
    | .Fun t₁ t₂ => do
      let ta ← typeOf Γ a
      if ta == t₁ then some t₂ else none
    | .Nat => none

/-- The leaves STLC needs: `Nat` for `TConst`'s literal, and `type` for the argument type that
    `TAbs` has to invent at mode `[1,2]`. -/
def stlcLeaves : InterpEnv :=
  (({} : InterpEnv).withArbitrary ``Nat Nat).withArbitrary ``type type

/-- Every mode `typing[1]` needs, derived at runtime. -/
def stlcEnv : Except String InterpEnv :=
  stlcLeaves.deriveClosure stlcSpecs [typingKey]

-- Closing over `typing[1]` pulls in `typing[1,2]` (because `TApp` produces a term *and* its type),
-- `lookup[1]` and `lookup[1,2]`, each under its own `recFnName`, and every step resolves.
/-- info: (4, true, "[interp] ok: 4 relation(s) registered, every step resolves") -/
#guard_msgs in
#eval match stlcEnv with
  | .error e => (0, false, e)
  | .ok env =>
    let fns := env.relations.toList.map (fun (p : SpecKey × RelSchedule) => p.2.recFnName)
    let distinct := fns.foldl (fun (acc : List Lean.Name) f =>
      if acc.contains f then acc else acc ++ [f]) []
    (env.relations.size, fns.length == distinct.length, env.checkReport)

-- The chosen `TApp` schedule is the one that produces the argument's type alongside the argument,
-- rather than guessing a type and hoping a term of it exists.
/-- info: "do\n    [e2, τ1] ← typing a_1 e2 τ1\n    [e1] ← aux_typing a_1 Fun τ1 c_1\n    return App e1 e2" -/
#guard_msgs in
#eval match typingRelSpec.deriveModeIn stlcLeaves typingKey (derivable := [``typing, ``lookup]) with
  | .error e => e
  | .ok rel => (rel.ctorSchedule? ``typing.TApp).elim "missing" ppSchedule

-- Every generated term typechecks, at the type asked for.
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  match stlcEnv with
  | .error _ => return false
  | .ok env => do
    let goal := type.Fun .Nat .Nat
    let s ← env.sample typingKey 5 [toVal ([] : List type), toVal goal] 200 200
    let terms ← s.samples.mapM fun vals =>
      match vals with
      | [v] => match toTerm v with
               | .ok t => pure (some t)
               | .error _ => pure none
      | _ => pure none
    return s.successes == 200 && terms.length == 200
      && terms.all (fun t => (t.bind (typeOf [])) == some goal)

/-! ## When an unconstrained generation is necessary

    Each case names the variables that would unblock it, so the repair is derived rather than
    guessed. `requiredInstVars` is the direct question: what does this ordering have to invent? -/

/-- A schedule reduced to the shape of its steps, so an assertion does not depend on how a long line
    happens to be wrapped. -/
def stepKinds (sched : Schedule) : List String :=
  sched.1.map fun
    | .Match .. => "match"
    | .Unconstrained .. => "arbitrary"
    | .SuchThat .. => "produce"
    | .Check .. => "check"

/-- `typing` producing both a term and its type. -/
def typingKey₂ : SpecKey :=
  { inductiveName := ``typing, outputIndices := [1, 2], deriveSort := .Generator }

-- `TAbs` at mode `[1,2]` — produce both the term and its type — must invent the argument type: the
-- premise reads `τ1 :: Γ`, which mixes the unbound `τ1` with the bound context. The rejection names
-- `τ1`, which is what makes the repair mechanical.
/-- info: (some [`τ1], true, true) -/
#guard_msgs in
#eval
  (requiredInstVars typingRelSpec typingKey₂ tabs [.use 0],
   match reschedule typingRelSpec typingKey₂ tabs [.use 0] with
   | .error (.outputInputUnderSameCtor _ arg vars) => arg == "τ1 :: a_1" && vars == [`τ1]
   | _ => false,
   -- And the generation lands immediately before the premise that needs it.
   match repair typingRelSpec typingKey₂ tabs [.use 0] with
   | .ok (plan, sched) =>
     plan == ([.inst `τ1, .use 0] : Plan) && stepKinds sched == ["arbitrary", "produce"]
   | .error _ => false)

-- At mode `[1]` nothing has to be invented for `TAbs`: the conclusion's `Fun τ1 τ2` is an input, so
-- matching it binds `τ1` before the premise runs.
/-- info: some [] -/
#guard_msgs in
#eval requiredInstVars typingRelSpec typingKey tabs [.use 0]

-- `TApp`'s two orderings need genuinely different things. Taking the premises as declared, `typing`
-- is asked for a term *and* its type — mode `[1,2]`, and nothing has to be invented. Taking them
-- backwards, `typing Γ e1 (.Fun τ1 τ2)` runs with `τ2` bound from the conclusion and `τ1` not, which
-- is the exact situation `outputInputNotUnderSameConstructor` describes: `τ1` must be invented.
/-- info: [(some [], ["typing[1,2] as Generator"]), (some [`τ1], [])] -/
#guard_msgs in
#eval
  [[PlanStep.use 0, .use 1], [.use 1, .use 0]].map (fun plan =>
    (requiredInstVars typingRelSpec typingKey tapp plan,
     match reschedule typingRelSpec typingKey tapp plan with
     | .ok (steps, _) => (steps.filterMap stepDepKey?).map renderSpecKey
     | .error _ => []))

-- The third case: an output nothing produces. `BST[1,2]`'s `BstLeaf` has no premises at all, so its
-- upper bound can only be invented — and the generation goes at the end, where the compile-time
-- scheduler also puts its trailing `InstVars`.
/-- info: (some [`hi], "do\n    hi ← Nat\n    return (hi, Leaf)") -/
#guard_msgs in
#eval
  let k : SpecKey := { inductiveName := ``BST, outputIndices := [1, 2], deriveSort := .Generator }
  let leaf := (InterpBST.bstSpec.ctors[0]?).getD default
  (requiredInstVars InterpBST.bstSpec k leaf [],
   match repair InterpBST.bstSpec k leaf [] with
   | .error e => e.message
   | .ok (_, sched) => ppSchedule sched)

-- Across `typing`'s constructors at mode `[1]`, exactly one needs anything invented: `TConst`, whose
-- literal `n` appears only in the conclusion and so has no premise to come from. Every other
-- constructor's variables are produced by a premise or bound by matching the conclusion.
/-- info: [some [`n], some [], some [], some [], some []] -/
#guard_msgs in
#eval typingRelSpec.ctors.map (fun c =>
  requiredInstVars typingRelSpec typingKey c
    ((List.range c.hypotheses.length).map PlanStep.use))

/-! ## A hygienic binder survives render-and-reparse

An anonymous instance binder such as `[DecidableEq α]` is named `inst._@.…._hyg.N` — a name with a
numeric component and macro scopes, which no backtick literal can spell. `derive_relspec` renders the spec
as source and parses it back, so before `srcName` it failed on any such relation. Cedar's
`MapNotContainsKey` is one, and was silently missing from the closure. -/

/-- An instance binder with no user name, the shape of Cedar's `MapNotContainsKey`. -/
inductive NotMem {α : Type} [DecidableEq α] : α → List α → Prop
  | nil (a : α) : NotMem a []
  | cons (a b : α) (l : List α) : a ≠ b → NotMem a l → NotMem a (b :: l)

derive_relspec NotMem

-- The binder really is hygienic, so this exercises the `Name.str`/`Name.num` path.
/-- info: true -/
#guard_msgs in
#eval ((notMemRelSpec.ctors[0]?).bind (·.vars[1]?)).any (·.name.hasMacroScopes)

-- And the round trip is exact: the spec that was parsed back is the spec that was extracted.
/-- info: true -/
#guard_msgs in
#eval show Lean.Elab.Term.TermElabM Bool from do
  let s ← extractRelSpec ``NotMem
  return reprStr s == reprStr notMemRelSpec

/-! ## An instance-implicit parameter is dropped by position, at the call

    Cedar's `MapNotContainsKey {α β} [DecidableEq α]` is what this pins. Its call sites are
    monomorphic, so the dictionary elaborates to a constant and the premise reifies as
    `MapNotContainsKey Attr (Qualified CedarType) instDecidableEqString a m`. The two types are
    `.TyCtor`s and drop by kind; the dictionary is a `.FuncApp` and does not. It was evaluated to an
    opaque atom and passed as the callee's first input, while the callee — whose `typeArgIndices`
    include the class position — binds nothing there. Every rule of the callee then failed `bindInputs`
    and `backtrack` filed that as a discard, so that call from `HasType.hasAttrRecordNotFound` could never
    succeed in the interpreter although the compiled generator runs it — while `InterpEnv.check` reported
    every step resolved. (Read from the call path and shown here on `Keyed`; Cedar's samples from the
    `HasType[0,4]` root almost never reach that call, so they could not show it.)

    `Keyed` has the same shape and nothing else. It holds of everything, because the dictionary is the
    point; its recursive rule makes the self-call carry the dictionary *binder*, which lowering holes
    out, so that path is covered too. The binder is named only for readability: an anonymous one gets
    a macro-scoped name (`inst._@…`), which `derive_relspec` also round-trips (`srcName`; see the
    `NotMem` test below). -/

/-- `Keyed k l` holds for every key and list. Instance-implicit, like `MapNotContainsKey`. -/
inductive Keyed {α : Type} [inst : DecidableEq α] : α → List α → Prop where
  | nil : ∀ k, Keyed k []
  | cons : ∀ k j rest, Keyed k rest → Keyed k (j :: rest)

/-- A monomorphic caller whose one rule goes through `Keyed` at `Nat`, so the call site supplies the
    concrete dictionary `instDecidableEqNat`. -/
inductive KeyedNat : Nat → List Nat → Prop where
  | mk : ∀ k l, Keyed k l → KeyedNat k l

derive_relspec Keyed
derive_relspec KeyedNat

-- The class position is recorded, and the caller's premise really does carry the dictionary as a
-- `.FuncApp` — the one argument kind `valueArgs` keeps.
/-- info: ([0, 1], true) -/
#guard_msgs in
#eval (keyedRelSpec.typeArgIndices,
  match keyedNatRelSpec.ctors.head?.bind (fun c => c.hypotheses.head?) with
  | some (_, args) => args.any (fun a => match a with | .FuncApp .. => true | _ => false)
  | none => false)

/-- The one leaf both directions need: `Nat`, for the key or element a rule has to invent. -/
def keyedLeaves : InterpEnv := ({} : InterpEnv).withArbitrary ``Nat Nat

/-- Both relations, for `deriveClosure` to draw on. -/
def keyedSpecs : List RelSpec := [keyedRelSpec, keyedNatRelSpec]

/-- Given the key, produce the list: a call to `Keyed[3]`, whose one input is the key. -/
def keyedListKey : SpecKey :=
  { inductiveName := ``KeyedNat, outputIndices := [1], deriveSort := .Generator }

/-- Given the list, produce a key: a call to `Keyed[2]`, whose rules open by matching the list. With
    `dispatchInputs` on, the guard matches that pattern against the inputs the call passes, so a stray
    dictionary in front of the list gets matched as the list. -/
def keyedKeyKey : SpecKey :=
  { inductiveName := ``KeyedNat, outputIndices := [0], deriveSort := .Generator }

-- Every attempt succeeds, in both directions and with the dispatch guard on. All three counts were 0:
-- `Keyed[3]` was handed `[instDecidableEqNat, 3]` for its one input, and `Keyed[2]`
-- `[instDecidableEqNat, [1, 2]]`, whose dictionary the guard then matched against `[]` and `_ :: _`.
/-- info: (true, 50, 50, 50) -/
#guard_msgs in
#eval show IO (Bool × Nat × Nat × Nat) from do
  match keyedLeaves.deriveClosure keyedSpecs [keyedListKey, keyedKeyKey] with
  | .error _ => return (false, 0, 0, 0)
  | .ok env => do
    let lists ← env.sample keyedListKey 4 [toVal (3 : Nat)] 50 0 (seed := some 7)
    let keys ← env.sample keyedKeyKey 4 [toVal ([1, 2] : List Nat)] 50 0 (seed := some 7)
    let guarded ← ({ env with dispatchInputs := true } : InterpEnv).sample keyedKeyKey 4
      [toVal ([1, 2] : List Nat)] 50 0 (seed := some 7)
    return (env.check.isEmpty, lists.successes, keys.successes, guarded.successes)

/-- `KeyedNat` decided outright. Its rule is then `check Keyed Nat instDecidableEqNat a_1 b_1`, and a
    checker closure derives an interpreted `Keyed[]@(0:Nat)` for it, which `checkSourceIn` prefers to
    any leaf — so the check's arguments reach that checker's `bindInputs` as the call site built them. -/
def keyedCheckKey : SpecKey :=
  { inductiveName := ``KeyedNat, outputIndices := [], deriveSort := .Checker }

-- `check` is clean and the verdict is definite. Before, the check handed three values to a checker
-- that binds two, every rule of `Keyed[]` errored, and `checkerBacktrack` answered "cannot decide";
-- `check` meanwhile reported the checker missing, having looked for it without its instantiation.
/-- info: (true, some true) -/
#guard_msgs in
#eval show Bool × Option Bool from
  match ({} : InterpEnv).deriveClosure keyedSpecs [keyedCheckKey] with
  | .error _ => (false, none)
  | .ok env =>
    (env.check.isEmpty,
     match env.decide keyedCheckKey 5 [toVal (3 : Nat), toVal ([1, 2] : List Nat)] with
     | .ok b => some b
     | .error _ => none)

-- `check` compares a producer call's arity with what its callee binds, not only whether the callee
-- exists. Re-registering `Keyed[3]` as though it had no type positions makes it bind three inputs where
-- the call passes one. Before, `check` found some `Keyed[3]` and said nothing about `KeyedNat`.
/-- info: true -/
#guard_msgs in
#eval
  match keyedLeaves.deriveClosure keyedSpecs [keyedListKey] with
  | .error _ => false
  | .ok env =>
    match env.relations.toList.find? (fun ((k, _) : SpecKey × RelSchedule) =>
        k.inductiveName == ``Keyed && k.outputIndices == [3]) with
    | none => false
    | some (_, rel) =>
      (env.addRelation { rel with typeArgIndices := [] }).check.any (fun i =>
        match i with
        | .arityMismatch s .. => s.inductiveName == ``KeyedNat
        | _ => false)

end SpecimenTest.InterpExtract

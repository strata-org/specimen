import Specimen.Interp.Diagnose

/-!
# The inputs each constructor is meant for

Some constructors fail because of what they are *given*, not how they are scheduled: STLC's `TVar`
asked for a type no variable in the context has, Cedar's `varContext` asked for a record type that is not
the request's context type. No reordering inside the constructor fixes that, and `diagnose` says only
"the inputs decide it". This module says *which part* of the inputs decides it, statically, from the rule
itself:

* the **pattern** — the conclusion's arguments at the mode's input positions, which dispatch checks;
* the **equalities** — variables that occur more than once across those positions: `varContext`'s
  conclusion mentions `ctx` both inside the environment and as the requested type `.record ctx`, so it
  applies only when the two agree;
* the **gates** — premises, other than recursive calls of the relation itself, whose steps read only what
  the inputs determine, so whether they can succeed is settled by the inputs alone (`TVar`'s
  `lookup Γ x τ` needs a variable of type `τ` in `Γ`).

`ShapeTrie` partitions a mode's input space by the patterns' heads, as `PatternCoverage` does for the
compile-time scorer, and names the shapes no constructor covers: requests a caller should never make.
`classifyEntry` replays a recorded entry against a shape, so a failure can be named — "the requested type
is not the context type" — rather than read off by hand.
-/

open Lean Schedules

namespace Specimen.Interp

/-- What a constructor needs of its inputs. -/
structure InputShape where
  ctorName : Name
  /-- `(input position, conclusion argument)`. -/
  patterns : List (Nat × ConstructorExpr)
  /-- Variables occurring more than once across the input patterns. -/
  repeated : List Name
  /-- Premises whose steps read only input-determined values. -/
  gates : List Nat
  deriving Repr, Inhabited

/-- Matches a conclusion argument against a value, extending `σ`. A repeated variable must match the
    same value; a function application constrains nothing that can be checked without evaluating it. -/
partial def matchCE (σ : List (Name × Val)) : ConstructorExpr → Val → Option (List (Name × Val))
  | .Unknown v, x =>
    match σ.find? (·.1 == v) with
    | some (_, y) => if y == x then some σ else none
    | none => some ((v, x) :: σ)
  | .Ctor n args, .ctor m vs =>
    if n != m || args.length != vs.length then none
    else (args.zip vs).foldlM (fun σ' (a, x) => matchCE σ' a x) σ
  | .Ctor _ _, _ => none
  | _, _ => some σ

/-- Variables a conclusion argument mentions, with repetitions. -/
partial def ceVars : ConstructorExpr → List Name
  | .Unknown v => [v]
  | .Ctor _ args => args.flatMap ceVars
  | .FuncApp _ args => args.flatMap ceVars
  | _ => []

/-- The input positions of a mode: the relation's argument positions that are not outputs, in order. -/
def inputPositions (rel : RelSpec) (key : SpecKey) : List Nat :=
  (List.range rel.argNames.length).filter (fun i => !key.outputIndices.contains i)

/-- The shape of constructor `c` at mode `key`. Gates are read off the installed schedule, if given. -/
def InputShape.of (rel : RelSpec) (key : SpecKey) (c : CtorSpec) (rs? : Option RelSchedule := none) :
    InputShape :=
  let patterns := (inputPositions rel key).filterMap (fun i => (c.conclusionArgs[i]?).map (i, ·))
  let vs := patterns.flatMap (fun (_, a) => ceVars a)
  let repeated := (vs.filter (fun v => (vs.filter (· == v)).length > 1)).eraseDups
  let gates := match rs? with
    | none => []
    | some rs =>
      match rs.ctorSchedule? c.ctorName, rs.provenanceOf? c.ctorName with
      | some (steps, _), some prov =>
        (steps.zipIdx.filterMap (fun (st, i) =>
          let isPrologue := ((prov.origins[i]?).bind id).isNone
          match st, (prov.origins[i]?).bind id with
          | .Match .., _ => none
          -- A recursive call reading only inputs is the recursion, not a gate.
          | _, some (.use p) =>
            if !isPrologue && countSizeConsumingCalls rel.inductiveName [st] == 0
                && readsOnlyInputs rs.inputNames steps i then some p else none
          | _, _ => none)).eraseDups
      | _, _ => []
  { ctorName := c.ctorName, patterns, repeated, gates }

def InputShape.render (s : InputShape) : String :=
  let pats := s.patterns.map (fun (i, a) => s!"#{i} = {ppConstructorExpr a}")
  s!"{s.ctorName.componentsRev.head!}: " ++ ", ".intercalate pats ++
    (if s.repeated.isEmpty then "" else s!" · equal: {s.repeated}") ++
    (if s.gates.isEmpty then "" else s!" · gated by premise(s) {s.gates}")

/-- Why a recorded entry does or does not fit a shape. -/
inductive EntryFit where
  | fits
  /-- The input at this position does not have the pattern's shape. -/
  | patternMismatch (position : Nat)
  /-- A repeated variable would have to be two different values. -/
  | equalityViolated (var : Name)
  deriving Repr, BEq, Inhabited

def EntryFit.render : EntryFit → String
  | .fits => "fits"
  | .patternMismatch i => s!"input #{i} does not have the pattern's shape"
  | .equalityViolated v => s!"`{v}` would have to be two different values"

/-- Replays entry `inputs` (in input-position order) against a shape. -/
def classifyEntry (s : InputShape) (inputs : List Val) : EntryFit := Id.run do
  let mut σ : List (Name × Val) := []
  for ((i, pat), x) in s.patterns.zip inputs do
    -- Shape first, ignoring repetition: a mismatch is a shape mismatch even if it also repeats a variable.
    if (matchCE [] pat x).isNone then return .patternMismatch i
    match matchCE σ pat x with
    | some σ' => σ := σ'
    | none =>
      let v := ((ceVars pat).find? (fun v => σ.any (·.1 == v))).getD `_
      return .equalityViolated v
  return .fits

/-- A head signature: a pattern cut off at `depth`, variables as `_`. -/
partial def headSig (depth : Nat) : ConstructorExpr → String
  | .Ctor n args =>
    let short := n.componentsRev.head?.map toString |>.getD (toString n)
    if depth ≤ 1 || args.isEmpty then short
    else s!"{short}({", ".intercalate (args.map (headSig (depth - 1)))})"
  | .FuncApp f _ => s!"{f.componentsRev.head?.map toString |>.getD (toString f)}(…)"
  | _ => "_"

/-- Whether a pattern can match a value of head signature `sig` — compared at the signature's own depth. -/
partial def compatibleSig (depth : Nat) (pat : ConstructorExpr) (sig : String) : Bool :=
  match pat with
  | .Unknown _ | .FuncApp _ _ => true
  | _ => headSig depth pat == sig || sig == "_"

/-- The partition of a mode's input space by the heads of its constructors' input patterns: each leaf
    assigns a head signature to every input position, and lists the constructors that can apply. -/
structure ShapeTrie where
  positions : List Nat
  leaves : List (List String × List Name)
  deriving Repr, Inhabited

/-- Builds the trie at `depth`. Positions every constructor leaves open are not split. -/
def ShapeTrie.of (rel : RelSpec) (key : SpecKey) (depth : Nat := 2) : ShapeTrie := Id.run do
  let positions := inputPositions rel key
  let sigsAt := fun (i : Nat) =>
    (rel.ctors.filterMap (fun c => (c.conclusionArgs[i]?).map (headSig depth))).filter (· != "_") |>.eraseDups
  let split := positions.filter (fun i => !(sigsAt i).isEmpty)
  let mut leaves : List (List String × List Name) := [([], [])]
  for i in split do
    leaves := leaves.flatMap (fun (sigs, _) => (sigsAt i).map (fun s => (sigs ++ [s], [])))
  let covering := fun (sigs : List String) => rel.ctors.filter (fun c =>
    (split.zip sigs).all (fun (i, s) => match c.conclusionArgs[i]? with
      | some pat => compatibleSig depth pat s
      | none => true)) |>.map (·.ctorName)
  return { positions := split, leaves := leaves.map (fun (sigs, _) => (sigs, covering sigs)) }

def ShapeTrie.render (t : ShapeTrie) (onlyUncovered : Bool := false) : String :=
  let rows := t.leaves.filter (fun (_, cs) => !onlyUncovered || cs.isEmpty)
  "\n".intercalate (rows.map (fun (sigs, cs) =>
    ", ".intercalate ((t.positions.zip sigs).map (fun (i, s) => s!"#{i} = {s}")) ++
      s!"  ↦  {if cs.isEmpty then "no constructor" else ", ".intercalate (cs.map (fun c => c.componentsRev.head!.toString))}"))

end Specimen.Interp

namespace Specimen.Interp

/-- A constructor's recorded entries, split by whether they are inputs it is meant for. -/
structure EntrySplit where
  intended : List CtorEntry := []
  /-- Entries that fail the pattern or an equality, with the reason. -/
  wrongShape : List (CtorEntry × EntryFit) := []
  /-- Entries that never succeed and only ever fail at a gate. -/
  gated : List CtorEntry := []
  deriving Inhabited

def EntrySplit.render (s : EntrySplit) : String :=
  let reasons := (s.wrongShape.map (·.2.render)).eraseDups.map (fun r =>
    s!"{(s.wrongShape.filter (·.2.render == r)).length}× {r}")
  s!"{s.intended.length} intended · {s.wrongShape.length} wrong shape" ++
    (if reasons.isEmpty then "" else s!" ({", ".intercalate reasons})") ++ s!" · {s.gated.length} rejected by a gate"

/-- Splits recorded entries by `shape`. Gates are checked by running: an entry is gate-rejected when
    `tries` runs of the constructor on it all fail, each at a step a gate premise emitted. -/
def splitEntries (env : InterpEnv) (key : SpecKey) (ctor : Name) (shape : InputShape)
    (entries : List CtorEntry) (tries : Nat := 3) (seed : Nat := 1) : IO EntrySplit := do
  let gateSteps : List Nat := match (env.relations[key]?).bind (·.provenanceOf? ctor) with
    | some prov => (prov.origins.zipIdx.filterMap (fun (o, i) => match o with
        | some (.use p) => if shape.gates.contains p then some i else none
        | _ => none))
    | none => []
  let mut out : EntrySplit := {}
  for e in entries do
    match classifyEntry shape e.1 with
    | .fits =>
      if gateSteps.isEmpty then out := { out with intended := out.intended ++ [e] }
      else
        let r ← env.ctorRatesAt key ctor [e] tries seed
        let onlyGates := r.failedAt.all (fun (i, _) => gateSteps.contains i) && !r.failedAt.isEmpty
        if r.ok == 0 && onlyGates then out := { out with gated := out.gated ++ [e] }
        else out := { out with intended := out.intended ++ [e] }
    | fit => out := { out with wrongShape := out.wrongShape ++ [(e, fit)] }
  return out

/-- `diagnose`, on the entries the constructor is meant for. A constructor nothing intended reaches is
    not tuned: its problem is the dispatch or the caller that sent it those inputs, and the split says
    which of its requirements those inputs broke. -/
def diagnoseIntended (specs : List RelSpec) (envFor : PlanBook → IO (Option InterpEnv)) (start : PlanBook)
    (key : SpecKey) (ctor : Name) (entries : List CtorEntry) (n : Nat := 12) :
    IO (Diagnosis × EntrySplit) := do
  let some env ← envFor start | return ({ key, ctor, baseline := ({}, {}), note := "the start book does not build" }, {})
  let some rel := specs.find? (·.inductiveName == key.inductiveName) | return ({ key, ctor, baseline := ({}, {}), note := "no spec" }, {})
  let some c := rel.ctors.find? (·.ctorName == ctor) | return ({ key, ctor, baseline := ({}, {}), note := "no such constructor" }, {})
  let shape := InputShape.of rel key c env.relations[key]?
  let split ← splitEntries env key ctor shape entries
  if split.intended.isEmpty then
    return ({ key, ctor, baseline := ({}, {}),
              note := s!"not tuned: no recorded entry is an input it is meant for ({shape.render})" }, split)
  let d ← diagnose specs envFor start key ctor [] (entries := split.intended) (n := n)
  return (d, split)

end Specimen.Interp

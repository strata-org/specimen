import Specimen.UnificationMonad

/-!
# `Val`: untyped runtime values for the schedule interpreter

The schedule interpreter (`Specimen.Interp`) runs a `Schedule` *as data* at runtime, with no
elaboration and no metaprogramming. Schedules talk about `Unknown`s (bare `Name`s) and
`ConstructorExpr`s (untyped constructor trees), so the interpreter needs a universal value
domain to bind those unknowns to. That domain is `Val`: a constructor tree over `Name`s plus
`Nat`/`String` literals — exactly the information a `ConstructorExpr` or a `Pattern` can talk
about.

## Type-level arguments are dropped

`ConstructorExpr`s produced by `exprToConstructorExpr` retain implicit and instance-implicit
argument positions (as `.TyCtor`, `.CSort`, or `.Hole`), because the emitted Lean code needs them
to elaborate. `Val` is untyped, so those positions carry no information and are *dropped*
(`valueArgs`). This matches the compile-time pipeline on the other side: `Range`s — and hence the
`Pattern`s a `.Match` step matches against — are built by `convertToCtorExpr`, which already
skips arguments whose type is a sort or a class. So patterns and values agree on positions.

`valueArgs` cannot drop *every* type-class dictionary, though: `exprToConstructorExpr` classifies a
constant that is neither a constructor nor an inductive as `.FuncApp`, so `@LE.le Nat instLENat x y`
reifies with `Nat` as a droppable `.TyCtor` but `instLENat` as a `.FuncApp instLENat []`. Two
consequences, both deliberate:

* An unregistered *nullary* `.FuncApp` evaluates to the opaque atom `Val.ctor f []` rather than
  failing. A dictionary argument therefore passes through to a *leaf* harmlessly.
* Leaf checkers and producers read their arguments from the **end** of the value-argument list
  (`Specimen.Interp.Bridge`). Lean puts implicit and instance-implicit binders before the explicit
  ones, so "the last `n`" is exactly the explicit arguments, with no per-relation configuration.

An *interpreted* callee cannot read from the end: it binds its inputs positionally, one per value
position (`RelSchedule.inputNames`), so a surviving dictionary is one input too many. A call to such a
relation therefore drops its type and instance positions **by position** (`valueArgsAt`, fed the
relation's `typeArgIndices`), which is the only test that recognises every dictionary.

## `Nat` is normalized to a literal

`Nat` values reach the interpreter both as literals (`.lit (.natVal n)`, e.g. from
`ConstructorExpr.Lit`) and in constructor form (`Nat.succ (Nat.succ Nat.zero)`, e.g. from a
unification pattern). `Val.mkCtor` normalizes the constructor form to a literal, and
`matchPattern` understands `Nat.zero`/`Nat.succ` patterns against literals, so the two spellings
are interchangeable.
-/

open Lean

namespace Specimen.Interp

/-- An untyped runtime value: a constructor tree over constructor `Name`s, plus `Nat`/`String`
    literals. This is the domain the interpreter binds schedule `Unknown`s to.

    Invariant maintained by `Val.mkCtor` and `evalConstructorExpr`: `args` contains only
    value-level arguments (type and instance arguments are dropped), and `Nat`s are always
    `.lit (.natVal _)` rather than `Nat.succ`/`Nat.zero` chains. -/
inductive Val where
  /-- A constructor applied to its value-level arguments. -/
  | ctor (name : Name) (args : List Val)
  /-- A `Nat` or `String` literal. -/
  | lit (l : Literal)

namespace Val

/-- Smart constructor for `Val.ctor` that normalizes `Nat` constructor form to a literal. -/
def mkCtor (name : Name) (args : List Val) : Val :=
  match name, args with
  | ``Nat.zero, [] => .lit (.natVal 0)
  | ``Nat.succ, [.lit (.natVal n)] => .lit (.natVal (n + 1))
  | _, _ => .ctor name args

/-- The `Nat` a value denotes, if it denotes one. -/
def asNat? : Val → Option Nat
  | .lit (.natVal n) => some n
  | _ => none

mutual

/-- Structural equality on `Val`s (used by the interpreter for `Eq`/`Ne` checks). -/
def beq : Val → Val → Bool
  | .ctor n₁ as₁, .ctor n₂ as₂ => n₁ == n₂ && beqList as₁ as₂
  | .lit l₁, .lit l₂ => l₁ == l₂
  | _, _ => false

/-- Pointwise `Val.beq` on lists (mutual helper; `List.all₂` would need a nested recursive call). -/
def beqList : List Val → List Val → Bool
  | [], [] => true
  | v₁ :: vs₁, v₂ :: vs₂ => beq v₁ v₂ && beqList vs₁ vs₂
  | _, _ => false

end

instance : BEq Val := ⟨beq⟩

/-- Last component of a name, for readable output (`BinaryTree.Node` prints as `Node`). -/
private def shortName (n : Name) : String :=
  (n.componentsRev.head?.getD n).toString

mutual

/-- Renders a `Val` in surface-ish syntax (tuples, list literals, and `Nat`s read naturally). -/
partial def toStr : Val → String
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | .ctor ``Prod.mk [a, b] => s!"({toStr a}, {toStr b})"
  | .ctor ``List.nil _ => "[]"
  | .ctor ``List.cons [h, t] => s!"{toStrAtom h} :: {toStr t}"
  | .ctor n [] => shortName n
  | .ctor n args => s!"{shortName n} {" ".intercalate (args.map toStrAtom)}"

/-- `toStr`, parenthesized when the result would otherwise not be a single token. -/
partial def toStrAtom (v : Val) : String :=
  match v with
  | .lit _ => toStr v
  | .ctor _ [] => toStr v
  | .ctor ``Prod.mk [_, _] => toStr v
  | .ctor ``List.nil _ => toStr v
  | _ => s!"({toStr v})"

end

instance : ToString Val := ⟨toStr⟩
instance : Repr Val := ⟨fun v _ => toStr v⟩
instance : Inhabited Val := ⟨.lit (.natVal 0)⟩

/-- Right-nested tuple of a list of values, mirroring the `(x₁, (x₂, x₃))` tuples the derived
    code uses to return multiple outputs. `[]` is `Unit.unit`. -/
def tuple : List Val → Val
  | [] => .ctor ``Unit.unit []
  | [v] => v
  | v :: vs => .ctor ``Prod.mk [v, tuple vs]

/-- Number of constructor nodes in a value (a cheap size metric for reporting). -/
partial def size : Val → Nat
  | .lit _ => 1
  | .ctor _ args => 1 + (args.map size).foldl (· + ·) 0

/-- Every constructor name a value contains, in a stack-fold walk that does not recurse through Lean.

    Duplicates included; deduplication happens at the aggregator so the *counts* survive. -/
partial def ctorNames (v : Val) : List Name :=
  let rec go (stack : List Val) (acc : List Name) : List Name :=
    match stack with
    | [] => acc
    | .lit _ :: rest => go rest acc
    | .ctor n args :: rest => go (args ++ rest) (n :: acc)
  go [v] []

/-! ### k-path coverage

    A flat histogram of constructor names (`ctorNames`) is 1-path coverage, and it is too coarse to
    be a tuning target: it cannot tell `unaryApp (is _) (lit _)` from `unaryApp (is _) (getAttr ..)`,
    so a generator that only ever nests literals under an operator scores as well as one that nests
    everything. Every *cost* measure — time, absorbed failures, acceptance — actively rewards the
    former, because shallow uniform outputs are cheap to produce.

    k-path coverage (Havrikov & Zeller's measure for grammars, read here on the value tree the
    derivation produces) fixes that: count the *distinct* downward chains of `k` constructor names.
    Nesting one new shape under an operator creates a new k-path, so it registers; producing the same
    shape a thousand more times does not. -/

/-- Stand-in name for a scalar literal, so `f (lit 3)` and `f (lit 4)` share a path but stay
    distinguishable from `f (var ..)`. Without this the path space would include every integer. -/
def litPathName : Name := `«lit»

/-- Downward chains of at most `k` constructor names starting at this node.

    A chain stops early at a leaf rather than being dropped, so a value shallower than `k` still
    contributes its shape. `[]` only for `k = 0`. -/
partial def pathsAt (k : Nat) (v : Val) : List (List Name) :=
  match k, v with
  | 0, _ => []
  | _, .lit _ => [[litPathName]]
  | 1, .ctor n _ => [[n]]
  | k' + 1, .ctor n args =>
    let below := args.flatMap (pathsAt k')
    if below.isEmpty then [[n]] else below.map (n :: ·)

/-- Every node of a value, so `pathsAt` can be read at each of them. -/
partial def nodes (v : Val) : List Val :=
  let rec go (stack : List Val) (acc : List Val) : List Val :=
    match stack with
    | [] => acc
    | (w@(.lit _)) :: rest => go rest (w :: acc)
    | (w@(.ctor _ args)) :: rest => go (args ++ rest) (w :: acc)
  go [v] []

/-- The distinct k-paths a value exhibits. -/
partial def kPaths (k : Nat) (v : Val) : List (List Name) :=
  ((v.nodes).flatMap (pathsAt k)).eraseDups

end Val

/-- Bindings for schedule `Unknown`s. -/
abbrev ValEnv := Std.HashMap Unknown Val

/-- Interpretations of the (total) functions that appear in `ConstructorExpr.FuncApp` position.
    A function may fail, e.g. on a partial operation; the `String` is reported to the user. -/
abbrev FuncTable := Std.HashMap Name (List Val → Except String Val)

/-- Whether a `ConstructorExpr` occupies a type-level (or instance) position, and so carries no
    information at the untyped `Val` level. See the module docstring. -/
def isTypeLevel : ConstructorExpr → Bool
  | .TyCtor _ _ | .CSort _ | .Hole => true
  | _ => false

/-- The value-level arguments of an application, dropping the syntactically type-level ones.

    Not every dictionary argument is dropped here — see the module docstring — which is why leaf
    checkers and producers count their arguments from the end, and why a call to a relation whose type
    positions are known uses `valueArgsAt` instead. -/
def valueArgs (args : List ConstructorExpr) : List ConstructorExpr :=
  args.filter (fun a => !isTypeLevel a)

/-- The value-level arguments of an application of a relation whose type and instance positions are
    `typeIdx` (its `RelSchedule.typeArgIndices`): every argument at a position outside `typeIdx` that is
    not syntactically type-level either.

    **Position decides, because kind cannot.** Cedar's `MapNotContainsKey {α β} [DecidableEq α]` is
    called from `HasType.hasAttrRecordNotFound` as
    `MapNotContainsKey Attr (Qualified CedarType) instDecidableEqString a m`. `valueArgs` drops the two
    `.TyCtor`s and keeps `.FuncApp instDecidableEqString []`, which evaluated to an opaque atom and went
    to the callee as its first input. The callee binds nothing at position 2 — `extractTypeArgIndices`
    counts class positions — so every constructor of `MapNotContainsKey[3,4]` failed `bindInputs` with an
    arity mismatch and `backtrack` absorbed that as an ordinary discard: that call could never succeed in
    the interpreter, while the compiled generator runs it normally. (Established by reading the call path
    and by `ExtractTest`'s `Keyed` test, which has the same shape. It was not visible in Cedar samples:
    from the `HasType[0,4]` root, `hasAttrRecordNotFound` is almost never reached, and when it is, it fails
    earlier than this call.)

    The kind test is kept alongside the positions rather than replaced by them. It never drops a value —
    a `.TyCtor`, `.CSort` or `.Hole` in argument position is never one — so with complete positions the
    two agree, and with `typeIdx = []` (a monomorphic relation, a relation only leaves answer, or a
    hand-built `RelSchedule` that kept the default) this is exactly `valueArgs`. -/
def valueArgsAt (typeIdx : List Nat) (args : List ConstructorExpr) : List ConstructorExpr :=
  if typeIdx.isEmpty then valueArgs args
  else (args.zipIdx.filter (fun (a, i) => !typeIdx.contains i && !isTypeLevel a)).map Prod.fst

/-- Whether an expression is a *type-or-dictionary*: something that carries no runtime information,
    so the untyped layer can drop or opaque it.

    `valueArgs` catches the syntactically type-level cases. This catches the other kind: an
    unregistered `FuncApp` all of whose arguments are themselves types or dictionaries. `n * n`
    reifies as `HMul.hMul Nat Nat Nat (instHMul Nat (instMulNat)) n n`, so `instHMul` is an
    *applied* `FuncApp` — it cannot be dropped by `valueArgs` and it has no interpretation to
    register, but it is plainly a dictionary, because nothing of substance reaches it. A genuine
    function like `List.length xs` fails the test, since `xs` is a variable. -/
partial def isTypeOrDict (funcs : FuncTable) (e : ConstructorExpr) : Bool :=
  match e with
  | .FuncApp f args => !funcs.contains f && (valueArgs args).all (isTypeOrDict funcs)
  | e => isTypeLevel e

/-- The last `n` elements of a list; the whole list if it is shorter.

    How a leaf reads its arguments out of a hypothesis' value-argument list: Lean orders implicit
    and instance-implicit binders before the explicit ones, so the trailing `n` arguments are the
    explicit ones even when a type-class dictionary survived `valueArgs`. -/
def lastArgs {α : Type} (n : Nat) (l : List α) : List α :=
  l.drop (l.length - n)

/-- Evaluates a `ConstructorExpr` to a `Val` under the bindings `env`, using `funcs` to interpret
    `FuncApp` nodes. Type-level arguments are dropped (see the module docstring).

    An `Unknown` that is not bound is looked up in `funcs` as a nullary application, since
    `Range`-derived `ConstructorExpr`s spell nullary constants as `.Unknown`.

    An *applied* `FuncApp` with no registered interpretation is an error, but a nullary one becomes
    the opaque atom `Val.ctor f []`: that is how a surviving type-class dictionary (`instLENat`)
    passes through the untyped layer without needing to be registered. -/
partial def evalConstructorExpr (funcs : FuncTable) (env : ValEnv) :
    ConstructorExpr → Except String Val
  | .Unknown u =>
    match env[u]? with
    | some v => .ok v
    | none =>
      match funcs[u]? with
      | some f => f []
      | none => .error s!"unbound variable '{u}' (not in the environment, and no function or \
          constant of that name is registered)"
  | .Lit l => .ok (.lit l)
  | .Ctor c args => do
    let vs ← (valueArgs args).mapM (evalConstructorExpr funcs env)
    return Val.mkCtor c vs
  | .TyCtor c args => do
    -- A type constructor in *value* position: keep it as an opaque constructor tree. (In argument
    -- position it is dropped by `valueArgs` before we ever get here.)
    let vs ← (valueArgs args).mapM (evalConstructorExpr funcs env)
    return Val.mkCtor c vs
  | .FuncApp f args => do
    match funcs[f]? with
    | some fn => fn (← (valueArgs args).mapM (evalConstructorExpr funcs env))
    | none =>
      -- An unregistered application of nothing but types and dictionaries *is* a dictionary: it
      -- becomes an opaque atom, with its arguments discarded, since none of them carry a value.
      if (valueArgs args).all (isTypeOrDict funcs) then .ok (.ctor f [])
      else .error s!"no interpretation registered for function '{f}' \
        (register one in `InterpEnv.funcs`)"
  | .CSort _ => .error "cannot evaluate a sort to a runtime value"
  | .Hole => .error "cannot evaluate a hole to a runtime value"

/-- Matches the value `v` against the pattern `p`, extending `bindings`. Returns `none` if the
    pattern does not match. The wildcard pattern (`MExp.wildCardPattern`, i.e. the unknown `_`)
    binds nothing.

    A variable that is **already bound** — in `bindings` as passed, or by an earlier occurrence in this
    same pattern — must equal `v` (by `Val.beq`, the equality `Eq` checks use); it is never
    overwritten. That is what a repeated variable means in a constructor, and what
    `RelSchedule.guardPasses` has always assumed. This used to `insert` unconditionally, so a second
    occurrence silently replaced the first: Cedar's `HasType.binaryAppEqLitSame`, whose conclusion is
    `HasType (.binaryApp .eq (.lit p) (.lit p)) … (.bool .tt)`, reached here as that non-linear pattern
    and accepted `.binaryApp .eq (.lit 1) (.lit 2)` as `.bool .tt`. `schedulePrologue` now linearizes
    such a pattern as the deriver does, so a well-formed schedule never gets here with a repeat; this
    keeps one that does — a premise's destructuring `Match` (`P (x, x)`, `P x (.succ x)`), a
    hand-written schedule, a future lowering — sound rather than silently wrong.

    One deliberate divergence from emitted code follows. A *compiled* schedule loaded through
    `RelSchedule.ofInductiveSchedule` that rebinds a name — the deriver's `P x (.succ x)` output shape,
    where Lean's `match` simply shadows — now rejects here where the emitted code accepts. Rejecting is
    the correct reading of the constructor; it is noted because it is a place the interpreter and the
    emitted code can disagree.

    `Nat` patterns in constructor form (`Nat.zero` / `Nat.succ p`) match `Nat` literals. -/
partial def matchPattern (p : Pattern) (v : Val) (bindings : ValEnv) : Option ValEnv :=
  match p with
  | .UnknownPattern u =>
    if u == `_ then some bindings
    else
      -- One probe rather than `get?` then `insert`: this runs on the dispatch path (`guardPassesWith`)
      -- for every constructor at every entry to a mode.
      match bindings.getThenInsertIfNew? u v with
      | (none, bindings') => some bindings'
      | (some prior, bindings') => if prior == v then some bindings' else none
  | .LitPattern l => if v == .lit l then some bindings else none
  | .CtorPattern c ps =>
    match c, ps, v with
    | ``Nat.zero, [], .lit (.natVal 0) => some bindings
    | ``Nat.succ, [p'], .lit (.natVal (n + 1)) => matchPattern p' (.lit (.natVal n)) bindings
    | _, _, .ctor c' args =>
      if c == c' && ps.length == args.length then
        (ps.zip args).foldlM (fun acc (p', v') => matchPattern p' v' acc) bindings
      else none
    | _, _, _ => none

end Specimen.Interp

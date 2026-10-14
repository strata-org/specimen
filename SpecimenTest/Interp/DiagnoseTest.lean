import Specimen.Interp.Diagnose
import Specimen.Interp.InputShapes
import SpecimenTest.Interp.BSTInterpTest
import SpecimenTest.Interp.ExtractTest

/-!
# Diagnosing a constructor that rarely succeeds

`Interp.Diagnose` on a relation built to fail for the reason Cedar's `binaryAppContains` did: a premise
chooses a value **blind**, and a later premise then rejects it.

```
inductive AnyNat : Nat → Prop | any : ∀ n, AnyNat n
inductive Bnd : Nat → Nat → Prop
  | mk : ∀ lo x, AnyNat x → Between lo x (lo + 3) → Bnd lo x
```

Generating `x` from `lo` in declared order draws `x` from `AnyNat` — an arbitrary `Nat`, knowing nothing
of `lo` — and then checks `lo < x < lo + 3`, which two values out of every draw satisfy. The diagnosis
must localize the failure to the `Between` premise, trace what it read back to `AnyNat` as a blind
producer, propose the anchor move that puts `Between` first (so it *produces* `x` from `lo`), and accept
it on both seed sets. It must not need to be told any of this.
-/

open Plausible Schedules Specimen Specimen.Interp SpecimenTest.InterpBST

namespace SpecimenTest.InterpDiagnose

inductive AnyNat : Nat → Prop where
  | any : ∀ n, AnyNat n

inductive Bnd : Nat → Nat → Prop where
  | mk : ∀ lo x, AnyNat x → Between lo x (lo + 3) → Bnd lo x

def anySpec : RelSpec where
  inductiveName := ``AnyNat
  argNames := [`a_5]
  recFnName := `aux_any
  ctors := [{ ctorName := ``AnyNat.any, vars := [{ name := `n, ty := (``Nat, []) }],
              conclusionArgs := [.Unknown `n] }]

def bndSpec : RelSpec where
  inductiveName := ``Bnd
  argNames := [`a_6, `b_6]
  recFnName := `aux_bnd
  ctors :=
    [{ ctorName := ``Bnd.mk
     , vars := [{ name := `lo, ty := (``Nat, []) }, { name := `x, ty := (``Nat, []) }]
     , hypotheses :=
         [ (``AnyNat, [.Unknown `x])
         , (``Between, [.Unknown `lo, .Unknown `x,
             .Ctor ``Nat.succ [.Ctor ``Nat.succ [.Ctor ``Nat.succ [.Unknown `lo]]]]) ]
     , conclusionArgs := [.Unknown `lo, .Unknown `x] }]

def bndSpecs : List RelSpec := [betweenSpec, anySpec, bndSpec]

/-- `fun lo => ∃ x, Bnd lo x`. -/
def bndKey : SpecKey := { inductiveName := ``Bnd, outputIndices := [1], deriveSort := .Generator }

/-- Declared order: `AnyNat x` first, so `x` is chosen blind. -/
def blindFirst : PlanBook := ({} : PlanBook).set bndKey ``Bnd.mk [.use 0, .use 1]

/-- Checkers are published, as a real measurement does: once `Between` produces `x`, `AnyNat x` is a check. -/
def envFor (b : PlanBook) : IO (Option InterpEnv) :=
  pure ((leaves.deriveClosureWith bndSpecs [bndKey] b (deriveCheckers := true)).toOption.map
    (·.publishInterpretedCheckers))

/-! ## The diagnosis finds the cause and the fix -/

/-- info: (some 1, [(`x, 0)], some [Specimen.Interp.PlanStep.use 1, Specimen.Interp.PlanStep.use 0], true) -/
#guard_msgs in
#eval show IO _ from do
  let d ← diagnose bndSpecs envFor blindFirst bndKey ``Bnd.mk [[toVal 5]]
  return (d.failingPremise, d.blind, d.order.map (·.1), d.accepted)

-- Before the fix it rarely succeeds; after, always.
/-- info: (true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  let d ← diagnose bndSpecs envFor blindFirst bndKey ``Bnd.mk [[toVal 5]]
  let fixedAll := match d.order with
    | some (_, a, b) => a.ok == a.tried && b.ok == b.tried && a.tried > 0
    | none => false
  return (d.baseline.1.ok * 4 < d.baseline.1.tried, fixedAll)

/-! ## Entries are recorded where constructors actually run

`BstNode`'s sub-calls enter `BST` with bounds the root never passes, at sizes below the root's. The
recording keeps at most `entryCap` distinct entries per constructor, and each can be replayed. -/

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool × Bool) from do
  match leaves.deriveClosureWith specs [bstKey] ({} : PlanBook) with
  | .error _ => return (false, false, false, false)
  | .ok env =>
    let (_, entries) ← withEntries (env.sample bstKey 6 [toVal 0, toVal 20] 60 0 (some 11))
    let node := (entries.getD (bstKey, ``BST.BstNode) #[]).toList
    let run ← env.ctorRatesAt bstKey ``BST.BstNode node 2 7
    return (!node.isEmpty, node.length ≤ entryCap,
      node.all (fun (_, initSize, size) => size < initSize),
      node.any (fun (ins, _, _) => ins != [toVal 0, toVal 20]) && run.tried == 2 * node.length)


/-! ## The inputs each constructor is meant for

STLC's `typing` at mode `[1]` (context and type in, term out): `TConst` and `TAdd` need `τ = Nat`, `TAbs`
needs `τ = Fun _ _`, and `TVar` is gated by `lookup Γ x τ` — a premise reading only the inputs, unlike the
recursive calls, which are not gates. The trie over `τ` has exactly the two shapes. -/

open SpecimenTest.InterpExtract in
/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval show IO (Bool × Bool × Bool × Bool × Bool) from do
  let some env := (stlcLeaves.deriveClosureWith stlcSpecs [typingKey] {} (deriveCheckers := true)).toOption
    | return (false, false, false, false, false)
  let rs := env.relations[typingKey]?
  let shapeOf := fun (n : Lean.Name) =>
    InputShape.of typingRelSpec typingKey ((typingRelSpec.ctors.find? (·.ctorName == n)).getD default) rs
  let gates := typingRelSpec.ctors.map (fun c => (c.ctorName, (shapeOf c.ctorName).gates))
  let onlyTVarGated := gates.all (fun (n, g) => if n == ``typing.TVar then g == [0] else g.isEmpty)
  let tconst := shapeOf ``typing.TConst
  let toFun := classifyEntry tconst [toVal ([] : List type), toVal (type.Fun .Nat .Nat)]
  let toNat := classifyEntry tconst [toVal ([] : List type), toVal type.Nat]
  let trie := ShapeTrie.of typingRelSpec typingKey
  let leaves := trie.leaves.map (fun (sigs, cs) => (sigs, cs.length))
  return (onlyTVarGated, toFun == .patternMismatch 2, toNat == .fits,
    leaves == [(["Nat"], 4), (["Fun(_, _)"], 3)], trie.leaves.all (!·.2.isEmpty))

-- A repeated variable across input positions is an equality the inputs must satisfy.
/-- info: (true, true) -/
#guard_msgs in
#eval
  let shape : InputShape := { ctorName := `eq, patterns := [(0, .Unknown `x), (1, .Unknown `x)],
                              repeated := [`x], gates := [] }
  (classifyEntry shape [toVal 1, toVal 2] == .equalityViolated `x, classifyEntry shape [toVal 3, toVal 3] == .fits)

end SpecimenTest.InterpDiagnose

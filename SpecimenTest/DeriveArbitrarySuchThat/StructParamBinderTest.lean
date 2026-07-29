import Plausible.Gen
import Plausible.Arbitrary
import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Specimen.DeriveEnum

/-! # Structure-parameter instance-binder tests

When an inductive relation's output type is parameterized by a *structure* `P`
(rather than a plain `Sort`), each constructor field of a projection type like
`P.Label` or `P.info.Metadata` can only be produced if the derived instance
carries a matching `[Arbitrary P.Label]` / `[Enum P.Label]` binder. The deriver
computes these **demand-driven**: it emits a binder for exactly the projection
leaves that appear in the schedule — one per *used* leaf, and none for unused
ones. (`DeriveStructParamGenerator.lean` is the larger STLC-shaped witness of the
same capability; this file isolates the binder logic across every axis.)

The tests vary three things:

* **Leaf shape** — a *direct* field (`x : P.Used`), a leaf behind a *compound*
  type (`tags : List P.Label`), and a *nested* struct chain (`P.inner.Needed`).
* **Emission path** — the single-instance path (`derive_generator` /
  `derive_enumerator`) and the mutual path (`derive_mutual`). Both must emit the
  binders.
* **Producer sort** — generators and enumerators.

Every fixture uses the same poison technique to check the *demand-driven*
property: the **unused** sibling field is monomorphized to `Empty`, which has no
`Arbitrary`/`Enum` instance. So if the deriver over-emitted a binder for the
unused field, the instance would fail to synthesize at use-site. Where the
relation pins down the value's shape, an `#eval`'d computable **oracle** also
checks each sample is sound (not just that the instance elaborated). -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

namespace StructParamBinderTest

/-! ## §1 Direct leaf: a tagged binary tree

`TwoFields` bundles two abstract types; only `Used` is referenced (as the `leaf`
payload `x : P.Used`), `Unused` is the poison field. `TaggedTree` is recursive,
so generating it exercises the `[Arbitrary/Enum P.Used]` binder both at the base
case and underneath the recursive `node`. Monomorphize `Used = Nat`,
`Unused = Empty` throughout. -/

structure TwoFields where
  Used : Type
  Unused : Type

inductive TaggedTree (P : TwoFields) where
  | leaf (x : P.Used) : TaggedTree P
  | node (l r : TaggedTree P) : TaggedTree P

abbrev TF1 : TwoFields := ⟨Nat, Empty⟩

/-- Node count — a soundness oracle confirming a sample is a real `TaggedTree`. -/
def treeSize {P : TwoFields} : TaggedTree P → Nat
  | .leaf _ => 1
  | .node l r => treeSize l + treeSize r + 1

/-- `true` iff the tree is a single leaf — the oracle for `IsLeaf`. -/
def isLeaf {P : TwoFields} : TaggedTree P → Bool
  | .leaf _ => true
  | .node _ _ => false

/-- Constrains a tree to be exactly one leaf; deriving `∃ t, IsLeaf P t` must
    produce `.leaf x` with `x : P.Used`. Used for the single-instance path. -/
inductive IsLeaf (P : TwoFields) : TaggedTree P → Prop where
  | leaf : IsLeaf P (.leaf x)

/-- Accepts any well-formed tree (recursive relation). Used for the mutual path;
    generating it produces trees with `node`s, exercising the leaf binder in a
    recursive context. -/
inductive IsTree (P : TwoFields) : TaggedTree P → Prop where
  | leaf : IsTree P (.leaf x)
  | node : IsTree P l → IsTree P r → IsTree P (.node l r)

/-! ### §1a Single-instance generator (`derive_generator`)

The single-instance path must emit `[Arbitrary P.Used]` — and nothing for the
`Empty`-monomorphized `Unused`. -/
#guard_msgs(drop info, drop warning) in
derive_generator (fun (P : TwoFields) => ∃ t : TaggedTree P, IsLeaf P t)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let mut count := 0
  for s in List.range 10 do
    let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun t => IsLeaf TF1 t) 3) (s * 5 + 1)
    if !isLeaf t then
      throw (IO.userError "§1a unsound: IsLeaf generator produced a non-leaf")
    count := count + 1
  IO.println s!"§1a single-instance generator, direct leaf: {count} sound samples"

/-! ### §1b Single-instance enumerator (`derive_enumerator`)

Same relation via the enumerator path — exercises the `[Enum P.Used]` binder. -/
#guard_msgs(drop info, drop warning) in
derive_enumerator (fun (P : TwoFields) => ∃ t : TaggedTree P, IsLeaf P t)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let mut total := 0
  let results ← runSizedEnum
    (EnumSizedSuchThat.enumSizedST (fun t => IsLeaf TF1 t)) 3
  for r in results do
    match r with
    | .ok t =>
      if !isLeaf t then
        throw (IO.userError "§1b unsound: IsLeaf enumerator produced a non-leaf")
      total := total + 1
    | .error _ => pure ()
  IO.println s!"§1b single-instance enumerator, direct leaf: {total} sound results"

/-! ### §1c Mutual path, recursive relation (`derive_mutual`)

Both producer sorts at once, over the recursive `IsTree`. This is the original
demand-driven regression: the blind field-walk would have required
`[Arbitrary P.Unused]`, which cannot synthesize with `Unused = Empty`. -/
#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : TwoFields) => ∃ t : TaggedTree P, IsTree P t),
  enumerator (fun (P : TwoFields) => ∃ t : TaggedTree P, IsTree P t)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let mut count := 0
  for s in List.range 8 do
    let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun t => IsTree TF1 t) 4) (s * 7 + 1)
    -- Soundness: every sample is a real, finite `TaggedTree` (size ≥ 1).
    if treeSize t < 1 then
      throw (IO.userError "§1c unsound: degenerate tree")
    count := count + 1
  let results ← runSizedEnum
    (EnumSizedSuchThat.enumSizedST (fun t => IsTree TF1 t)) 3
  IO.println s!"§1c mutual, recursive relation: {count} gen samples, {results.length} enum results"

/-! ## §2 Compound leaf: a struct-param field behind `List`

`Bag` carries `tags : List P.Label` — the leaf `P.Label` appears only *inside*
`List _`, never as a bare field. The deriver must still emit `[Arbitrary P.Label]`
(and only that — `Phantom` is the `Empty` poison field). Deriving the generator
on the single-instance path covers both fixed behaviors at once: the compound
branch being demand-driven, and the single-instance path being wired.

NOTE: a `derive_enumerator` for a *compound* struct-param leaf currently fails
with a spurious `Enum (Except GenError (List P.Label))` synthesis goal — a
**separate, pre-existing** bug in the enumerator's compound-field emission (it
reproduces regardless of the struct-param binder work, and does not affect the
*direct*-leaf enumerator in §1b, nor a plain `Type` parameter). It is out of
scope here; this section derives a generator only. -/

structure Config where
  Label : Type
  Phantom : Type

inductive Bag (P : Config) where
  | mk (tags : List P.Label) : Bag P

def bagTags {P : Config} : Bag P → List P.Label
  | .mk tags => tags

inductive IsBag (P : Config) : Bag P → Prop where
  | mk : IsBag P (.mk tags)

abbrev Cfg1 : Config := ⟨Nat, Empty⟩

#guard_msgs(drop info, drop warning) in
derive_generator (fun (P : Config) => ∃ b : Bag P, IsBag P b)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let mut count := 0
  for s in List.range 6 do
    let b ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun b => IsBag Cfg1 b) 3) (s * 3 + 2)
    -- Soundness: `bagTags` is a genuine `List Nat` we can consume.
    let _ : Nat := (bagTags b).length
    count := count + 1
  IO.println s!"§2 compound leaf (List P.Label), generator, Phantom = Empty: {count} samples"

/-! ## §3 Nested struct: a two-step projection chain

`Outer.inner : Inner` is itself a structure; only `Inner.Needed` is used (reached
by the chain `P.inner.Needed`), so the deriver must emit
`[Arbitrary (Inner.Needed (Outer.inner P))]` and nothing for the other,
`Empty`-monomorphized fields. Derived on the mutual path for both producer
sorts. -/

structure Inner where
  Needed : Type
  NotNeeded : Type

structure Outer where
  inner : Inner
  TopLevel : Type

inductive Wrapped (P : Outer) where
  | mk (v : P.inner.Needed) : Wrapped P

inductive IsGood (P : Outer) : Wrapped P → Prop where
  | mk : IsGood P (.mk v)

abbrev Out1 : Outer := ⟨⟨Bool, Empty⟩, Empty⟩

#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : Outer) => ∃ w : Wrapped P, IsGood P w),
  enumerator (fun (P : Outer) => ∃ w : Wrapped P, IsGood P w)

#guard_msgs(drop info) in
#eval show IO Unit from do
  let _ ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
    (fun w => @IsGood Out1 w) 2) 7
  let results ← runSizedEnum
    (EnumSizedSuchThat.enumSizedST (fun w => @IsGood Out1 w)) 2
  IO.println s!"§3 nested struct (P.inner.Needed), mutual: ok, {results.length} enum results"

/-! ## §4 Per-leaf constraints are discovered, not hardcoded

The class attached to a struct-param leaf is determined by *how the leaf is
used*, exactly as constraint propagation (#42) does for plain `Sort` type
params — not fixed to the producer's own class. In particular a leaf that is
*compared by equality* needs `[DecidableEq leaf]`, and a leaf that is only
*generated* must NOT be saddled with a spurious `DecidableEq`.

`Pair` carries two leaf-typed fields `a b : P.Key`; `Distinct` accepts a pair
iff `a ≠ b`. Deriving `∃ p, Distinct P p` schedules an unconstrained generation
of `a` and `b` (→ `[Arbitrary P.Key]`) and an `Eq`/`Ne` check on them
(→ `[DecidableEq P.Key]`). Both binders are required: with `Key = Nat` (which has
both instances) it derives and runs; the `≠` check would fail to compile without
the discovered `DecidableEq`. `Spare` is the `Empty` poison field, confirming no
binder is emitted for the unused leaf. -/

structure KeyConfig where
  Key : Type
  Spare : Type

inductive Pair (P : KeyConfig) where
  | mk (a b : P.Key) : Pair P

inductive Distinct (P : KeyConfig) : Pair P → Prop where
  | mk : a ≠ b → Distinct P (.mk a b)

abbrev KC : KeyConfig := ⟨Nat, Empty⟩

#guard_msgs(drop info, drop warning) in
derive_generator (fun (P : KeyConfig) => ∃ p : Pair P, Distinct P p)

#guard_msgs(drop info) in
#eval show IO Unit from do
  -- The point is that this instance *synthesizes* — it requires both
  -- `[Arbitrary P.Key]` and the discovered `[DecidableEq P.Key]`; the `a ≠ b`
  -- check would not compile without the latter. We also assert soundness on any
  -- sample we manage to draw (generation is rejection-based, so a size that
  -- exhausts backtracking is tolerated, not a failure).
  let mut sound := 0
  for s in List.range 12 do
    let r ← (Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun p => Distinct KC p) 6) (s * 5 + 1) |>.toBaseIO)
    match r with
    | .ok (.mk a b) =>
      if a == b then
        throw (IO.userError "§4 unsound: Distinct generator produced equal components")
      sound := sound + 1
    | .error _ => pure ()  -- backtracking exhausted at this seed; fine
  IO.println s!"§4 per-leaf constraints (Arbitrary + discovered DecidableEq on P.Key): {sound} sound samples"

end StructParamBinderTest

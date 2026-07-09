import Plausible.Gen
import Plausible.Arbitrary
import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveArbitrary
import Specimen.DeriveEnum

/-! # Demand-driven struct-param binder tests

Verify that the deriver only emits instance binders for struct-param fields that
actually appear in the schedule. A struct with fields `Used : Type` and
`Unused : Type` should only require `[Arbitrary P.Used]` — not both.

This is a regression test for the demand-driven approach vs. the old
`expandStructInstBinders` which would blindly walk all fields. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true

namespace PartialLeafTest

/-! ## Test 1: Only one of two struct fields used

`TwoFields` has `Used : Type` and `Unused : Type`. The relation `HasVal` only
mentions `P.Used` in its constructors. If the deriver emits `[Arbitrary P.Unused]`
too, it would appear in the generated instance signature — but we deliberately
do NOT provide an `Arbitrary` instance for the `Unused` field's monomorphization,
so if the binder were emitted the instance would fail to synthesize at use-site. -/

structure TwoFields where
  Used : Type
  Unused : Type

inductive TaggedExpr (P : TwoFields) where
  | leaf (x : P.Used) : TaggedExpr P
  | node (l r : TaggedExpr P) : TaggedExpr P

inductive HasVal (P : TwoFields) : TaggedExpr P → Prop where
  | leaf : HasVal P (.leaf x)
  | node : HasVal P l → HasVal P r → HasVal P (.node l r)

#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : TwoFields) => ∃ e : TaggedExpr P, HasVal P e),
  enumerator (fun (P : TwoFields) => ∃ e : TaggedExpr P, HasVal P e)

/-! Monomorphize: `Used = Nat`, `Unused = Empty` (no Arbitrary instance for Empty).
    If the deriver emitted `[Arbitrary P.Unused]`, this #eval would fail to synthesize. -/
abbrev TF1 : TwoFields := ⟨Nat, Empty⟩

#guard_msgs(drop info) in
#eval show IO Unit from do
  let _ ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
    (fun e => HasVal TF1 e) 3) 42
  IO.println s!"partial-leaf test 1: derived instance synthesizes with Unused = Empty"

/-! ## Test 2: Struct field used only via compound type

`Config` has `Label : Type` and `Phantom : Type`. The constructor references
`P.Label` but never `P.Phantom` directly. -/

structure Config where
  Label : Type
  Phantom : Type

inductive LabelledList (P : Config) where
  | nil : LabelledList P
  | cons (tag : P.Label) (rest : LabelledList P) : LabelledList P

inductive IsLabelled (P : Config) : LabelledList P → Prop where
  | nil : IsLabelled P .nil
  | cons : IsLabelled P rest → IsLabelled P (.cons tag rest)

#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : Config) => ∃ xs : LabelledList P, IsLabelled P xs),
  enumerator (fun (P : Config) => ∃ xs : LabelledList P, IsLabelled P xs)

/-! Monomorphize: `Label = String`, `Phantom = Empty`. -/
abbrev C1 : Config := ⟨String, Empty⟩

#guard_msgs(drop info) in
#eval show IO Unit from do
  let _ ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
    (fun xs => IsLabelled C1 xs) 3) 42
  IO.println s!"partial-leaf test 2: compound-type case works with Phantom = Empty"

/-! ## Test 3: Nested struct, only inner field used

`Outer` has `inner : Inner` and `TopLevel : Type`. `Inner` has `Needed : Type`
and `NotNeeded : Type`. The relation only uses `P.inner.Needed`. -/

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

#guard_msgs(drop info, drop warning) in
derive_mutual
  generator  (fun (P : Outer) => ∃ w : Wrapped P, IsGood P w),
  enumerator (fun (P : Outer) => ∃ w : Wrapped P, IsGood P w)

/-! Monomorphize: `inner.Needed = Bool`, everything else `Empty`. -/
abbrev O1 : Outer := ⟨⟨Bool, Empty⟩, Empty⟩

#guard_msgs(drop info) in
#eval show IO Unit from do
  let _ ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST
    (fun w => @IsGood O1 w) 2) 7
  IO.println s!"partial-leaf test 3: nested struct, only inner.Needed required"

end PartialLeafTest

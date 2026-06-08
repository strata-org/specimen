/-
  Tests for `derive_generator` with type aliases, literal values, and opaque definitions.

  `TypeBoxPred` and `TypeBoxPredS` use `NatFoo.ty` which is an `abbrev` that
  unfolds to `Nat`. The deriver handles these because `whnf` reduces the alias.

  `TypeBoxPredOpaque` uses `SomeFoo.ty` where `SomeFoo` is `opaque`, so the
  projection cannot be unfolded. The deriver handles the projection expression
  but the generated code fails to elaborate because `Arbitrary SomeFoo.ty` and
  `DecOpt (x = x)` cannot be synthesized (expected for opaque types).
-/
import Specimen.DeriveConstrainedProducer
import Plausible.Attr

structure TypeBox where
  ty : Type

instance : Inhabited TypeBox := ⟨⟨Unit⟩⟩

abbrev NatFoo : TypeBox where
  ty := Nat

opaque SomeFoo : TypeBox

abbrev five := 5

inductive TypeBoxPred : Nat → Prop where
| someRefl {x : NatFoo.ty} : x = x → 0 = x → 5 = 5 → TypeBoxPred 5

inductive TypeBoxPredS : String → Prop where
| someRefl {x : NatFoo.ty} y : x = x → y = "foo" → TypeBoxPredS "foo"

inductive TypeBoxPredOpaque : Nat → Prop where
| someRefl {x : SomeFoo.ty} : x = x → TypeBoxPredOpaque five

instance (α : Type) (n : Nat) [OfNat α n] : ArbitrarySizedSuchThat α (fun x => OfNat.ofNat n = x) where
  arbitrarySizedST _ := return OfNat.ofNat n

/--
error: failed to synthesize instance of type class
  ArbitrarySizedSuchThat Nat fun x => OfNat.ofNat 0 = x

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.-/
#guard_msgs(all) in
#check ArbitrarySizedSuchThat.arbitrarySizedST (fun (x : Nat) => Eq (OfNat.ofNat 0) x)

-- These succeed: NatFoo.ty unfolds to Nat via whnf
#guard_msgs(error, drop info) in
derive_generator ∃ (n : Nat), TypeBoxPred n

#guard_msgs(error, drop info) in
derive_generator ∃ (n : _), TypeBoxPredS n

-- This fails at elaboration: SomeFoo is opaque so SomeFoo.ty cannot be resolved,
-- and DecOpt (x = x) has no instance for opaque types. Errors are dropped since
-- they are not user-friendly (see open-issues.md).
#guard_msgs(drop error, drop info) in
derive_generator ∃ (n : Nat), TypeBoxPredOpaque n

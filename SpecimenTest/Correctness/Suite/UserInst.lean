import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.UserInst
inductive Sums : Nat → Nat → Nat → Prop where
  | mk : a + b = n → Sums a b n
instance : BacktrackGenFor (Nat × Nat) (fun (a, b) => Sums a b n) where
  gen _ _ := do
    let a ← chooseNat 0 n
    pure (a, n - a)
@[specimen_sound] theorem sums_gen (n s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (a, b) => Sums a b n) (G := SGen) s l)
      (fun (a, b) => Sums a b n) := by
  show succObs.spec (do let a ← chooseNat 0 n; pure (a, n - a) : SGen (Nat × Nat)) _
  walk
  exact .mk (by omega)
instance : BacktrackGenForComplete (Nat × Nat) (fun (a, b) => Sums a b n) :=
  ⟨fun p hp => by
    obtain ⟨a, b⟩ := p
    obtain ⟨h⟩ := (hp : Sums a b n)
    exact ⟨0, fun _ _ _ _ => produces_bind_of (produces_chooseNat (k := a) _ (Nat.zero_le _) (by omega))
      (produces_pure_iff.mpr (by ext <;> simp <;> omega))⟩⟩
structure NatPair where
  x : Nat
  y : Nat
  deriving Repr, Inhabited
inductive HasSum10 : NatPair → Prop where
  | mk : Sums x y 10 → HasSum10 ⟨x, y⟩

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ (self : NatPair), HasSum10 self)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.UserInst

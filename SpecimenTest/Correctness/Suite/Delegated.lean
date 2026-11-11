import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.Delegated
inductive Tm : Type where
  | var (i : Nat)
  deriving Repr
def g (n : Nat) : Nat := n + 1
def f (n : Nat) : Bool := n % 2 == 0
def h (n : Nat) : Nat := n * 2
def p (a b : Nat) : Bool := a == b
inductive S1 : Tm → Prop where
  | mk : f (g i) = true → S1 (.var i)
inductive S2a : Tm → Prop where
  | mk : h i = i → S2a (.var i)
inductive S2b : Tm → Prop where
  | mk : p i i = true → S2b (.var i)
def g' (n : Nat) : Nat := if n = 0 then 0 else n - 1
instance : BacktrackGenFor Nat (fun i => g' i = i) where
  gen _ _ := pure 0
@[specimen_sound] theorem g'_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun i => g' i = i) (G := SGen) s l) (fun i => g' i = i) := by
  show succObs.spec (pure 0 : SGen Nat) _
  walk; rfl
instance : BacktrackGenForComplete Nat (fun i => g' i = i) :=
  ⟨fun i hi => ⟨0, fun _ _ _ _ => by
    have : i = 0 := by unfold g' at hi; split at hi <;> omega
    subst this; exact produces_pure_iff.mpr rfl⟩⟩
inductive R : Tm → Prop where
  | mk : g' i = i → R (.var i)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun (_u : Unit) => ∃ e : Tm, S1 e),
  generator (fun (_u : Unit) => ∃ e : Tm, S2a e),
  generator (fun (_u : Unit) => ∃ e : Tm, S2b e),
  generator (fun (_u : Unit) => ∃ e : Tm, R e)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.Delegated

import Specimen.Correctness.SuccObs

/-!
# Laws of producers, as classes

A derived producer is correct only if the producers it calls are, so its proofs assume their laws as
instances and reason one level deep. A derived instance gets its law from its worker's theorem; a
hand-written one from its author; an unconstrained generator's completeness is what a derived
producer's completeness is relative to.
-/

namespace Specimen.Correctness

variable {α : Type}

/-- Every success of the producer satisfies `P`. -/
class BacktrackGenForSound (α : Type) (P : α → Prop) [BacktrackGenFor α P] : Prop where
  sound : ∀ s l x, Produces (BacktrackGenFor.gen (P := P) (G := SGen) s l) x → P x

/-- Every value satisfying `P` is produced at every large enough size and leaf size. -/
class BacktrackGenForComplete (α : Type) (P : α → Prop) [BacktrackGenFor α P] : Prop where
  complete : ∀ x, P x → ∃ n, ∀ s l, n ≤ s → n ≤ l →
    Produces (BacktrackGenFor.gen (P := P) (G := SGen) s l) x

/-- The unconstrained generator produces every value at every large enough size. -/
class ArbitrarySizedComplete (α : Type) [Basalt.ArbitrarySized α] : Prop where
  complete : ∀ x : α, ∃ n, ∀ s, n ≤ s → Produces (Basalt.ArbitrarySized.arbitrarySized s : SGen α) x

/-- A premise that holds is checked true at every large enough size. -/
class DecOptComplete (P : Prop) [DecOpt P] : Prop where
  complete : P → ∃ n, ∀ s, n ≤ s → DecOpt.decOpt (P := P) s = .ok true

/-- A premise that fails is checked false at every large enough size. -/
class DecOptRefuteComplete (P : Prop) [DecOpt P] : Prop where
  refute : ¬ P → ∃ n, ∀ s, n ≤ s → DecOpt.decOpt (P := P) s = .ok false

/-! ## The bounds, chosen -/

namespace DecOptComplete
variable {P : Prop} [DecOpt P] [DecOptComplete P]
noncomputable def bound (h : P) : Nat := Classical.choose (complete h)
theorem ok (h : P) {s : Nat} (hs : bound h ≤ s) : DecOpt.decOpt (P := P) s = .ok true :=
  Classical.choose_spec (complete h) s hs
end DecOptComplete

namespace DecOptRefuteComplete
variable {P : Prop} [DecOpt P] [DecOptRefuteComplete P]
noncomputable def bound (h : ¬ P) : Nat := Classical.choose (refute h)
theorem ok (h : ¬ P) {s : Nat} (hs : bound h ≤ s) : DecOpt.decOpt (P := P) s = .ok false :=
  Classical.choose_spec (refute h) s hs
end DecOptRefuteComplete

/-- A premise that holds is checked true at every size: a check that does not use its size. Its
completeness needs no bound, so a generator's proof chooses none for it. -/
class DecOptCompleteAll (P : Prop) [DecOpt P] : Prop where
  ok : P → ∀ s, DecOpt.decOpt (P := P) s = .ok true

/-- A premise that fails is checked false at every size. -/
class DecOptRefuteCompleteAll (P : Prop) [DecOpt P] : Prop where
  ok : ¬ P → ∀ s, DecOpt.decOpt (P := P) s = .ok false

instance (priority := low) {P : Prop} [DecOpt P] [DecOptCompleteAll P] : DecOptComplete P :=
  ⟨fun h => ⟨0, fun s _ => DecOptCompleteAll.ok h s⟩⟩
instance (priority := low) {P : Prop} [DecOpt P] [DecOptRefuteCompleteAll P] : DecOptRefuteComplete P :=
  ⟨fun h => ⟨0, fun s _ => DecOptRefuteCompleteAll.ok h s⟩⟩

/-- A decidable premise is checked by deciding it, at every size. -/
instance {P : Prop} [Decidable P] : DecOptCompleteAll P := ⟨fun h _ => by simp [DecOpt.decOpt, h]⟩
instance {P : Prop} [Decidable P] : DecOptRefuteCompleteAll P := ⟨fun h _ => by simp [DecOpt.decOpt, h]⟩

namespace BacktrackGenForComplete

variable {P : α → Prop} [BacktrackGenFor α P] [BacktrackGenForComplete α P]

/-- A size from which `x` is produced. -/
noncomputable def bound (x : α) (h : P x) : Nat := Classical.choose (complete x h)

theorem produces {x : α} (h : P x) {s l : Nat} (hs : bound x h ≤ s) (hl : bound x h ≤ l) :
    Produces (BacktrackGenFor.gen (P := P) (G := SGen) s l) x :=
  Classical.choose_spec (complete x h) s l hs hl

end BacktrackGenForComplete

namespace ArbitrarySizedComplete

variable [Basalt.ArbitrarySized α] [ArbitrarySizedComplete α]

/-- A size from which `x` is drawn. -/
noncomputable def bound (x : α) : Nat := Classical.choose (complete x)

theorem produces {x : α} {s : Nat} (hs : bound x ≤ s) :
    Produces (Basalt.ArbitrarySized.arbitrarySized s : SGen α) x :=
  Classical.choose_spec (complete x) s hs

end ArbitrarySizedComplete

/-! ## Specimen's own producers -/

instance (v : α) : BacktrackGenForSound α (fun x => x = v) := ⟨fun _ _ x hx => (produces_pure_iff (a := v)).mp hx⟩
instance (v : α) : BacktrackGenForSound α (fun x => v = x) :=
  ⟨fun _ _ x hx => ((produces_pure_iff (a := v)).mp hx).symm⟩
instance (v : α) : BacktrackGenForComplete α (fun x => x = v) :=
  ⟨fun x h => ⟨0, fun _ _ _ _ => h ▸ produces_pure_iff.mpr rfl⟩⟩
instance (v : α) : BacktrackGenForComplete α (fun x => v = x) :=
  ⟨fun x h => ⟨0, fun _ _ _ _ => h ▸ produces_pure_iff.mpr rfl⟩⟩

end Specimen.Correctness

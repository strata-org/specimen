import Specimen.Correctness.ReachClose

/-!
# Laws of the leaf instances

Soundness (`@[specimen_sound]`), completeness and the searches' laws of the instances
`Specimen.BasaltBridge` gives for a premise on a natural number's bound (`n ≤ x`, `n < x`, `x ≤ n`,
`x < n`) and for a pair constrained equal (`a = b`, both produced), for the proofs `specimen.emitSound`
and `specimen.emitComplete` run on generators that call them.
-/

namespace Specimen.Correctness

open Basalt

/-! ## Bounds on a natural number: soundness -/

section NatBounds
variable (n s l : Nat)

@[specimen_sound] theorem natGe_gen :
    succObs.spec (BacktrackGenFor.gen (P := fun x => n ≤ x) (G := SGen) s l) (fun x => n ≤ x) := by
  show succObs.spec (do let k ← chooseNat 0 l; pure (n + k) : SGen Nat) _
  walk; omega

@[specimen_sound] theorem natGt_gen :
    succObs.spec (BacktrackGenFor.gen (P := fun x => n < x) (G := SGen) s l) (fun x => n < x) := by
  show succObs.spec (do let k ← chooseNat 0 l; pure (n + 1 + k) : SGen Nat) _
  walk; omega

@[specimen_sound] theorem natLe_gen :
    succObs.spec (BacktrackGenFor.gen (P := fun x => x ≤ n) (G := SGen) s l) (fun x => x ≤ n) := by
  show succObs.spec (chooseNat 0 n : SGen Nat) _
  walk; omega

@[specimen_sound] theorem natLt_gen :
    succObs.spec (BacktrackGenFor.gen (P := fun x => x < n) (G := SGen) s l) (fun x => x < n) := by
  show succObs.spec (if 0 < n then chooseNat 0 (n - 1) else Specimen.refute : SGen Nat) _
  walk; omega

@[specimen_sound] theorem natGe_enum :
    succObs.spec (EnumFor.enum (P := fun x => n ≤ x) (G := SGen) s l) (fun x => n ≤ x) :=
  natGe_gen n s l

@[specimen_sound] theorem natGt_enum :
    succObs.spec (EnumFor.enum (P := fun x => n < x) (G := SGen) s l) (fun x => n < x) :=
  natGt_gen n s l

@[specimen_sound] theorem natLe_enum :
    succObs.spec (EnumFor.enum (P := fun x => x ≤ n) (G := SGen) s l) (fun x => x ≤ n) :=
  natLe_gen n s l

@[specimen_sound] theorem natLt_enum :
    succObs.spec (EnumFor.enum (P := fun x => x < n) (G := SGen) s l) (fun x => x < n) :=
  natLt_gen n s l

end NatBounds


/-! ## Bounds on a natural number: completeness -/

section NatBounds

/-- The draw above a bound `b` reaches `x`, `b ≤ x`, at a leaf size of at least `x - b`. -/
theorem produces_above {b x l : Nat} (hx : b ≤ x) (hl : x - b ≤ l) :
    Produces (do let k ← chooseNat 0 l; pure (b + k) : SGen Nat) x :=
  produces_bind_of (produces_chooseNat (k := x - b) _ (Nat.zero_le _) hl)
    (produces_pure_iff.mpr (by omega))

theorem produces_upTo {n x : Nat} (hx : x ≤ n) : Produces (chooseNat 0 n : SGen Nat) x :=
  produces_chooseNat _ (Nat.zero_le _) hx

theorem produces_below {n x : Nat} (hx : x < n) :
    Produces (if 0 < n then chooseNat 0 (n - 1) else Specimen.refute : SGen Nat) x := by
  simp only [show 0 < n from by omega, ite_true]; exact produces_chooseNat _ (Nat.zero_le _) (by omega)

instance {n : Nat} : BacktrackGenForComplete Nat (fun x => n ≤ x) :=
  ⟨fun x hx => ⟨x - n, fun _ _ _ hl => produces_above hx hl⟩⟩
instance {n : Nat} : BacktrackGenForComplete Nat (fun x => n < x) :=
  ⟨fun x hx => ⟨x - n, fun _ _ _ hl => by
    show Produces (do let k ← chooseNat 0 _; pure (n + 1 + k) : SGen Nat) x
    exact produces_above (b := n + 1) hx (by omega)⟩⟩
instance {n : Nat} : BacktrackGenForComplete Nat (fun x => x ≤ n) :=
  ⟨fun _ hx => ⟨0, fun _ _ _ _ => produces_upTo hx⟩⟩
instance {n : Nat} : BacktrackGenForComplete Nat (fun x => x < n) :=
  ⟨fun _ hx => ⟨0, fun _ _ _ _ => produces_below hx⟩⟩

instance {n : Nat} : EnumForComplete Nat (fun x => n ≤ x) :=
  ⟨fun x hx => ⟨x - n, fun _ _ _ hl => produces_above hx hl⟩⟩
instance {n : Nat} : EnumForComplete Nat (fun x => n < x) :=
  ⟨fun x hx => ⟨x - n, fun _ _ _ hl => by
    show Produces (do let k ← chooseNat 0 _; pure (n + 1 + k) : SGen Nat) x
    exact produces_above (b := n + 1) hx (by omega)⟩⟩
instance {n : Nat} : EnumForComplete Nat (fun x => x ≤ n) :=
  ⟨fun _ hx => ⟨0, fun _ _ _ _ => produces_upTo hx⟩⟩
instance {n : Nat} : EnumForComplete Nat (fun x => x < n) :=
  ⟨fun _ hx => ⟨0, fun _ _ _ _ => produces_below hx⟩⟩

instance {n : Nat} : EnumForSearch Nat (fun x => n ≤ x) := ⟨fun _ _ => by
  show SearchHits (do let k ← chooseNat 0 _; pure (n + k) : SGen Nat) (do let k ← chooseNat 0 _; pure (n + k))
  walk⟩
instance {n : Nat} : EnumForSearch Nat (fun x => n < x) := ⟨fun _ _ => by
  show SearchHits (do let k ← chooseNat 0 _; pure (n + 1 + k) : SGen Nat) (do let k ← chooseNat 0 _; pure (n + 1 + k))
  walk⟩
instance {n : Nat} : EnumForSearch Nat (fun x => x ≤ n) := ⟨fun _ _ => by
  show SearchHits (chooseNat 0 n : SGen Nat) (chooseNat 0 n)
  walk⟩
instance {n : Nat} : EnumForSearch Nat (fun x => x < n) := ⟨fun _ _ => by
  show SearchHits (if 0 < n then chooseNat 0 (n - 1) else Specimen.refute : SGen Nat)
    (if 0 < n then chooseNat 0 (n - 1) else Specimen.refute)
  walk⟩

end NatBounds


/-! ## A pair constrained equal -/

section EqPair
variable {α : Type} [Basalt.ArbitrarySized α]

@[specimen_sound] theorem eqPair_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (p : α × α) => match p with | (a, b) => a = b) (G := SGen) s l)
      (fun (p : α × α) => match p with | (a, b) => a = b) := by
  show succObs.spec (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a) : SGen (α × α)) _
  walk; rfl

@[specimen_sound] theorem eqPair_enum (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun (p : α × α) => match p with | (a, b) => a = b) (G := SGen) s l)
      (fun (p : α × α) => match p with | (a, b) => a = b) :=
  eqPair_gen s l

theorem eqPair_searchFinds [ArbitrarySizedSearch α] (s l : Nat) :
    SearchFinds (EnumFor.enum (P := fun (p : α × α) => match p with | (a, b) => a = b) (G := Search) s l)
      (EnumFor.enum (P := fun (p : α × α) => match p with | (a, b) => a = b) (G := SGen) s l) := by
  show SearchFinds (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a) : Search (α × α))
    (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a))
  walk

/-- A checker's search for an equal pair accepts only a pair the rest of the check accepts. -/
@[specimen_sound] theorem eqPair_search_accepts [ArbitrarySizedSearch α] {s l : Nat}
    {k : α × α → Except Plausible.GenError Bool}
    (h : Specimen.CheckerSearch.search (P := fun (p : α × α) => match p with | (a, b) => a = b) s l k = .ok true) :
    ∃ p, (match p with | (a, b) => a = b) ∧ k p = .ok true :=
  search_accepts (eqPair_searchFinds s l) (eqPair_enum s l) h

theorem produces_eqPair [ArbitrarySizedComplete α] {x : α} {l : Nat}
    (hl : ArbitrarySizedComplete.bound x ≤ l) :
    Produces (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a) : SGen (α × α)) (x, x) :=
  produces_bind_of (ArbitrarySizedComplete.produces hl) (produces_pure_iff.mpr rfl)

instance [ArbitrarySizedComplete α] :
    BacktrackGenForComplete (α × α) (fun (p : α × α) => match p with | (a, b) => a = b) :=
  ⟨fun p hp => by
    obtain ⟨x, y⟩ := p
    cases (hp : x = y)
    exact ⟨ArbitrarySizedComplete.bound x, fun _ _ _ hl => produces_eqPair hl⟩⟩

instance [ArbitrarySizedComplete α] :
    EnumForComplete (α × α) (fun (p : α × α) => match p with | (a, b) => a = b) :=
  ⟨fun p hp => by
    obtain ⟨x, y⟩ := p
    cases (hp : x = y)
    exact ⟨ArbitrarySizedComplete.bound x, fun _ _ _ hl => produces_eqPair hl⟩⟩

instance [ArbitrarySizedHits α] :
    EnumForSearch (α × α) (fun (p : α × α) => match p with | (a, b) => a = b) := ⟨fun _ l => by
  show SearchHits (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a) : SGen (α × α))
    (do let a ← Basalt.ArbitrarySized.arbitrarySized l; pure (a, a))
  walk⟩


/-! The same laws with the predicate as the proofs see it once `dsimp` has read the `match` on the
pair as its projections (`fun x => x.1 = x.2`), about the same instances: instances are found by the
predicate's syntax, the two forms are equal only by definition. -/

@[specimen_sound] theorem eqPair_gen' (s l : Nat) :
    succObs.spec (@BacktrackGenFor.gen (α × α) (fun x => x.1 = x.2) instBacktrackGenForEqPair SGen _ _ _ _ _ _ s l)
      (fun x => x.1 = x.2) :=
  eqPair_gen s l

@[specimen_sound] theorem eqPair_enum' (s l : Nat) :
    succObs.spec (@EnumFor.enum (α × α) (fun x => x.1 = x.2) instEnumForEqPair SGen _ _ _ _ _ _ s l)
      (fun x => x.1 = x.2) :=
  eqPair_gen s l

@[specimen_sound] theorem eqPair_search_accepts' [ArbitrarySizedSearch α] {s l : Nat}
    {k : α × α → Except Plausible.GenError Bool}
    (h : @Specimen.CheckerSearch.search (α × α) (fun x => x.1 = x.2) _ s l k = .ok true) :
    ∃ p : α × α, p.1 = p.2 ∧ k p = .ok true :=
  eqPair_search_accepts h

instance [ArbitrarySizedComplete α] :
    @BacktrackGenForComplete (α × α) (fun x => x.1 = x.2) instBacktrackGenForEqPair :=
  ⟨fun p hp => BacktrackGenForComplete.complete
    (P := fun (p : α × α) => match p with | (a, b) => a = b) p hp⟩

instance [ArbitrarySizedComplete α] :
    @EnumForComplete (α × α) (fun x => x.1 = x.2) instEnumForEqPair :=
  ⟨fun p hp => EnumForComplete.complete
    (P := fun (p : α × α) => match p with | (a, b) => a = b) p hp⟩

instance [ArbitrarySizedHits α] :
    @EnumForSearch (α × α) (fun x => x.1 = x.2) instEnumForEqPair :=
  ⟨fun s l => EnumForSearch.hits (P := fun (p : α × α) => match p with | (a, b) => a = b) s l⟩

end EqPair

end Specimen.Correctness

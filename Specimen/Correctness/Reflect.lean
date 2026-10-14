/-!
# Reflected inductive relations (`RelSpec` / `Provable`)

Lean's inductive relations are not first-class *as structure* — no theorem can quantify over "a
relation and its constructors." To prove producers correct **once, generically**, we reflect a
relation into data (`RelSpec`) with an inductively-defined denotation (`Provable`) whose own
recursor we can induct on. The two steps a concrete-relation proof cannot reach generically —
*applying a constructor* (soundness) and *inducting on a derivation* (completeness) — become
`Provable.intro` and induction on `Provable`, uniformly.

A constructor is reflected as: an existential binder context `Vars`, the list of recursive
sub-goals `recs` (each must itself be `Provable`), a conjoined decidable side-condition `side`, and
the conclusion `concl` (the argument the constructor concludes at), all as functions of `Vars`.

The metaprogram's only residual per-relation duty is an **adequacy** proof `Provable rSpec a ↔ R a`
(see `EvSlice` for the `Ev` instance).

`provable_iff` below is the inversion principle — membership is exactly "some reflected constructor
applies" — and `provable_covered` packages it as the `hadeq` hypothesis `stepBacktrack_sound` wants, so
that obligation is discharged generically rather than per relation.
-/

namespace Specimen.Correctness

/-- A reflected constructor of an inductive relation over argument type `A`. -/
structure RelCtor (A : Type) where
  /-- The constructor's existentially-bound variables (a tuple type). -/
  Vars : Type
  /-- Recursive sub-goals: each must itself be `Provable`. -/
  recs : Vars → List A
  /-- Conjoined non-recursive side-condition (equalities, decidable atoms, …). -/
  side : Vars → Prop
  /-- The argument this constructor concludes at. -/
  concl : Vars → A

/-- A reflected inductive relation over `A`: its list of constructors. -/
structure RelSpec (A : Type) where
  ctors : List (RelCtor A)

/-- Denotation of a `RelSpec`: the least predicate closed under its reflected constructors. Its
    single `intro` is the generic "apply a constructor"; its recursor is the generic "induct on a
    derivation". -/
inductive Provable {A : Type} (r : RelSpec A) : A → Prop where
  | intro (c : RelCtor A) (hc : c ∈ r.ctors) (vs : c.Vars)
      (hrec : ∀ a ∈ c.recs vs, Provable r a) (hside : c.side vs) :
      Provable r (c.concl vs)

/-- **Inversion for `Provable`**: membership is exactly "some reflected constructor applies".

This is what feeds `stepBacktrack_sound`'s `hadeq` hypothesis. Without it, every relation needs a
hand-written proof that its branch conditions cover the relation; with it, that obligation is
discharged generically once the branch conditions are *defined* as these existentials. -/
theorem provable_iff {A : Type} (r : RelSpec A) (a : A) :
    Provable r a ↔ ∃ c ∈ r.ctors, ∃ vs : c.Vars,
      c.concl vs = a ∧ c.side vs ∧ ∀ b ∈ c.recs vs, Provable r b := by
  constructor
  · intro h
    cases h with
    | intro c hc vs hrec hside => exact ⟨c, hc, vs, rfl, hside, hrec⟩
  · rintro ⟨c, hc, vs, rfl, hside, hrec⟩
    exact Provable.intro c hc vs hrec hside

/-- The canonical branch condition for a reflected constructor: "this constructor applies at `a`". -/
def RelCtor.applies {A : Type} (r : RelSpec A) (c : RelCtor A) (a : A) : Prop :=
  ∃ vs : c.Vars, c.concl vs = a ∧ c.side vs ∧ ∀ b ∈ c.recs vs, Provable r b

/-- **`hadeq` for free.** `stepBacktrack_sound` needs "the relation is covered by the branch
    conditions"; with the canonical conditions that is exactly `provable_iff`, so no relation has to
    prove it by hand. -/
theorem provable_covered {A : Type} (r : RelSpec A) :
    ∀ a, Provable r a ↔ ∃ c ∈ r.ctors, c.applies r a := provable_iff r

end Specimen.Correctness

import Specimen.DecOpt
import Specimen.EnumeratorCombinators
import Specimen.Correctness.LazyListLemmas

/-!
# Verified specifications for the checker and enumerator combinators

This file proves the *relation-independent* facts about the checker combinators
(`DecOpt.negOpt`, `DecOpt.andOpt`, `DecOpt.andOptList`, `DecOpt.checkerBacktrack`) that every
derived `DecOpt` instance is built from. They mirror the combinator specifications in §2 of
*Computing Correctly with Inductive Relations* (PLDI'22).

The generic checker soundness/completeness theorems reduce, at each constructor, to these lemmas
plus the correctness of the sub-checkers invoked for that constructor's premises:

* `checkerBacktrack_ok_true`  — the backtracking checker succeeds iff *some* branch succeeds
  (the disjunction over constructors).
* `checkerBacktrack_ok_false` — it definitively fails iff *every* branch definitively fails.
* `andOptList_ok_true`        — a conjunction of premise-checks succeeds iff *all* succeed.
* `negOpt_ok`                 — negation flips the verdict and preserves "don't know" (errors).

`.ok true`/`.ok false`/`.error` model the paper's `Some true`/`Some false`/`None` (proved /
disproved / out-of-fuel), respectively.
-/

open Plausible DecOpt

namespace Specimen.Correctness

/-- Negation flips a definite verdict (`ok`) and preserves "don't know" (`error`). -/
theorem negOpt_ok {a : Except GenError Bool} {b : Bool} :
    negOpt a = .ok b ↔ a = .ok (!b) := by
  cases a with
  | ok x => cases x <;> cases b <;> simp [negOpt]
  | error e => simp [negOpt]

/-- Binary optional-conjunction succeeds iff both operands succeed. -/
theorem andOpt_ok_true {a b : Except GenError Bool} :
    andOpt a b = .ok true ↔ a = .ok true ∧ b = .ok true := by
  cases a with
  | ok x => cases x <;> simp [andOpt]
  | error e =>
    cases b with
    | ok y => cases y <;> simp [andOpt]
    | error e' => simp [andOpt]

/-- **`false` annihilates conjunction**: a conjunction is definitively false iff *either* operand is,
    regardless of whether the other is inconclusive. This is the law that fails for a
    left-preferring `andOpt` (which answers `.error` for `andOpt (.error _) (.ok false)`), and it is
    the negative-direction counterpart of `andOpt_ok_true`. -/
theorem andOpt_ok_false {a b : Except GenError Bool} :
    andOpt a b = .ok false ↔ a = .ok false ∨ b = .ok false := by
  cases a with
  | ok x => cases x <;> simp [andOpt]
  | error e =>
    cases b with
    | ok y => cases y <;> simp [andOpt]
    | error e' => simp [andOpt]

/-- Left-fold of `andOpt` from an accumulator: succeeds iff the accumulator and every element
    succeed. Generalizing the accumulator is what makes the list induction go through. -/
theorem foldl_andOpt_ok_true (acc : Except GenError Bool) (bs : List (Except GenError Bool)) :
    List.foldl andOpt acc bs = .ok true ↔ acc = .ok true ∧ ∀ x ∈ bs, x = .ok true := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, andOpt_ok_true, List.forall_mem_cons, and_assoc]

/-- A conjunction of premise-checks succeeds iff *every* premise-check succeeds. -/
theorem andOptList_ok_true {bs : List (Except GenError Bool)} :
    andOptList bs = .ok true ↔ ∀ x ∈ bs, x = .ok true := by
  rw [andOptList, foldl_andOpt_ok_true]
  simp

/-- Left-fold counterpart of `andOpt_ok_false`. -/
theorem foldl_andOpt_ok_false (acc : Except GenError Bool) (bs : List (Except GenError Bool)) :
    List.foldl andOpt acc bs = .ok false ↔ acc = .ok false ∨ (.ok false) ∈ bs := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, andOpt_ok_false, or_assoc]
    simp [List.mem_cons, eq_comm]

/-- **A conjunction of premise-checks is definitively false iff *some* premise-check is.** Together
    with `andOptList_ok_true` this gives conjunction the same two-sided specification
    `checkerBacktrack` already enjoys (`checkerBacktrack_ok_true` / `_ok_false`), which is what a
    derived checker needs to be proved *decisive* — it cannot answer "don't know" when one premise
    already refutes the constructor. -/
theorem andOptList_ok_false {bs : List (Except GenError Bool)} :
    andOptList bs = .ok false ↔ (.ok false) ∈ bs := by
  rw [andOptList, foldl_andOpt_ok_false]
  simp

/-- Spec of the internal accumulator recursion of `checkerBacktrack`: it reports `ok true` iff
    *some* checker in the list reports `ok true`, independently of the accumulator. -/
theorem checkerBacktrack_aux_ok_true (l : List (Unit → Except GenError Bool)) (b : Bool) :
    checkerBacktrack.aux l b = .ok true ↔ ∃ c ∈ l, c () = .ok true := by
  induction l generalizing b with
  | nil => cases b <;> simp [checkerBacktrack.aux]
  | cons c cs ih =>
    simp only [checkerBacktrack.aux]
    cases hc : c () with
    | ok x =>
      cases x with
      | true => simp [hc]
      | false => rw [ih]; simp [hc]
    | error e => rw [ih]; simp [hc]

/-- **Backtracking checker, positive direction.** `checkerBacktrack` succeeds (`ok true`) iff at
    least one of its branch-checkers succeeds — the disjunction over a relation's constructors. -/
theorem checkerBacktrack_ok_true {cs : List (Unit → Except GenError Bool)} :
    checkerBacktrack cs = .ok true ↔ ∃ c ∈ cs, c () = .ok true := by
  simpa [checkerBacktrack] using checkerBacktrack_aux_ok_true cs false

/-- Spec of the internal accumulator recursion for the definite-failure verdict: `checkerBacktrack`
    reports `ok false` iff no checker errored so far (`b = false`) and *every* checker reports
    `ok false`. -/
theorem checkerBacktrack_aux_ok_false (l : List (Unit → Except GenError Bool)) (b : Bool) :
    checkerBacktrack.aux l b = .ok false ↔ b = false ∧ ∀ c ∈ l, c () = .ok false := by
  induction l generalizing b with
  | nil => cases b <;> simp [checkerBacktrack.aux]
  | cons c cs ih =>
    simp only [checkerBacktrack.aux]
    cases hc : c () with
    | ok x =>
      cases x with
      | true => simp [hc]
      | false => rw [ih]; simp [hc]
    | error e => rw [ih]; simp [hc]

/-- **Backtracking checker, negative direction.** `checkerBacktrack` definitively fails (`ok false`)
    iff *every* branch-checker definitively fails — no branch was inconclusive. -/
theorem checkerBacktrack_ok_false {cs : List (Unit → Except GenError Bool)} :
    checkerBacktrack cs = .ok false ↔ ∀ c ∈ cs, c () = .ok false := by
  simpa [checkerBacktrack] using checkerBacktrack_aux_ok_false cs false

/-- If every branch returns a *definite* verdict (`ok _`, never `error`), so does `checkerBacktrack`.
    This is the building block for **decisiveness** of a backtracking checker: it can't get stuck at
    `error` when none of its branches can. -/
theorem checkerBacktrack_isOk {cs : List (Unit → Except GenError Bool)}
    (h : ∀ c ∈ cs, ∃ b, c () = .ok b) : ∃ b, checkerBacktrack cs = .ok b := by
  by_cases ht : ∃ c ∈ cs, c () = .ok true
  · exact ⟨true, checkerBacktrack_ok_true.mpr ht⟩
  · refine ⟨false, checkerBacktrack_ok_false.mpr ?_⟩
    intro c hc
    obtain ⟨b, hb⟩ := h c hc
    cases b with
    | true => exact absurd ⟨c, hc, hb⟩ ht
    | false => exact hb

/-! ## The enumerator's branch-combining law

`EnumeratorCombinators.enumerate` is the enumerator's analogue of the generator's `backtrack`, and
this is the analogue of the generator's backtrack support law (`genSupportAt_backtrack`): a value is
enumerated iff *some* branch enumerates it.

Two differences from the generator case are worth noting, because they make this the *easier* half:

* **No weights.** `enumerate` runs every branch exactly once rather than sampling one, so there is no
  weight-positivity side condition — and hence no analogue of the generator's `size == 0` dead
  recursion. The emitted `size = 0` case simply omits the recursive branches.
* **It is provable.** `enumerate` is built only from `LazyList.append`, which is total and structurally
  recursive. The enumerator's *bind* is a different story — see the note in `ProducerInterp.lean`. -/

/-- A value is in `enumerateAll`'s output iff some branch produces it. -/
theorem mem_enumerateAll {α : Type} {a : Except GenError α} (fuel : Nat) :
    ∀ (es : List (ExceptT GenError Enumerator α)),
      a ∈ EnumeratorCombinators.enumerateAll es fuel ↔ ∃ e ∈ es, a ∈ e fuel
  | [] => by
    simp only [EnumeratorCombinators.enumerateAll, List.foldr_nil]
    constructor
    · intro h; cases h
    · intro ⟨_, he, _⟩; exact absurd he (by simp)
  | e :: es => by
    show a ∈ LazyList.append (e fuel) (EnumeratorCombinators.enumerateAll es fuel) ↔ _
    rw [LazyList.mem_append, mem_enumerateAll fuel es]
    constructor
    · rintro (h | ⟨e', he', h⟩)
      · exact ⟨e, List.Mem.head _, h⟩
      · exact ⟨e', List.Mem.tail _ he', h⟩
    · rintro ⟨e', he', h⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact Or.inl h
      · exact Or.inr ⟨e', he', h⟩

/-! ### `squashErrors`: values untouched, verdict information preserved

`enumerate` passes `enumerateAll`'s output through `squashErrors`, which drops definitive failures and keeps
only the first inconclusive one. The two laws below are what that must not break:

* every **value** survives, and nothing else becomes a value (`mem_squashErrors_ok`);
* an **inconclusive** failure survives iff there was one, and no failure is introduced that was not an
  inconclusive one (`hasInconclusive_squashErrors`, `inconclusive_of_mem_squashErrors`) — which is all
  the checker's `lazyListBacktrackOpt` reads. -/

private theorem not_mem_lnil {α} {a : α} : ¬ a ∈ (LazyList.lnil : LazyList α) := fun h => by cases h

/-- Forcing a freshly built thunk runs its function. Stated for `simp` rather than unfolding `Thunk.get`,
    which would also unfold every `t.get` a recursive call is made on. -/
@[simp] private theorem thunk_get_mk {β : Type} (f : Unit → β) : (Thunk.mk f).get = f () := rfl

theorem mem_squashErrors_go_ok {α : Type} {a : α} :
    ∀ (p : Option GenError) (l : LazyList (Except GenError α)),
      (.ok a : Except GenError α) ∈ EnumeratorCombinators.squashErrors.go p l ↔ .ok a ∈ l
  | none, .lnil => by simp [EnumeratorCombinators.squashErrors.go]
  | some e, .lnil => by
    simp only [EnumeratorCombinators.squashErrors.go, LazyList.mem_lcons]
    constructor
    · rintro (h | h)
      · cases h
      · exact absurd h not_mem_lnil
    · intro h; exact absurd h not_mem_lnil
  | p, .lcons (.ok b) t => by
    simp only [thunk_get_mk, EnumeratorCombinators.squashErrors.go, LazyList.mem_lcons]
    rw [mem_squashErrors_go_ok p t.get]
  | p, .lcons (.error e) t => by
    simp only [EnumeratorCombinators.squashErrors.go, LazyList.mem_lcons]
    rw [mem_squashErrors_go_ok _ t.get]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · cases h
      · exact h

theorem mem_squashErrors_ok {α : Type} {a : α} (l : LazyList (Except GenError α)) :
    (.ok a : Except GenError α) ∈ EnumeratorCombinators.squashErrors l ↔ .ok a ∈ l :=
  mem_squashErrors_go_ok none l

/-- Some inconclusive failure is in `l`. -/
def HasInconclusive {α : Type} (l : LazyList (Except GenError α)) : Prop :=
  ∃ e, (.error e : Except GenError α) ∈ l ∧ Gen.GenError.isInconclusive e = true

/-- `pending` only ever holds an inconclusive failure. -/
private def PendingOk (p : Option GenError) : Prop := ∀ e, p = some e → Gen.GenError.isInconclusive e = true

private theorem squash_go_errors {α : Type} :
    ∀ (p : Option GenError) (l : LazyList (Except GenError α)), PendingOk p →
      (HasInconclusive (EnumeratorCombinators.squashErrors.go p l) ↔ p.isSome ∨ HasInconclusive l) ∧
      (∀ e, (.error e : Except GenError α) ∈ EnumeratorCombinators.squashErrors.go p l →
        Gen.GenError.isInconclusive e = true)
  | none, .lnil, _ => by
    simp only [EnumeratorCombinators.squashErrors.go, HasInconclusive, Option.isSome_none]
    exact ⟨⟨fun ⟨_, h, _⟩ => absurd h not_mem_lnil, fun h => by
      rcases h with h | ⟨_, h, _⟩
      · cases h
      · exact absurd h not_mem_lnil⟩, fun _ h => absurd h not_mem_lnil⟩
  | some e, .lnil, hp => by
    simp only [EnumeratorCombinators.squashErrors.go, HasInconclusive, Option.isSome_some, true_or,
      iff_true]
    refine ⟨⟨e, LazyList.mem_lcons.2 (Or.inl rfl), hp e rfl⟩, fun e' h => ?_⟩
    rcases LazyList.mem_lcons.1 h with h | h
    · cases h; exact hp e rfl
    · exact absurd h not_mem_lnil
  | p, .lcons (.ok b) t, hp => by
    obtain ⟨ih1, ih2⟩ := squash_go_errors p t.get hp
    simp only [EnumeratorCombinators.squashErrors.go, HasInconclusive] at ih1 ih2 ⊢
    refine ⟨?_, fun e h => ?_⟩
    · constructor
      · rintro ⟨e, h, hi⟩
        rcases LazyList.mem_lcons.1 h with h | h
        · cases h
        · rcases ih1.1 ⟨e, h, hi⟩ with h | ⟨e', h', hi'⟩
          · exact Or.inl h
          · exact Or.inr ⟨e', LazyList.mem_lcons.2 (Or.inr h'), hi'⟩
      · rintro (h | ⟨e, h, hi⟩)
        · obtain ⟨e, h, hi⟩ := ih1.2 (Or.inl h)
          exact ⟨e, LazyList.mem_lcons.2 (Or.inr h), hi⟩
        · rcases LazyList.mem_lcons.1 h with h | h
          · cases h
          · obtain ⟨e, h, hi⟩ := ih1.2 (Or.inr ⟨e, h, hi⟩)
            exact ⟨e, LazyList.mem_lcons.2 (Or.inr h), hi⟩
    · rcases LazyList.mem_lcons.1 h with h | h
      · cases h
      · exact ih2 e h
  | p, .lcons (.error e) t, hp => by
    let p' := if p.isNone && Gen.GenError.isInconclusive e then some e else p
    have hp' : PendingOk p' := by
      intro e' h'
      by_cases hc : (p.isNone && Gen.GenError.isInconclusive e) = true
      · simp only [p', hc, if_true, Option.some.injEq] at h'
        subst h'; simp only [Bool.and_eq_true] at hc; exact hc.2
      · simp only [p', hc] at h'; exact hp e' h'
    obtain ⟨ih1, ih2⟩ := squash_go_errors p' t.get hp'
    simp only [EnumeratorCombinators.squashErrors.go]
    refine ⟨?_, ih2⟩
    rw [ih1]
    simp only [HasInconclusive]
    constructor
    · rintro (h | ⟨e', h, hi⟩)
      · by_cases hc : (p.isNone && Gen.GenError.isInconclusive e) = true
        · simp only [Bool.and_eq_true] at hc
          exact Or.inr ⟨e, LazyList.mem_lcons.2 (Or.inl rfl), hc.2⟩
        · simp only [p', hc] at h; exact Or.inl h
      · exact Or.inr ⟨e', LazyList.mem_lcons.2 (Or.inr h), hi⟩
    · rintro (h | ⟨e', h, hi⟩)
      · left
        cases p with
        | none => simp at h
        | some _ => simp [p']
      · rcases LazyList.mem_lcons.1 h with h | h
        · cases h
          cases p with
          | none => left; simp [p', hi]
          | some _ => left; simp [p']
        · exact Or.inr ⟨e', h, hi⟩

/-- An inconclusive failure survives squashing iff there was one. -/
theorem hasInconclusive_squashErrors {α : Type} (l : LazyList (Except GenError α)) :
    HasInconclusive (EnumeratorCombinators.squashErrors l) ↔ HasInconclusive l := by
  have := (squash_go_errors none l (fun _ h => by cases h)).1
  unfold EnumeratorCombinators.squashErrors
  simpa using this

/-- Squashing introduces no failure that is not inconclusive. -/
theorem inconclusive_of_mem_squashErrors {α : Type} {l : LazyList (Except GenError α)} {e : GenError}
    (h : (.error e : Except GenError α) ∈ EnumeratorCombinators.squashErrors l) :
    Gen.GenError.isInconclusive e = true :=
  (squash_go_errors none l (fun _ h => by cases h)).2 e h

/-- A **value** is enumerated iff some branch enumerates it. The law for `enumerateAll` restricted to
    values: `enumerate` squashes failures, so it no longer holds for `.error` entries — those are governed
    by `hasInconclusive_squashErrors` instead. -/
theorem mem_enumerate {α : Type} {a : α} (fuel : Nat)
    (es : List (ExceptT GenError Enumerator α)) :
    (.ok a : Except GenError α) ∈ EnumeratorCombinators.enumerate es fuel ↔ ∃ e ∈ es, .ok a ∈ e fuel := by
  show _ ∈ EnumeratorCombinators.squashErrors _ ↔ _
  rw [mem_squashErrors_ok]
  exact mem_enumerateAll fuel es

end Specimen.Correctness

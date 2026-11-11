import Specimen.Correctness.SearchFinds

/-!
# A search finds what its generator produces

The converse of `SearchFinds`, for a checker's *completeness*: a checker that searches for a witness
(`Specimen.CheckerSearch`) answers yes when one exists only if its enumerator's search reaches it.

`SearchHits g x`: whenever the generator `g` (the derived code at `SGen`) produces a value the
continuation answers `yes` of, the search `x` (the same code at `Search`) answers `yes`. That needs
nothing of the search's other branches: `Search`'s disjunction is parallel or, so a `yes` is not
hidden by a branch that has not finished. It is a `GenRel` (with `SGen` on the left, so a generator
that never finishes relates to every search), and `walk` proves it of a derived enumerator by
induction on its fuel, as it does `SearchFinds`.
-/

open Lean.Order Basalt Specimen

namespace Specimen.Correctness

variable {α β : Type}

/-- Answered `yes`. -/
def IsYes (v : Verdict) : Prop := v = .yes

namespace IsYes

theorem yes : IsYes .yes := rfl

theorem orElse_left {a : Verdict} {b : Unit → Verdict} (h : IsYes a) : IsYes (Verdict.orElse a b) := by
  unfold IsYes at *; subst h; rfl

/-- Parallel or: a `yes` on the right is one of the whole, whatever the left. -/
theorem orElse_right {a : Verdict} {b : Unit → Verdict} (h : IsYes (b ())) :
    IsYes (Verdict.orElse a b) := by
  unfold IsYes at *; cases a <;> simp only [Verdict.orElse, h]

theorem any : ∀ {l : List (Unit → Verdict)} {t : Unit → Verdict}, t ∈ l → IsYes (t ()) →
    IsYes (Verdict.any l)
  | [], _, ht, _ => by simp at ht
  | s :: ts, t, ht, h => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact orElse_left h
    · exact orElse_right (any ht h)

end IsYes

/-- Whenever the generator produces a value the continuation answers `yes` of, the search answers
`yes`. -/
def SearchHits (g : SGen α) (x : Search α) : Prop :=
  ∀ (k : α → Verdict) (a : α), Produces g a → IsYes (k a) → IsYes (x.run k)

namespace SearchHits

theorem pure (a : α) : SearchHits (Pure.pure a : SGen α) (Pure.pure a : Search α) := fun k b hb h => by
  rw [produces_pure_iff.mp hb] at h; exact h

theorem bind {g : SGen α} {x : Search α} {k' : α → SGen β} {k : α → Search β}
    (hk : ∀ a, SearchHits (k' a) (k a)) (hx : SearchHits g x) :
    SearchHits (g >>= k') (x >>= k) := fun c b hb h => by
  obtain ⟨a, ha, hb⟩ := produces_bind hb
  exact hx (fun a => (k a).run c) a ha (hk a c b hb h)

theorem map {g : SGen α} {x : Search α} (f : α → β) (hx : SearchHits g x) :
    SearchHits (f <$> g) (f <$> x) := by
  have e : (f <$> g : SGen β) = g >>= fun a => Pure.pure (f a) := by
    rw [← bind_pure_comp]
  rw [e]
  exact bind (k := fun a => Pure.pure (f a)) (fun a => pure (f a)) hx

theorem not_produces_default (a : α) :
    ¬ Produces (@Inhabited.default (SGen α) (instInhabitedOfGen α)) a := by
  intro h
  have e : (@Inhabited.default (SGen α) (instInhabitedOfGen α)).run.run =
      (Pure.pure none : SPMF (Option (Except Exhaustion α))) := rfl
  unfold Produces at h; rw [e, SPMF.mem_support_pure_iff] at h; cases h

theorem default (x : Search α) : SearchHits (@Inhabited.default (SGen α) (instInhabitedOfGen α)) x :=
  fun _ a ha _ => absurd ha (not_produces_default a)

theorem choose (lo hi : Nat) (h : lo ≤ hi) :
    SearchHits (RandomChoice.choose lo hi h : SGen _) (RandomChoice.choose lo hi h : Search _) :=
  fun k a _ hk => by
    show IsYes (Verdict.any (List.ofFn fun (i : Fin (hi - lo + 1)) _ =>
      k (.up ⟨lo + i.val, by have := i.isLt; omega⟩)))
    obtain ⟨⟨v, hv1, hv2⟩⟩ := a
    refine IsYes.any (List.mem_ofFn.mpr ⟨⟨v - lo, by omega⟩, rfl⟩) ?_
    have : (⟨lo + (v - lo), by omega⟩ : {x : Nat // lo ≤ x ∧ x ≤ hi}) = ⟨v, hv1, hv2⟩ :=
      Subtype.ext (by simp only; omega)
    simp only [this]; exact hk

theorem admissible (x : Search α) : Lean.Order.admissible fun g : SGen α => SearchHits g x := by
  intro c hc hall k a ha hk
  have ha' : some (Except.ok a) ∈ SPMF.support (CCPO.csup (α := SPMF (Option (Except Exhaustion α))) hc) := ha
  obtain ⟨g, hg, hga⟩ := (SPMF.mem_support_csup_iff hc).mp ha'
  exact hall g hg k a hga hk

theorem fail : SearchHits (Fail.fail : SGen α) (Fail.fail : Search α) :=
  fun _ a ha _ => absurd ha (not_produces_refute a)

theorem failWith (e : Exhaustion) :
    SearchHits (FailWith.failWith e : SGen α) (FailWith.failWith e : Search α) := fun _ a ha _ => by
  simp [Produces, FailWith.failWith, OptionT.run_pure] at ha

theorem seq {f' : SGen (α → β)} {f : Search (α → β)} {g : SGen α} {x : Search α}
    (hf : SearchHits f' f) (hx : SearchHits g x) : SearchHits (f' <*> g) (f <*> x) := by
  have e₁ : (f <*> x : Search β) = f >>= fun h => h <$> x := rfl
  have e₂ : (f' <*> g : SGen β) = f' >>= fun h => h <$> g := by rw [seq_eq_bind_map]
  rw [e₁, e₂]
  exact bind (fun h => map h hx) hf

end SearchHits

@[walk_rel]
theorem genRel_searchHits : GenRel SGen Search @SearchHits where
  pure := SearchHits.pure
  bind := SearchHits.bind
  map := SearchHits.map
  default := SearchHits.default
  choose := SearchHits.choose
  admissible := SearchHits.admissible

attribute [gen_rule] SearchHits.fail SearchHits.failWith SearchHits.seq

namespace SearchHits

/-- A branch of positive weight of the generator, and its partner at the search. -/
theorem weighted_mem {gs' : List (Nat × (Unit → SGen α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted @SearchHits gs' gs) {p : Nat × (Unit → SGen α)} (hp : p ∈ gs') :
    ∃ q ∈ gs, q.1 = p.1 ∧ SearchHits (p.2 ()) (q.2 ()) := by
  induction hs with
  | nil => simp at hp
  | @cons w g' g gs' gs hg _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(w, g), List.mem_cons_self, rfl, hg⟩
    · obtain ⟨q, hq, hw, h⟩ := ih hp
      exact ⟨q, List.mem_cons_of_mem _ hq, hw, h⟩

theorem branches_of {gs' : List (Nat × (Unit → SGen α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted @SearchHits gs' gs) {k : α → Verdict} {a : α}
    (h : ∃ p ∈ gs', 0 < p.1 ∧ Produces (p.2 ()) a) (hk : IsYes (k a)) :
    IsYes ((Search.branches gs).run k) := by
  obtain ⟨p, hp, hw, ha⟩ := h
  obtain ⟨q, hq, hqw, hpq⟩ := weighted_mem hs hp
  refine IsYes.any (t := fun _ => (q.2 ()).1 k) (List.mem_map.mpr ⟨q, ?_, rfl⟩) (hpq k a ha hk)
  exact List.mem_filter.mpr ⟨hq, by simp; omega⟩

/-- The generator's search draws a branch of positive weight; the search tries them all, in order. -/
@[gen_rule]
theorem backtrack {gs' : List (Nat × (Unit → SGen α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted @SearchHits gs' gs) :
    SearchHits (Backtrack.backtrack gs' : SGen α) (Backtrack.backtrack gs : Search α) := fun k a ha hk =>
  branches_of hs ((produces_backtrack_iff gs' a).mp ha) hk

@[gen_rule]
theorem pick {gs' : List (Nat × (Unit → SGen α))} {gs : List (Nat × (Unit → Search α))}
    (hs : GenRel.Weighted @SearchHits gs' gs) {h' : 0 < Backtrack.sumWeights gs'}
    {h : 0 < Backtrack.sumWeights gs} :
    SearchHits (Pick.pick gs' h' : SGen α) (Pick.pick gs h : Search α) := fun k a ha hk =>
  branches_of hs (Specimen.Backtrack.mem_support_searchWith_ok 1 gs' none a ha) hk

end SearchHits

/-- A search that hits finds: the checker's answer is `yes`. -/
theorem search_yes {g : SGen α} {x : Search α} (hh : SearchHits g x)
    {k : α → Except Plausible.GenError Bool} {a : α} (ha : Produces g a) (hk : k a = .ok true) :
    (x.run (Verdict.ofCheck ∘ k)).toCheck = .ok true := by
  have hy : IsYes ((Verdict.ofCheck ∘ k) a) := by simp only [IsYes, Function.comp, hk]; rfl
  rw [hh _ a ha hy]; rfl

end Specimen.Correctness

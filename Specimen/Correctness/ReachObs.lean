import Specimen.Correctness.SuccObs

/-!
# The reach observation

Completeness is about what a generator *can* succeed with: `∃ x, Produces g x ∧ Q x`. That is the
angelic counterpart of `succObs`, and like it a monad morphism into Basalt's specifications, so
Basalt's own rules for `pure`, `bind`, `map` and `if` apply, and its walk computes the angelic
precondition: a disjunction over a search's live branches, an existential over each draw. What the
walk leaves is the choices: which branch, which draw.
-/

open Basalt Basalt.Walk RandomChoice

namespace Specimen.Correctness

variable {α : Type}

/-- Some success satisfies the postcondition. -/
def reachObs : Obs SGen (WP Mix.angelic) where
  spec g := fun Q => ∃ x, Produces g x ∧ Q x
  map_pure a := by
    funext Q; apply propext
    exact ⟨fun ⟨b, hb, hq⟩ => produces_pure_iff.mp hb ▸ hq, fun h => ⟨a, produces_pure_iff.mpr rfl, h⟩⟩
  map_bind x k := by
    funext Q; apply propext
    show (∃ b, Produces (x >>= k) b ∧ Q b) ↔ ∃ a, Produces x a ∧ ∃ b, Produces (k a) b ∧ Q b
    simp only [produces_bind_iff]
    exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hq⟩ => ⟨a, ha, b, hb, hq⟩, fun ⟨a, ha, b, hb, hq⟩ => ⟨b, ⟨a, ha, hb⟩, hq⟩⟩
  map_choose lo hi h := by
    funext Q; apply propext
    exact ⟨fun ⟨x, _, hq⟩ => ⟨x, hq⟩, fun ⟨x, hq⟩ => ⟨x, produces_choose lo hi h x, hq⟩⟩

instance : reachObs.Monotone := ⟨fun _ _ _ h ⟨a, ha, hp⟩ => ⟨a, ha, h a hp⟩⟩

theorem reachObs_iff {g : SGen α} {P : α → Prop} : reachObs.spec g P ↔ ∃ x, Produces g x ∧ P x :=
  Iff.rfl

theorem produces_of_reach {g : SGen α} {v : α} (h : reachObs.spec g (· = v)) : Produces g v := by
  obtain ⟨x, hx, rfl⟩ := h; exact hx

theorem reach_of_produces {g : SGen α} {v : α} (h : Produces g v) : reachObs.spec g (· = v) :=
  ⟨v, h, rfl⟩

/-- A fact that a sub-generator produces a value, under the postcondition the walk arrives with. Not a
walk leaf: the walk leaves what a sub-generator produces to choose (`le_reach_self`), and the closing
search picks it from the facts. -/
theorem le_reach_of_produces {x : SGen α} {v : α} {p : α → Prop} (hx : Produces x v) :
    p v ≤ reachObs.spec x p := fun h => ⟨v, hx, h⟩

/-- A sub-generator the walk does not enter: what it produces is left to choose, `∃ v, Produces x v ∧
p v`, for the closing search to supply from the facts. -/
@[obs_leaf self]
theorem le_reach_self {x : SGen α} {p : α → Prop} : (∃ v, Produces x v ∧ p v) ≤ reachObs.spec x p :=
  id

/-! ## The sampler's combinators -/

theorem reach_backtrack_of {gs : List (Nat × (Unit → SGen α))} {post : α → Prop}
    {p : Nat × (Unit → SGen α)} (hp : p ∈ gs) (hw : 0 < p.1) (h : reachObs.spec (p.2 ()) post) :
    reachObs.spec (Specimen.Backtrack.backtrack gs) post := by
  obtain ⟨x, hx, hq⟩ := h
  exact ⟨x, (produces_backtrack_iff gs x).mpr ⟨p, hp, hw, hx⟩, hq⟩

theorem anyLive_of_foldr {β : Type} : ∀ {gs : List (Nat × β)} {cs : List Prop},
    (List.zipWith (fun p c => 0 < p.1 ∧ c) gs cs).foldr Or False → AnyLive gs cs
  | _ :: _, _ :: _, .inl h => .inl h
  | _ :: _, _ :: _, .inr h => .inr (anyLive_of_foldr h)

theorem anyLiveOpt_of_foldr {β : Type} : ∀ {os : List (Option (Nat × β))} {cs : List Prop},
    (List.zipWith (fun o c => ∃ q, o = some q ∧ 0 < q.1 ∧ c) os cs).foldr Or False → AnyLiveOpt os cs
  | _ :: _, _ :: _, .inl h => .inl h
  | _ :: _, _ :: _, .inr h => .inr (anyLiveOpt_of_foldr h)

/-- A search reaches what one of its live branches does: the walk's precondition is the disjunction
over them, which it prunes of the refuted and the dead. -/
@[gen_rule]
theorem le_reach_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen α)))}
    {post : α → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c o => c ≤ reachObs.spec (optGen o) post) cs os) :
    (List.zipWith (fun o c => ∃ q, o = some q ∧ 0 < q.1 ∧ c) os cs).foldr Or False ≤
      reachObs.spec (Specimen.Backtrack.backtrack (os.filterMap fun o => o)) post := by
  intro hl
  have h' : List.Forall₂ (fun c o => ∀ q, o = some q →
      c ≤ (fun g : Unit → SGen α => reachObs.spec (g ()) post) q.2) cs os :=
    h.imp fun {c o} hc q hq => by subst hq; exact hc
  obtain ⟨q, hq, hw, hF⟩ := anyLiveOpt_elim (F := fun g : Unit → SGen α => reachObs.spec (g ()) post) h'
    (anyLiveOpt_of_foldr hl)
  exact reach_backtrack_of (mem_filterMap_id.mpr hq) hw hF

@[gen_rule]
theorem le_reach_backtrack {gs : List (Nat × (Unit → SGen α))} {post : α → Prop} {cs : List Prop}
    (h : List.Forall₂ (fun c p => c ≤ reachObs.spec (p.2 ()) post) cs gs) :
    (List.zipWith (fun p c => 0 < p.1 ∧ c) gs cs).foldr Or False ≤
      reachObs.spec (Specimen.Backtrack.backtrack gs) post := by
  intro hl
  obtain ⟨p, hp, hw, hF⟩ := anyLive_elim (F := fun g => reachObs.spec (g ()) post) h (anyLive_of_foldr hl)
  exact reach_backtrack_of hp hw hF

@[gen_rule]
theorem le_reach_optGen_some {q : Nat × (Unit → SGen α)} {post : α → Prop} {c : Prop}
    (h : c ≤ reachObs.spec (q.2 ()) post) : c ≤ reachObs.spec (optGen (some q)) post := h

@[gen_rule]
theorem le_reach_optGen_ite {b : Prop} [Decidable b] {q : Nat × (Unit → SGen α)} {post : α → Prop}
    {c : Prop} (h : b → c ≤ reachObs.spec (q.2 ()) post) :
    (b ∧ c) ≤ reachObs.spec (optGen (if b then some q else none)) post := by
  rintro ⟨hb, hc⟩
  simp only [hb, ite_true, optGen]
  exact h hb hc

@[gen_rule]
theorem le_reach_fail {post : α → Prop} : False ≤ reachObs.spec (Specimen.Fail.fail : SGen α) post :=
  False.elim

@[gen_rule]
theorem le_reach_failWith {e : Exhaustion} {post : α → Prop} :
    False ≤ reachObs.spec (Specimen.FailWith.failWith e : SGen α) post := False.elim

@[gen_rule]
theorem le_reach_truncations {ls : List (Specimen.Label α)} {post : α → Prop} :
    False ≤ reachObs.spec (Specimen.truncations ls : SGen α) post := False.elim

/-- A size split is not entered: which split is left to choose. -/
@[gen_rule]
theorem le_reach_drawEven {k f s : Nat} {post : List Nat → Prop} :
    (∃ parts, Produces (Specimen.SizeSplit.drawEven k f s : SGen (List Nat)) parts ∧ post parts) ≤
      reachObs.spec (Specimen.SizeSplit.drawEven k f s : SGen (List Nat)) post := id

@[gen_rule]
theorem le_reach_draw {fs : List Nat} {s : Nat} {post : List Nat → Prop} :
    (∃ parts, Produces (Specimen.SizeSplit.draw fs s : SGen (List Nat)) parts ∧ post parts) ≤
      reachObs.spec (Specimen.SizeSplit.draw fs s : SGen (List Nat)) post := id

/-! ## Outputs determined by an equation -/

theorem reach_gen_eqRight {α : Type} (val : α) (s l : Nat) :
    Produces (BacktrackGenFor.gen (P := fun x => x = val) (G := SGen) s l) val :=
  produces_pure_iff.mpr rfl

theorem reach_gen_eqLeft {α : Type} (val : α) (s l : Nat) :
    Produces (BacktrackGenFor.gen (P := fun x => val = x) (G := SGen) s l) val :=
  produces_pure_iff.mpr rfl

end Specimen.Correctness

namespace Specimen.Correctness

variable {α : Type}

/-- `frequency` can produce what its live branches can. -/
theorem reach_frequency {gs : List (Nat × (Unit → SGen α))} (h : 0 < (gs.map Prod.fst).sum)
    {Q : α → Prop} :
    reachObs.spec (frequency gs h) Q ↔ ∃ p ∈ gs, 0 < p.1 ∧ reachObs.spec (p.2 ()) Q := by
  rw [reachObs.map_frequency]
  simp only [Obs.select, WP.choose_bind_apply, Obs.selectD_map (fun w : WP Mix.angelic α => w Q), List.map_map]
  refine (Mix.select_angelic _ (by simp [Function.comp_def]) h _).trans ?_
  constructor
  · rintro ⟨_, hp, hw, ha⟩
    obtain ⟨⟨w, g⟩, hmem, rfl⟩ := List.mem_map.mp hp
    exact ⟨(w, g), hmem, hw, ha⟩
  · rintro ⟨⟨w, g⟩, hmem, hw, ha⟩
    exact ⟨_, List.mem_map.mpr ⟨(w, g), hmem, rfl⟩, hw, ha⟩

/-! ## The size split can draw every split that meets the floors -/

open Specimen.SizeSplit in
theorem produces_uniform : ∀ (k r : Nat) (q : List Nat), q.length = k + 1 → q.sum = r →
    Produces (uniform (k + 1) r : SGen (List Nat)) q
  | 0, r, q, hl, hs => by
    match q, hl with
    | [x], _ => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; subst hs; exact produces_pure_iff.mpr rfl
  | k + 1, r, q, hl, hs => by
    match q, hl with
    | j :: q', hl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.sum_cons] at hs
      show Produces (do
        let j ← frequency ((List.range (r + 1)).map fun j => (count (r - j) k, fun _ => pure j))
          (weights_pos k r)
        let rest ← uniform (k + 1) (r - j)
        pure (j :: rest) : SGen (List Nat)) (j :: q')
      refine produces_bind_of (a := j) ?_ (produces_bind_of (a := q') ?_ (produces_pure_iff.mpr rfl))
      · refine produces_of_reach ((reach_frequency _).mpr ⟨(count (r - j) k, fun _ => pure j), ?_, count_pos _ _,
          reach_of_produces (produces_pure_iff.mpr rfl)⟩)
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
      · exact produces_uniform k (r - j) q' hl (by omega)

theorem forall₂_le_sum {f q : List Nat} (h : List.Forall₂ (· ≤ ·) f q) : f.sum ≤ q.sum := by
  induction h with
  | nil => exact Nat.le_refl 0
  | cons hab _ ih => simp only [List.sum_cons]; omega

theorem forall₂_le_parts {f q : List Nat} (h : List.Forall₂ (· ≤ ·) f q) :
    (List.zipWith (· - ·) q f).length = f.length ∧
      (List.zipWith (· - ·) q f).sum + f.sum = q.sum ∧
      List.zipWith (· + ·) (List.zipWith (· - ·) q f) f = q := by
  induction h with
  | nil => simp
  | @cons a b _ _ hab _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨by simp [h1], by simp only [List.zipWith_cons_cons, List.sum_cons]; omega, ?_⟩
    simp only [List.zipWith_cons_cons, h3, List.cons.injEq, and_true]; omega

open Specimen.SizeSplit in
/-- **Every split that meets the floors can be drawn.** -/
theorem produces_draw {floors q : List Nat} {total : Nat} (hf : List.Forall₂ (· ≤ ·) floors q)
    (hs : q.sum = total) : Produces (draw floors total : SGen (List Nat)) q := by
  have hle : floors.sum ≤ total := hs ▸ forall₂_le_sum hf
  obtain ⟨h1, h2, h3⟩ := forall₂_le_parts hf
  unfold draw
  simp only [hle, ↓reduceIte]
  refine produces_bind_of (a := List.zipWith (· - ·) q floors) ?_ (produces_pure_iff.mpr h3.symm)
  cases hk : floors.length with
  | zero =>
    have : floors = [] := List.eq_nil_of_length_eq_zero hk
    subst this
    have : q = [] := by cases hf; rfl
    subst this
    exact produces_pure_iff.mpr rfl
  | succ k => exact produces_uniform k _ _ (h1.trans hk) (by omega)

theorem forall₂_replicate_le {c : Nat} : ∀ {q : List Nat}, (∀ x ∈ q, c ≤ x) →
    List.Forall₂ (· ≤ ·) (List.replicate q.length c) q
  | [], _ => .nil
  | x :: q, h => .cons (h x List.mem_cons_self) (forall₂_replicate_le fun y hy => h y (List.mem_cons_of_mem _ hy))

open Specimen.SizeSplit in
theorem produces_drawEven {k floor total : Nat} {q : List Nat} (hl : q.length = k)
    (hf : ∀ x ∈ q, total / k * min floor 1000 / 1000 ≤ x) (hs : q.sum = total) :
    Produces (drawEven k floor total : SGen (List Nat)) q := by
  refine produces_draw ?_ hs
  subst hl
  exact forall₂_replicate_le hf

end Specimen.Correctness

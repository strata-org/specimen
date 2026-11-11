import Specimen.Correctness.ReachClose
import Specimen.Debug

/-!
# What a size split draws

Every split the drawing can produce has one part per call and adds up to at most the size: exactly
the size where the floors fit, each part then at least its floor.
-/

namespace Specimen.Correctness

open Specimen.SizeSplit Basalt

theorem produces_of_frequency {α : Type} {gs : List (Nat × (Unit → SGen α))} {h} {x : α}
    (hx : Produces (frequency gs h) x) : ∃ p ∈ gs, 0 < p.1 ∧ Produces (p.2 ()) x := by
  obtain ⟨p, hp, hw, hr⟩ := (reach_frequency h).mp (reach_of_produces hx)
  exact ⟨p, hp, hw, produces_of_reach hr⟩

theorem uniform_parts : ∀ (k r : Nat) (ps : List Nat), Produces (uniform (k + 1) r : SGen (List Nat)) ps →
    ps.length = k + 1 ∧ ps.sum = r
  | 0, r, ps, h => by
    have := produces_pure_iff.mp h; subst this; simp
  | k + 1, r, ps, h => by
    obtain ⟨j, hj, h⟩ := produces_bind_iff.mp h
    obtain ⟨rest, hrest, h⟩ := produces_bind_iff.mp h
    have := produces_pure_iff.mp h; subst this
    obtain ⟨p, hp, -, hpj⟩ := produces_of_frequency hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := produces_pure_iff.mp hpj; subst this
    have hi := List.mem_range.mp hi
    obtain ⟨h1, h2⟩ := uniform_parts k (r - j) rest hrest
    exact ⟨by simp [h1], by simp only [List.sum_cons, h2]; omega⟩

theorem greedy_parts : ∀ (fs : List Nat) (t : Nat), (greedy fs t).length = fs.length ∧ (greedy fs t).sum ≤ t
  | [], _ => by simp [greedy]
  | f :: fs, t => by
    obtain ⟨h1, h2⟩ := greedy_parts fs (t - min f t)
    simp only [greedy, List.length_cons, h1, List.sum_cons, true_and]
    omega

theorem zipWith_add_parts : ∀ (ps fs : List Nat), ps.length = fs.length →
    (List.zipWith (· + ·) ps fs).length = fs.length ∧
      (List.zipWith (· + ·) ps fs).sum = ps.sum + fs.sum ∧
      List.Forall₂ (· ≤ ·) fs (List.zipWith (· + ·) ps fs)
  | [], [], _ => by simp
  | p :: ps, f :: fs, h => by
    obtain ⟨h1, h2, h3⟩ := zipWith_add_parts ps fs (by simpa using h)
    refine ⟨by simp [h1], by simp only [List.zipWith_cons_cons, List.sum_cons, h2]; omega,
      .cons (Nat.le_add_left _ _) h3⟩

/-- **What a split draws.** One part per call, adding up to at most the size; where the floors fit,
exactly the size, each part at least its floor. -/
theorem draw_parts {fs : List Nat} {total : Nat} {ps : List Nat}
    (h : Produces (draw fs total : SGen (List Nat)) ps) :
    ps.length = fs.length ∧ ps.sum ≤ total ∧ (fs.sum ≤ total → List.Forall₂ (· ≤ ·) fs ps) := by
  unfold draw at h
  split at h
  · rename_i hle
    obtain ⟨us, hus, h⟩ := produces_bind_iff.mp h
    have := produces_pure_iff.mp h; subst this
    cases hk : fs.length with
    | zero =>
      have : fs = [] := List.eq_nil_of_length_eq_zero hk
      subst this
      exact ⟨by simp, by simp, fun _ => by simp⟩
    | succ k =>
      rw [hk] at hus
      obtain ⟨hl, hs⟩ := uniform_parts k _ us hus
      obtain ⟨h1, h2, h3⟩ := zipWith_add_parts us fs (hl.trans hk.symm)
      exact ⟨h1.trans hk, by omega, fun _ => h3⟩
  · rename_i hgt
    have := produces_pure_iff.mp h; subst this
    obtain ⟨h1, h2⟩ := greedy_parts fs total
    exact ⟨h1, h2, fun h => absurd h hgt⟩

/-- The split, for the soundness walk: what it draws, as `draw_parts` says. -/
@[gen_rule]
theorem le_succ_draw {fs : List Nat} {total : Nat} {post : List Nat → Prop} :
    (∀ ps, ps.length = fs.length → ps.sum ≤ total → (fs.sum ≤ total → List.Forall₂ (· ≤ ·) fs ps) →
      post ps) ≤ succObs.spec (draw fs total : SGen (List Nat)) post := fun h ps hps =>
  let ⟨h1, h2, h3⟩ := draw_parts hps
  h ps h1 h2 h3

end Specimen.Correctness

/-! ## A split that meets every call's need -/

namespace Specimen.Correctness

open Specimen.SizeSplit

theorem fill_sum : ∀ (ps : List Nat) (r : Nat), ps ≠ [] → (fill ps r).sum = ps.sum + r
  | [], _, h => absurd rfl h
  | [p], r, _ => by simp [fill]
  | p :: q :: ps, r, _ => by
    simp only [fill, List.sum_cons]
    have := fill_sum (q :: ps) r (by simp)
    simp only [List.sum_cons] at this
    omega

theorem fill_ge : ∀ (ps : List Nat) (r : Nat), List.Forall₂ (· ≤ ·) ps (fill ps r)
  | [], _ => .nil
  | [p], r => .cons (Nat.le_add_right _ _) .nil
  | p :: q :: ps, r => .cons (Nat.le_refl _) (fill_ge (q :: ps) r)

theorem forall₂_le_trans : ∀ {as bs cs : List Nat}, List.Forall₂ (· ≤ ·) as bs →
    List.Forall₂ (· ≤ ·) bs cs → List.Forall₂ (· ≤ ·) as cs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => .cons (Nat.le_trans h₁ h₂) (forall₂_le_trans t₁ t₂)

theorem forall₂_le_max_left : ∀ (fs ts : List Nat), fs.length = ts.length →
    List.Forall₂ (· ≤ ·) fs (List.zipWith max fs ts)
  | [], [], _ => .nil
  | f :: fs, t :: ts, h => .cons (Nat.le_max_left _ _) (forall₂_le_max_left fs ts (by simpa using h))

theorem zipWith_ne_nil {fs ts : List Nat} (hf : fs ≠ []) (h : fs.length = ts.length) :
    List.zipWith max fs ts ≠ [] := by
  cases fs with
  | nil => exact absurd rfl hf
  | cons f fs => cases ts with
    | nil => simp at h
    | cons t ts => simp

/-- **The split can give every call its floor and its need.** -/
theorem produces_draw_fill {fs ts : List Nat} {s : Nat} (hf : fs ≠ []) (hl : fs.length = ts.length)
    (hs : (List.zipWith max fs ts).sum ≤ s) :
    Produces (draw fs s : SGen (List Nat)) (fillParts fs ts s) := by
  refine produces_draw (forall₂_le_trans (forall₂_le_max_left fs ts hl) (fill_ge _ _)) ?_
  rw [fillParts, fill_sum _ _ (zipWith_ne_nil hf hl)]
  omega

theorem le_getD_fill : ∀ (ps : List Nat) (r i : Nat), ps.getD i 0 ≤ (fill ps r).getD i 0
  | [], _, _ => by simp [fill]
  | [p], r, 0 => by simp [fill]
  | [p], r, i + 1 => by simp [fill]
  | p :: q :: ps, r, 0 => by simp [fill]
  | p :: q :: ps, r, i + 1 => by simpa [fill] using le_getD_fill (q :: ps) r i

theorem le_getD_zipWith_max : ∀ (fs ts : List Nat) (i : Nat), fs.length = ts.length →
    ts.getD i 0 ≤ (List.zipWith max fs ts).getD i 0
  | [], [], _, _ => by simp
  | f :: fs, t :: ts, 0, _ => by simp
  | f :: fs, t :: ts, i + 1, h => by simpa using le_getD_zipWith_max fs ts i (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- Each call gets at least its need. -/
theorem le_sizeAt_fillParts {fs ts : List Nat} {s : Nat} (i : Nat) (hl : fs.length = ts.length) :
    ts.getD i 0 ≤ sizeAt (fillParts fs ts s) i :=
  Nat.le_trans (le_getD_zipWith_max fs ts i hl) (le_getD_fill _ _ i)

end Specimen.Correctness

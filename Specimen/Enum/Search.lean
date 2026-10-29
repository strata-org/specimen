module

public import Specimen.Enum.Pick
import all Init.Internal.Order.Basic

/-!
# A search that stops at the first success

`Search α` asks of everything an enumeration lists whether one of its values satisfies a
continuation, and stops at the first that does: a checker's question, answered without building the
enumeration first, which `Finite`, a strict reading, has to. Its answer is three-valued, as a
derived checker's is (`Verdict`): found, refuted, or undecided within the budget.

A search is a monotone function of its continuation, so that `bind` is monotone and `Search` is a
`Gen`; `Verdict`'s bottom, `undef`, is a search that has not finished.
-/

@[expose] public section

open Lean.Order

namespace Specimen

/-- What a search finds: a value satisfying its continuation (`yes`), none (`no`), not decided within
its budget (`unknown`), or nothing yet (`undef`, the bottom). -/
inductive Verdict where
  | undef
  | yes
  | no
  | unknown
  deriving DecidableEq, Repr, Inhabited

namespace Verdict

instance instPartialOrder : PartialOrder Verdict := FlatOrder.instOrder (b := .undef)

instance instCCPO : CCPO Verdict := FlatOrder.instCCPO (b := .undef)

theorem eq_undef_or_eq {x y : Verdict} (h : x ⊑ y) : x = .undef ∨ x = y := by
  cases h with
  | bot => exact .inl rfl
  | refl => exact .inr rfl

/-- Kleene disjunction, left to right: `yes` as soon as one side says so, without running the right
side; `undef` as soon as an unfinished side is reached. -/
def orElse : Verdict → (Unit → Verdict) → Verdict
  | .undef, _ => .undef
  | .yes, _ => .yes
  | .no, b => b ()
  | .unknown, b => match b () with
    | .undef => .undef
    | .yes => .yes
    | _ => .unknown

/-- The disjunction of a list, left to right. -/
def any : List (Unit → Verdict) → Verdict
  | [] => .no
  | t :: ts => orElse (t ()) fun _ => any ts

theorem orElse_mono {a₁ a₂ : Verdict} {b₁ b₂ : Unit → Verdict} (ha : a₁ ⊑ a₂) (hb : b₁ () ⊑ b₂ ()) :
    orElse a₁ b₁ ⊑ orElse a₂ b₂ := by
  rcases eq_undef_or_eq ha with rfl | rfl
  · exact FlatOrder.rel.bot
  · rcases eq_undef_or_eq hb with h | h
    · cases a₁ <;> simp only [orElse, h] <;> first | exact FlatOrder.rel.bot | exact FlatOrder.rel.refl
    · cases a₁ <;> simp only [orElse, h] <;> exact FlatOrder.rel.refl

theorem any_map_mono {l : List β} {f g : β → Verdict} (h : ∀ b, f b ⊑ g b) :
    any (l.map fun b _ => f b) ⊑ any (l.map fun b _ => g b) := by
  induction l with
  | nil => exact FlatOrder.rel.refl
  | cons b l ih => exact orElse_mono (h b) ih

theorem any_ofFn_mono {n : Nat} {f g : Fin n → Verdict} (h : ∀ i, f i ⊑ g i) :
    any (List.ofFn fun i _ => f i) ⊑ any (List.ofFn fun i _ => g i) := by
  induction n with
  | zero => exact FlatOrder.rel.refl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact orElse_mono (h 0) (ih fun i => h i.succ)

@[simp] theorem orElse_no (a : Verdict) : orElse a (fun _ => .no) = a := by
  cases a <;> rfl

@[simp] theorem no_orElse (b : Unit → Verdict) : orElse .no b = b () := rfl

theorem orElse_assoc (a : Verdict) (b c : Unit → Verdict) :
    orElse (orElse a b) c = orElse a (fun _ => orElse (b ()) c) := by
  cases a <;> cases hb : b () <;> cases hc : c () <;> simp [orElse, hb, hc]

theorem any_append (l₁ l₂ : List (Unit → Verdict)) :
    any (l₁ ++ l₂) = orElse (any l₁) (fun _ => any l₂) := by
  induction l₁ with
  | nil => rfl
  | cons t l₁ ih => simp only [List.cons_append, any, ih, orElse_assoc]

end Verdict

/-- A search over the values of `α`: given what to ask of a value, the answer for all of them. -/
def Search (α : Type) : Type := { s : (α → Verdict) → Verdict // monotone s }

namespace Search

variable {α β : Type}

/-- Ask `k` of the values `s` lists. -/
def run (s : Search α) (k : α → Verdict) : Verdict := s.1 k

protected def pure (a : α) : Search α := ⟨fun k => k a, fun _ _ h => h a⟩

protected def bind (s : Search α) (f : α → Search β) : Search β :=
  ⟨fun k => s.1 fun a => (f a).1 k, fun _ _ h => s.2 _ _ fun a => (f a).2 _ _ h⟩

instance : Monad Search where
  pure := Search.pure
  bind := Search.bind

/-- `default` is the search that never finishes. -/
instance : Inhabited (Search α) := ⟨⟨fun _ => .undef, monotone_const _⟩⟩

instance instPartialOrder : PartialOrder (Search α) where
  rel s t := s.1 ⊑ t.1
  rel_refl := PartialOrder.rel_refl
  rel_trans h₁ h₂ := PartialOrder.rel_trans h₁ h₂
  rel_antisymm h₁ h₂ := Subtype.ext (PartialOrder.rel_antisymm h₁ h₂)

/-- The supremum of a chain of searches, pointwise, is monotone: each search in it is. -/
theorem csup_monotone {c : ((α → Verdict) → Verdict) → Prop} (hc : chain c)
    (hm : ∀ f, c f → monotone f) : monotone (CCPO.csup hc) := by
  intro k k' hk
  rw [← fun_csup_eq c hc]
  unfold fun_csup
  apply csup_le
  rintro _ ⟨f, hf, rfl⟩
  exact PartialOrder.rel_trans (hm f hf k k' hk) (le_csup _ ⟨f, hf, rfl⟩)

/-- The underlying functions of a chain of searches. -/
def underlying (c : Search α → Prop) : ((α → Verdict) → Verdict) → Prop :=
  fun f => ∃ s, c s ∧ s.1 = f

theorem chain_underlying {c : Search α → Prop} (hc : chain c) : chain (underlying c) := by
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  exact hc s t hs ht

instance instCCPO : CCPO (Search α) where
  has_csup {c} hc := by
    let hc' := chain_underlying hc
    refine ⟨⟨CCPO.csup hc', csup_monotone hc' ?_⟩, fun t => ⟨fun h s hs => ?_, fun h => ?_⟩⟩
    · rintro _ ⟨s, _, rfl⟩
      exact s.2
    · exact PartialOrder.rel_trans (le_csup hc' ⟨s, hs, rfl⟩) h
    · exact csup_le hc' fun _ ⟨s, hs, hsf⟩ => hsf ▸ h s hs

instance : MonoBind Search where
  bind_mono_left {_ _ _ _ f} h k := h fun a => (f a).1 k
  bind_mono_right {_ _ s _ _} h k := s.2 _ _ fun a => h a k

/-- Every value of the range, in increasing order. -/
instance : RandomChoice Search where
  choose lo hi _ := ⟨fun k => Verdict.any (List.ofFn fun (i : Fin (hi - lo + 1)) _ =>
      k (.up ⟨lo + i.val, by have := i.isLt; omega⟩)),
    fun _ _ h => Verdict.any_ofFn_mono fun _ => h _⟩

/-- A refutation: no value. -/
instance : Fail Search := ⟨⟨fun _ => .no, monotone_const _⟩⟩

/-- A labelled failure: undecided. -/
instance : FailWith ε Search := ⟨fun _ => ⟨fun _ => .unknown, monotone_const _⟩⟩

/-- The branches of positive weight, in order, until one succeeds. -/
def branches (gs : List (Nat × (Unit → Search α))) : Search α :=
  ⟨fun k => Verdict.any ((gs.filter (·.1 != 0)).map fun p _ => (p.2 ()).1 k),
    fun _ _ h => Verdict.any_map_mono fun p => (p.2 ()).2 _ _ h⟩

instance : Backtrack Search := ⟨branches⟩

instance : Pick Search := ⟨fun gs _ => branches gs⟩

attribute [local instance] List.instPartialOrderPointwise instPartialOrderConstFst

theorem branches_mono :
    ∀ {gs₁ gs₂ : List (Nat × (Unit → Search α))}, gs₁ ⊑ gs₂ → branches gs₁ ⊑ branches gs₂
  | [], [], _ => PartialOrder.rel_refl
  | [], _ :: _, h | _ :: _, [], h => absurd (Backtrack.length_eq_of_rel h) (by simp)
  | (w₁, g₁) :: gs₁, (w₂, g₂) :: gs₂, h => by
    obtain ⟨⟨hw, hg⟩, ht⟩ := Backtrack.rel_cons_iff.mp h
    simp only at hw
    subst hw
    intro k
    by_cases hw0 : w₁ = 0
    · simpa [branches, hw0] using branches_mono ht k
    · simp only [branches, List.filter_cons, hw0, bne_iff_ne, ne_eq, not_false_eq_true,
        ↓reduceIte, List.map_cons]
      exact Verdict.orElse_mono (hg () k) (branches_mono ht k)

instance : MonoBacktrack Search := ⟨branches_mono⟩

instance : MonoPick Search := ⟨branches_mono⟩

end Search

end Specimen

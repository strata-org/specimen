import Basalt.GradedRun
import SpecimenTest.BasaltPort.GradedStlcTest

/-!
# The ∃-fold: the graded enumeration is adequate for the inductive `typing`

`agreesIx_stlc` relates the enumeration's *value* reading to its *specification* reading. Both are the
same polymorphic body, so that theorem cannot notice an error made identically in both — which is exactly
how the `bindC` incompleteness survived. This file closes that gap by relating the enumeration to Lean's
hand-written `inductive typing`, which owes the enumerator nothing.

Two directions, and they are not symmetric in difficulty:

* **Soundness** — everything enumerated is well typed. Unconditional: no hypothesis about the leaf
  enumerations is needed, because `TConst` accepts *any* numeral and `TAbs` *any* annotation. Proved by
  induction on the iteration count.
* **Completeness** — every well-typed term is enumerated somewhere. Needs the leaves to cover their types
  (`Covers`), and needs monotonicity in the iteration count so that sub-derivations found at different
  budgets can be combined. Proved by induction on the `typing` derivation.

Work is done at `SetE` (the specification carrier) and transported to `Lv` (values) through
`agreesIx_stlc`, so the earlier `Agrees` development is what makes the value-level statement cheap.
-/

open Basalt

/-! ## Soundness -/

/-- Everything the family produces at an index is well typed at that index. -/
def SoundIx (m : TyIx → SetE term) : Prop := ∀ Γ τ n e, m (Γ, τ) n e → typing Γ e τ

theorem lookupEnum_sound (τ : type) : ∀ (Γ : List type) (n x : Nat),
    (lookupEnum Γ τ : SetE Nat) n x → lookup Γ x τ := by
  intro Γ
  induction Γ with
  | nil => intro n x h; exact absurd h (by simp [lookupEnum])
  | cons σ Γ ih =>
    intro n x h
    simp only [lookupEnum, SetE.union_apply] at h
    rcases h with h | h
    · by_cases hst : σ = τ
      · simp only [hst, ↓reduceIte, SetE.single_apply] at h
        obtain ⟨hn, hx⟩ := h
        subst hx; subst hst
        exact lookup.Now _ _
      · simp only [hst, ↓reduceIte] at h
        exact absurd h (by simp)
    · cases n with
      | zero => exact absurd h (by simp)
      | succ n =>
        simp only [SetE.pay_succ, SetE.gmap_apply] at h
        obtain ⟨y, hy, hxy⟩ := h
        subst hxy
        exact lookup.Later τ σ y Γ (ih n y hy)

theorem stlcAFStep_sound {natE : SetE Nat} {rec : TyIx → SetE term} (h : SoundIx rec) :
    SoundIx (stlcAFStep natE rec) := by
  intro Γ τ n e he
  cases τ with
  | Nat =>
    simp only [stlcAFStep, SetE.union_apply, SetE.gmap_apply] at he
    rcases he with ⟨x, hx, hex⟩ | ⟨k, _, hek⟩ | hadd
    · subst hex; exact typing.TVar Γ x .Nat (lookupEnum_sound _ _ _ _ hx)
    · subst hek; exact typing.TConst Γ k
    · cases n with
      | zero => exact absurd hadd (by simp)
      | succ n =>
        simp only [SetE.pay_succ, SetE.gmap_apply, SetE.pair_apply] at hadd
        obtain ⟨p, ⟨i, _, h1, h2⟩, hep⟩ := hadd
        subst hep
        exact typing.TAdd Γ p.1 p.2 (h _ _ _ _ h1) (h _ _ _ _ h2)
  | Fun τ1 τ2 =>
    simp only [stlcAFStep, SetE.union_apply, SetE.gmap_apply] at he
    rcases he with ⟨x, hx, hex⟩ | habs
    · subst hex; exact typing.TVar Γ x (.Fun τ1 τ2) (lookupEnum_sound _ _ _ _ hx)
    · cases n with
      | zero => exact absurd habs (by simp)
      | succ n =>
        simp only [SetE.pay_succ, SetE.gmap_apply] at habs
        obtain ⟨b, hb, heb⟩ := habs
        subst heb
        exact typing.TAbs Γ b τ1 τ2 (h _ _ _ _ hb)

theorem stlcStep_sound {natE : SetE Nat} {typeE : SetE type} {rec : TyIx → SetE term}
    (h : SoundIx rec) : SoundIx (stlcStep natE typeE rec) := by
  intro Γ τ n e he
  simp only [stlcStep, SetE.union_apply] at he
  rcases he with haf | happ
  · exact stlcAFStep_sound h Γ τ n e haf
  · cases n with
    | zero => exact absurd happ (by simp)
    | succ n =>
      simp only [SetE.pay_succ, SetE.bindC_apply, SetE.gmap_apply, SetE.pair_apply] at happ
      obtain ⟨i, _, τ1, _, p, ⟨j, _, h1, h2⟩, hep⟩ := happ
      subst hep
      exact typing.TApp Γ p.1 p.2 τ1 τ (h _ _ _ _ h2) (h _ _ _ _ h1)

/-- **Soundness.** Nothing the enumeration produces is ill typed, at any iteration count, index or level —
and with no assumption whatever on the leaf enumerations. -/
theorem stlc_sound {natE : SetE Nat} {typeE : SetE type} :
    ∀ levels, SoundIx (gradedIterIx (stlcStep natE typeE) levels)
  | 0 => by intro Γ τ n e he; exact absurd he (by simp [gradedIterIx])
  | levels + 1 => stlcStep_sound (stlc_sound levels)

/-! ## Monotonicity in the iteration count

Assembled from the generic `SubE` lemmas. Needed because the completeness proof gets one budget per
premise and must raise them to a common one. -/

theorem stlcAFStep_mono {natE : SetE Nat} (x y : TyIx → SetE term) (h : SubIxE x y) :
    SubIxE (stlcAFStep natE x) (stlcAFStep natE y) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact (SubE.refl _).union ((SubE.refl _).union
      ((((h (Γ, .Nat)).pair (h (Γ, .Nat))).gmap _).pay))
  | Fun τ1 τ2 => exact (SubE.refl _).union (((h (τ1 :: Γ, τ2)).gmap _).pay)

theorem stlcStep_mono {natE : SetE Nat} {typeE : SetE type}
    (x y : TyIx → SetE term) (h : SubIxE x y) :
    SubIxE (stlcStep natE typeE x) (stlcStep natE typeE y) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (stlcAFStep_mono x y h (Γ, τ)).union
    ((SubE.bindC (SubE.refl typeE) fun τ1 =>
      (((h (Γ, .Fun τ1 τ)).pair (h (Γ, τ1))).gmap _)).pay)

theorem stlc_iter_le {natE : SetE Nat} {typeE : SetE type} {m n : Nat} (hmn : m ≤ n) :
    SubIxE (gradedIterIx (stlcStep natE typeE) m) (gradedIterIx (stlcStep natE typeE) n) :=
  subIxE_gradedIterIx_le (fun x y h => stlcStep_mono x y h) hmn

/-! ## Completeness -/

/-- A leaf enumeration that reaches every value of its type at *some* level. -/
def Covers (s : SetE α) : Prop := ∀ a, ∃ n, s n a

theorem lookupEnum_complete : ∀ {Γ : List type} {x : Nat} {τ : type},
    lookup Γ x τ → ∃ n, (lookupEnum Γ τ : SetE Nat) n x := by
  intro Γ x τ h
  induction h with
  | Now σ Γ' =>
    refine ⟨0, ?_⟩
    simp only [lookupEnum, SetE.union_apply]
    exact Or.inl (by simp)
  | Later σ σ' y Γ' _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    simp only [lookupEnum, SetE.union_apply]
    exact Or.inr (by simpa using hk)

/-- **Completeness.** Every well-typed term is enumerated — at some iteration count and some level.

This is the statement `Agrees` structurally could not make: `typing` is hand-written and owes the
enumerator nothing, so a rule mis-graded identically in both carriers shows up here as an unprovable case.
The `bindC` bug fixed earlier is exactly what this rules out. -/
theorem stlc_complete {natE : SetE Nat} {typeE : SetE type}
    (hn : Covers natE) (ht : Covers typeE) :
    ∀ {Γ : List type} {e : term} {τ : type}, typing Γ e τ →
      ∃ levels n, gradedIterIx (stlcStep natE typeE) levels (Γ, τ) n e := by
  intro Γ e τ h
  induction h with
  | TConst Γ k =>
    obtain ⟨m, hm⟩ := hn k
    refine ⟨1, m, ?_⟩
    show stlcStep natE typeE (gradedIterIx _ 0) (Γ, .Nat) m (term.Const k)
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    exact Or.inl (Or.inr (Or.inl ⟨k, hm, rfl⟩))
  | TAdd Γ e1 e2 _ _ ih1 ih2 =>
    obtain ⟨l1, n1, hh1⟩ := ih1
    obtain ⟨l2, n2, hh2⟩ := ih2
    refine ⟨max l1 l2 + 1, n1 + n2 + 1, ?_⟩
    show stlcStep natE typeE (gradedIterIx _ (max l1 l2)) (Γ, .Nat) (n1 + n2 + 1) _
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    refine Or.inl (Or.inr (Or.inr ?_))
    simp only [SetE.pay_succ, SetE.gmap_apply, SetE.pair_apply]
    refine ⟨(e1, e2), ⟨n1, by omega, ?_, ?_⟩, rfl⟩
    · exact stlc_iter_le (Nat.le_max_left _ _) _ _ _ hh1
    · have hsub : n1 + n2 - n1 = n2 := by omega
      rw [hsub]
      exact stlc_iter_le (Nat.le_max_right _ _) _ _ _ hh2
  | TAbs Γ b τ1 τ2 _ ih =>
    obtain ⟨l, n, hh⟩ := ih
    refine ⟨l + 1, n + 1, ?_⟩
    show stlcStep natE typeE (gradedIterIx _ l) (Γ, .Fun τ1 τ2) (n + 1) _
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    exact Or.inl (Or.inr (by simpa using hh))
  | TVar Γ x σ hlk =>
    obtain ⟨m, hm⟩ := lookupEnum_complete hlk
    refine ⟨1, m, ?_⟩
    cases σ with
    | Nat =>
      show stlcStep natE typeE (gradedIterIx _ 0) (Γ, .Nat) m (term.Var x)
      simp only [stlcStep, SetE.union_apply, stlcAFStep]
      exact Or.inl (Or.inl ⟨x, hm, rfl⟩)
    | Fun a b =>
      show stlcStep natE typeE (gradedIterIx _ 0) (Γ, .Fun a b) m (term.Var x)
      simp only [stlcStep, SetE.union_apply, stlcAFStep]
      exact Or.inl (Or.inl ⟨x, hm, rfl⟩)
  | TApp Γ e1 e2 τ1 τ2 _ _ ih2 ih1 =>
    obtain ⟨l2, n2, hh2⟩ := ih2
    obtain ⟨l1, n1, hh1⟩ := ih1
    obtain ⟨k, hk⟩ := ht τ1
    refine ⟨max l1 l2 + 1, k + (n1 + n2) + 1, ?_⟩
    show stlcStep natE typeE (gradedIterIx _ (max l1 l2)) (Γ, τ2) (k + (n1 + n2) + 1) _
    simp only [stlcStep, SetE.union_apply]
    refine Or.inr ?_
    simp only [SetE.pay_succ, SetE.bindC_apply, SetE.gmap_apply, SetE.pair_apply]
    refine ⟨k, by omega, τ1, hk, (e1, e2), ⟨n1, by omega, ?_, ?_⟩, rfl⟩
    · exact stlc_iter_le (Nat.le_max_left _ _) _ _ _ hh1
    · have harith : k + (n1 + n2) - k - n1 = n2 := by omega
      rw [harith]
      exact stlc_iter_le (Nat.le_max_right _ _) _ _ _ hh2

/-! ## The ∃-fold -/

/-- **The adequacy theorem.** The graded enumeration is exactly `typing`, folded over levels: `→` is
completeness, `←` soundness. Stated against the hand-written inductive relation, so unlike `agreesIx_stlc`
it cannot be satisfied by a body that is wrong in both carriers at once. -/
theorem stlc_iff {natE : SetE Nat} {typeE : SetE type}
    (hn : Covers natE) (ht : Covers typeE) (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ levels n, gradedIterIx (stlcStep natE typeE) levels (Γ, τ) n e :=
  ⟨stlc_complete hn ht, fun ⟨levels, n, h⟩ => stlc_sound levels Γ τ n e h⟩

/-! ### A non-vacuous instance

`Covers` fails for any *fixed* budget `gradedIter natStep L` — that only reaches numerals below `L`. The
leaf specifications below are the unbounded limits of those, which is what makes the hypotheses of
`stlc_iff` satisfiable. Threading a leaf budget through the induction, so the statement can be made about
`gradedIter` at a concrete `L`, is bookkeeping this file does not do. -/

/-- `Nat` graded by magnitude — the limit of `gradedIter natStep`. -/
def natSpec : SetE Nat := fun n a => a = n

/-- Number of `Fun` nodes: what `typeStep` charges for a type. -/
def tyCount : type → Nat
  | .Nat => 0
  | .Fun a b => 1 + tyCount a + tyCount b

/-- `type` graded by size — the limit of `gradedIter typeStep`. -/
def typeSpec : SetE type := fun n τ => tyCount τ = n

theorem covers_natSpec : Covers natSpec := fun a => ⟨a, rfl⟩
theorem covers_typeSpec : Covers typeSpec := fun τ => ⟨tyCount τ, rfl⟩

theorem stlc_iff_spec (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ levels n, gradedIterIx (stlcStep natSpec typeSpec) levels (Γ, τ) n e :=
  stlc_iff covers_natSpec covers_typeSpec Γ e τ

/-! ### At the value carrier

This is where the earlier `Agrees` development pays for itself: transporting adequacy from the
specification carrier to the executable one is one rewrite. -/

/-- **Adequacy for the enumeration that actually runs.** `e` is a well-typed term exactly when it appears
in some level of the value enumeration. -/
theorem stlc_mem_iff {natEv : Lv Nat} {typeEv : Lv type} {natE : SetE Nat} {typeE : SetE type}
    (hna : Agrees natEv natE) (hta : Agrees typeEv typeE)
    (hn : Covers natE) (ht : Covers typeE) (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ levels n, e ∈ gradedIterIx (stlcStep natEv typeEv) levels (Γ, τ) n := by
  rw [stlc_iff hn ht Γ e τ]
  exact ⟨fun ⟨l, n, h⟩ => ⟨l, n, (agreesIx_stlc hna hta l (Γ, τ) n e).mpr h⟩,
         fun ⟨l, n, h⟩ => ⟨l, n, (agreesIx_stlc hna hta l (Γ, τ) n e).mp h⟩⟩

/-! ## Adequacy at a concrete leaf budget

`Covers` holds only of the unbounded leaf *limits*, but any run has a finite leaf budget, so the statement
worth having names one. This section replaces the `Covers` hypotheses with concrete `gradedIter` leaves at
an existentially quantified budget — something a caller can actually supply.

The two abbreviations are load-bearing: without them the carrier of `gradedIter natStep L` is ambiguous
(`Lv`, `Cnt` and `SetE` all fit) and elaboration fails with `?m term`. -/

/-- The concrete numeral leaf at budget `L`, read as a specification. -/
abbrev natAt (L : Nat) : SetE Nat := gradedIter natStep L
/-- The concrete type leaf at budget `L`, read as a specification. -/
abbrev tyAt (L : Nat) : SetE type := gradedIter typeStep L

theorem natStep_mono (x y : SetE Nat) (h : SubE x y) : SubE (natStep x) (natStep y) :=
  (SubE.refl _).union ((h.gmap _).pay)

theorem typeStep_mono (x y : SetE type) (h : SubE x y) : SubE (typeStep x) (typeStep y) :=
  (SubE.refl _).union (((h.pair h).gmap _).pay)

theorem natAt_le {L L' : Nat} (h : L ≤ L') : SubE (natAt L) (natAt L') :=
  subE_gradedIter_le natStep_mono h
theorem tyAt_le {L L' : Nat} (h : L ≤ L') : SubE (tyAt L) (tyAt L') :=
  subE_gradedIter_le typeStep_mono h

/-- Every numeral is reached at some budget and level. Stated existentially on purpose: pinning the exact
level forces the `pay` index into `1 + a + b` shape, which `SetE.pay_succ`'s `_ + 1` pattern will not
match, and the exact numbers are not needed downstream. -/
theorem natAt_reaches : ∀ a : Nat, ∃ L n, natAt L n a
  | 0 => ⟨1, 0, by show (natStep (gradedIter natStep 0) : SetE Nat) 0 0
                   simp only [natStep, SetE.union_apply]
                   exact Or.inl (by simp)⟩
  | a + 1 => by
    obtain ⟨L, n, h⟩ := natAt_reaches a
    refine ⟨L + 1, n + 1, ?_⟩
    show (natStep (natAt L) : SetE Nat) (n + 1) (a + 1)
    simp only [natStep, SetE.union_apply]
    exact Or.inr (by simpa using h)

theorem tyAt_reaches : ∀ τ : type, ∃ L n, tyAt L n τ
  | .Nat => ⟨1, 0, by show (typeStep (gradedIter typeStep 0) : SetE type) 0 type.Nat
                      simp only [typeStep, SetE.union_apply]
                      exact Or.inl (by simp)⟩
  | .Fun a b => by
    obtain ⟨La, na, ha⟩ := tyAt_reaches a
    obtain ⟨Lb, nb, hb⟩ := tyAt_reaches b
    refine ⟨max La Lb + 1, na + nb + 1, ?_⟩
    show (typeStep (tyAt (max La Lb)) : SetE type) (na + nb + 1) (type.Fun a b)
    simp only [typeStep, SetE.union_apply]
    refine Or.inr ?_
    simp only [SetE.pay_succ, SetE.gmap_apply, SetE.pair_apply]
    refine ⟨(a, b), ⟨na, by omega, ?_, ?_⟩, rfl⟩
    · exact tyAt_le (Nat.le_max_left _ _) _ _ ha
    · have harith : na + nb - na = nb := by omega
      rw [harith]
      exact tyAt_le (Nat.le_max_right _ _) _ _ hb

/-! ### Monotonicity in the leaves, not just the recursion -/

theorem stlcAFStep_mono_all {nA nA' : SetE Nat} (hnat : SubE nA nA')
    {x y : TyIx → SetE term} (h : SubIxE x y) : SubIxE (stlcAFStep nA x) (stlcAFStep nA' y) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact (SubE.refl _).union ((hnat.gmap _).union
      ((((h (Γ, .Nat)).pair (h (Γ, .Nat))).gmap _).pay))
  | Fun τ1 τ2 => exact (SubE.refl _).union (((h (τ1 :: Γ, τ2)).gmap _).pay)

theorem stlcStep_mono_all {nA nA' : SetE Nat} {tA tA' : SetE type}
    (hnat : SubE nA nA') (hty : SubE tA tA')
    {x y : TyIx → SetE term} (h : SubIxE x y) :
    SubIxE (stlcStep nA tA x) (stlcStep nA' tA' y) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (stlcAFStep_mono_all hnat h (Γ, τ)).union
    ((SubE.bindC hty fun τ1 =>
      (((h (Γ, .Fun τ1 τ)).pair (h (Γ, τ1))).gmap _)).pay)

theorem stlc_iter_mono_leaves {nA nA' : SetE Nat} {tA tA' : SetE type}
    (hnat : SubE nA nA') (hty : SubE tA tA') :
    ∀ l, SubIxE (gradedIterIx (stlcStep nA tA) l) (gradedIterIx (stlcStep nA' tA') l)
  | 0 => fun _ => SubE.refl _
  | l + 1 => stlcStep_mono_all hnat hty (stlc_iter_mono_leaves hnat hty l)

/-- The enumeration family at leaf budget `L` and iteration count `l`. -/
abbrev enumAt (L l : Nat) : TyIx → SetE term := gradedIterIx (stlcStep (natAt L) (tyAt L)) l

/-- Raise the leaf budget, then the iteration count — both bumps the induction needs. -/
theorem stlc_bump {L L' l l' : Nat} (hL : L ≤ L') (hl : l ≤ l')
    {Γ : List type} {τ : type} {n : Nat} {e : term}
    (h : enumAt L l (Γ, τ) n e) : enumAt L' l' (Γ, τ) n e :=
  subIxE_gradedIterIx_le (fun x y hxy => stlcStep_mono x y hxy) hl (Γ, τ) n e
    (stlc_iter_mono_leaves (natAt_le hL) (tyAt_le hL) l (Γ, τ) n e h)

/-- **Completeness with a real budget.** Every well-typed term is enumerated by the graded enumeration
built from `gradedIter natStep L` / `gradedIter typeStep L` at some concrete `L`. -/
theorem stlc_complete_budget : ∀ {Γ : List type} {e : term} {τ : type}, typing Γ e τ →
    ∃ L levels n, enumAt L levels (Γ, τ) n e := by
  intro Γ e τ h
  induction h with
  | TConst Γ k =>
    obtain ⟨L, m, hm⟩ := natAt_reaches k
    refine ⟨L, 1, m, ?_⟩
    show stlcStep (natAt L) (tyAt L) (enumAt L 0) (Γ, .Nat) m (term.Const k)
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    exact Or.inl (Or.inr (Or.inl ⟨k, hm, rfl⟩))
  | TAdd Γ e1 e2 _ _ ih1 ih2 =>
    obtain ⟨L1, l1, n1, hh1⟩ := ih1
    obtain ⟨L2, l2, n2, hh2⟩ := ih2
    refine ⟨max L1 L2, max l1 l2 + 1, n1 + n2 + 1, ?_⟩
    show stlcStep _ _ (enumAt (max L1 L2) (max l1 l2)) (Γ, .Nat) (n1 + n2 + 1) _
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    refine Or.inl (Or.inr (Or.inr ?_))
    simp only [SetE.pay_succ, SetE.gmap_apply, SetE.pair_apply]
    refine ⟨(e1, e2), ⟨n1, by omega, ?_, ?_⟩, rfl⟩
    · exact stlc_bump (Nat.le_max_left _ _) (Nat.le_max_left _ _) hh1
    · have harith : n1 + n2 - n1 = n2 := by omega
      rw [harith]
      exact stlc_bump (Nat.le_max_right _ _) (Nat.le_max_right _ _) hh2
  | TAbs Γ b τ1 τ2 _ ih =>
    obtain ⟨L, l, n, hh⟩ := ih
    refine ⟨L, l + 1, n + 1, ?_⟩
    show stlcStep _ _ (enumAt L l) (Γ, .Fun τ1 τ2) (n + 1) _
    simp only [stlcStep, SetE.union_apply, stlcAFStep]
    exact Or.inl (Or.inr (by simpa using hh))
  | TVar Γ x σ hlk =>
    obtain ⟨m, hm⟩ := lookupEnum_complete hlk
    refine ⟨0, 1, m, ?_⟩
    cases σ with
    | Nat =>
      show stlcStep _ _ (enumAt 0 0) (Γ, .Nat) m (term.Var x)
      simp only [stlcStep, SetE.union_apply, stlcAFStep]
      exact Or.inl (Or.inl ⟨x, hm, rfl⟩)
    | Fun a b =>
      show stlcStep _ _ (enumAt 0 0) (Γ, .Fun a b) m (term.Var x)
      simp only [stlcStep, SetE.union_apply, stlcAFStep]
      exact Or.inl (Or.inl ⟨x, hm, rfl⟩)
  | TApp Γ e1 e2 τ1 τ2 _ _ ih2 ih1 =>
    obtain ⟨L2, l2, n2, hh2⟩ := ih2
    obtain ⟨L1, l1, n1, hh1⟩ := ih1
    obtain ⟨Lt, k, hk⟩ := tyAt_reaches τ1
    refine ⟨max (max L1 L2) Lt, max l1 l2 + 1, k + (n1 + n2) + 1, ?_⟩
    show stlcStep _ _ (enumAt (max (max L1 L2) Lt) (max l1 l2)) (Γ, τ2) (k + (n1 + n2) + 1) _
    simp only [stlcStep, SetE.union_apply]
    refine Or.inr ?_
    simp only [SetE.pay_succ, SetE.bindC_apply, SetE.gmap_apply, SetE.pair_apply]
    refine ⟨k, by omega, τ1, ?_, (e1, e2), ⟨n1, by omega, ?_, ?_⟩, rfl⟩
    · exact tyAt_le (Nat.le_max_right _ _) _ _ hk
    · exact stlc_bump (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        (Nat.le_max_left _ _) hh1
    · have harith : k + (n1 + n2) - k - n1 = n2 := by omega
      rw [harith]
      exact stlc_bump (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        (Nat.le_max_right _ _) hh2

/-- **The ∃-fold at a concrete leaf budget** — the form a caller can instantiate. -/
theorem stlc_iff_budget (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L levels n, enumAt L levels (Γ, τ) n e :=
  ⟨stlc_complete_budget, fun ⟨_, levels, n, h⟩ => stlc_sound levels Γ τ n e h⟩

/-! ### The value enumeration, at a concrete budget

The payoff: adequacy for the enumeration that actually runs, with a budget a caller supplies. The only
work is transporting through `agreesIx_stlc`, which is why the `Agrees` development was worth doing. -/

theorem agrees_type (levels : Nat) :
    Agrees (gradedIter typeStep levels) (gradedIter typeStep levels) :=
  agrees_gradedIter agrees_typeStep levels

/-- **`typing` is exactly the graded value enumeration, folded over budgets and levels.**

No `Covers` hypothesis, no unbounded leaf limits, no `sorry`: `L` is an ordinary leaf budget and the
enumeration on the right is the one that executes. -/
theorem stlc_mem_iff_budget (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ L levels n,
      e ∈ gradedIterIx (stlcStep (gradedIter natStep L : Lv Nat)
        (gradedIter typeStep L : Lv type)) levels (Γ, τ) n := by
  rw [stlc_iff_budget Γ e τ]
  exact ⟨fun ⟨L, l, n, h⟩ =>
           ⟨L, l, n, (agreesIx_stlc (agrees_nat L) (agrees_type L) l (Γ, τ) n e).mpr h⟩,
         fun ⟨L, l, n, h⟩ =>
           ⟨L, l, n, (agreesIx_stlc (agrees_nat L) (agrees_type L) l (Γ, τ) n e).mp h⟩⟩

/-! # Moving the result to the carrier that runs

`stlc_mem_iff_budget` above is stated at `Lv α = Nat → List α`. `Basalt/Graded.lean`'s own docstring says
that is **the carrier to reason at and the wrong one to run**: being a function it memoises nothing, so
level `n` re-demands levels `0..n` of every operand and a `k`-way union costs `(k+1)^n` demands on the
recursive occurrence. So the theorem above is about code nobody should execute.

`Basalt/GradedRun.lean` supplies `LvT α = Array (Thunk (List α))`: the `Array` memoises *across* levels,
the `Thunk` defers each level. This section restates STLC adequacy there.

## What changes, and why it is forced

**`LvT` is not — and cannot be — a `Graded` instance.** `Choice.nothing` and `Graded.single` have to
allocate an array, and nothing in their types says how long. Every *other* operation inherits its width
from its first operand (`LvT.size_union`, `size_pay`, `size_pair`, `size_bindC`, … all read
`… .size = x.size`). So a width `N` has to be threaded explicitly through the leaves, and each definition
below takes an extra `N` that its `Lv` counterpart does not: `natStepT N`, `typeStepT N`, `lookupEnumT N`,
`stlcAFStepT N`, `stlcStepT N`, and the two closures `gradedIterT N` / `gradedIterIxT N`.

The threading is not decoration. `Agree.union`, `.pair` and `.bindC` each carry a *size side condition*
(`y.size = x.size`, `∀ a, (k a).size = x.size`), because `LvT.union x y` is built at `x.size` and would
silently truncate a longer `y`. Discharging those obligations is the whole cost of the carrier change, and
it is discharged by one invariant, maintained by every definition here:

    every enumeration in the system has width exactly `N + 1`

hence the `size_*T` lemmas below, which are what the `Agree` proofs consume. `LvT.nothing`/`LvT.single`
produce `N + 1` levels (that is their `+ 1`), so `N` is "the largest level stored", and `gradedIterT N`
starts from `LvT.nothing N` for exactly the reason `gradedIter` starts from `Choice.nothing`.

## Why the conclusion is bounded, and why that is honest rather than a weakening

`Agree x m := ∀ n < x.size, x.get n = m n` is deliberately bounded, and it has to be: past the end
`LvT.get` returns `[]` whereas `Lv` keeps going, so the unbounded statement is simply false. The final
theorem therefore reads

    typing Γ e τ ↔ ∃ N L levels n, n < N + 1 ∧ e ∈ (enumT N L levels (Γ, τ)).get n

The `n < N + 1` is not an obstruction to the `↔`: the forward direction gets an `n` from the `Lv` theorem
and is free to *choose* the width, taking `N := n`. So the bound costs nothing here. What it does do is
make the statement say the true thing — a finite run claims only the levels it allocated — and a caller
with a width already fixed gets `mem_enumT_iff` instead, which is the same fact level by level.

## One thing the array does *not* memoise

`gradedIterIxT N step (l+1) i = step (gradedIterIxT N step l) i` passes the recursive occurrence as a
*function of the index*, so two syntactic occurrences at the same index (`LvT.pair (rec (Γ,.Nat))
(rec (Γ,.Nat))` in `TAdd`) build two arrays. Memoisation here is across *levels*, which is the `(k+1)^n`
blow-up `Lv` suffers; sharing across *indices* would need the family itself to be data (a memo table keyed
by `TyIx`) and is a separate change. -/

/-! ## The system at `LvT`

Each definition mirrors its `Lv` counterpart operation for operation, with `N` threaded. -/

/-- `Nat` graded by magnitude, at width `N + 1`. -/
def natStepT (N : Nat) (rec : LvT Nat) : LvT Nat :=
  LvT.union (LvT.single N 0) (LvT.pay (LvT.gmap (· + 1) rec))

/-- `type` graded by size, at width `N + 1`. -/
def typeStepT (N : Nat) (rec : LvT type) : LvT type :=
  LvT.union (LvT.single N type.Nat)
    (LvT.pay (LvT.gmap (fun p => type.Fun p.1 p.2) (LvT.pair rec rec)))

/-- The de Bruijn indices at which `Γ` holds `τ`, at width `N + 1`. Structurally recursive on `Γ`, exactly
as `lookupEnum` is — the width is threaded unchanged. -/
def lookupEnumT (N : Nat) : List type → type → LvT Nat
  | [], _ => LvT.nothing N
  | σ :: Γ, τ =>
      LvT.union (if σ = τ then LvT.single N 0 else LvT.nothing N)
        (LvT.pay (LvT.gmap (· + 1) (lookupEnumT N Γ τ)))

/-- The `TApp`-free fragment at width `N + 1`. -/
def stlcAFStepT (N : Nat) (natE : LvT Nat) (rec : TyIx → LvT term) : TyIx → LvT term
  | (Γ, .Nat) =>
      LvT.union (LvT.gmap term.Var (lookupEnumT N Γ .Nat))
        (LvT.union (LvT.gmap term.Const natE)
          (LvT.pay (LvT.gmap (fun p => term.Add p.1 p.2)
            (LvT.pair (rec (Γ, .Nat)) (rec (Γ, .Nat))))))
  | (Γ, .Fun τ1 τ2) =>
      LvT.union (LvT.gmap term.Var (lookupEnumT N Γ (.Fun τ1 τ2)))
        (LvT.pay (LvT.gmap (term.Abs τ1) (rec (τ1 :: Γ, τ2))))

/-- The full system at width `N + 1`. `LvT.bindC` is the correlated premise, same as at `Lv`. -/
def stlcStepT (N : Nat) (natE : LvT Nat) (typeE : LvT type) (rec : TyIx → LvT term) :
    TyIx → LvT term
  | (Γ, τ) =>
      LvT.union (stlcAFStepT N natE rec (Γ, τ))
        (LvT.pay (LvT.bindC typeE (fun τ1 =>
          LvT.gmap (fun p => term.App p.1 p.2)
            (LvT.pair (rec (Γ, .Fun τ1 τ)) (rec (Γ, τ1))))))

/-- `gradedIter` at `LvT`. The base case has to *name* the width — that is the one place the carrier's
explicit size cannot be inferred from an operand. -/
def gradedIterT {α : Type} (N : Nat) (step : LvT α → LvT α) : Nat → LvT α
  | 0 => LvT.nothing N
  | l + 1 => step (gradedIterT N step l)

/-- `gradedIterIx` at `LvT`. Same remark about the base case. -/
def gradedIterIxT {α ι : Type} (N : Nat) (step : (ι → LvT α) → ι → LvT α) : Nat → ι → LvT α
  | 0, _ => LvT.nothing N
  | l + 1, i => step (gradedIterIxT N step l) i

/-! ## The width invariant

Every enumeration above has width exactly `N + 1`. These are what discharge the size side conditions on
`Agree.union` / `.pair` / `.bindC`; without them the carrier change does not go through. -/

@[simp] theorem size_natStepT (N : Nat) (rec : LvT Nat) : (natStepT N rec).size = N + 1 := by
  simp [natStepT]

@[simp] theorem size_typeStepT (N : Nat) (rec : LvT type) : (typeStepT N rec).size = N + 1 := by
  simp [typeStepT]

@[simp] theorem size_lookupEnumT (N : Nat) (τ : type) : ∀ Γ : List type,
    (lookupEnumT N Γ τ).size = N + 1
  | [] => by simp [lookupEnumT]
  | σ :: Γ => by
      rw [lookupEnumT, LvT.size_union]
      by_cases h : σ = τ <;> simp [h]

@[simp] theorem size_stlcAFStepT (N : Nat) (natE : LvT Nat) (rec : TyIx → LvT term) (i : TyIx) :
    (stlcAFStepT N natE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  cases τ <;> simp [stlcAFStepT]

@[simp] theorem size_stlcStepT (N : Nat) (natE : LvT Nat) (typeE : LvT type)
    (rec : TyIx → LvT term) (i : TyIx) : (stlcStepT N natE typeE rec i).size = N + 1 := by
  obtain ⟨Γ, τ⟩ := i
  simp [stlcStepT]

theorem size_gradedIterT {α : Type} (N : Nat) {step : LvT α → LvT α}
    (hs : ∀ x, (step x).size = N + 1) : ∀ l, (gradedIterT N step l).size = N + 1
  | 0 => by simp [gradedIterT]
  | _ + 1 => hs _

theorem size_gradedIterIxT {α ι : Type} (N : Nat) {step : (ι → LvT α) → ι → LvT α}
    (hs : ∀ x i, (step x i).size = N + 1) : ∀ l i, (gradedIterIxT N step l i).size = N + 1
  | 0, _ => by simp [gradedIterIxT]
  | _ + 1, i => hs _ i

/-! ## Agreement with the `Lv` system

Nothing about `Agrees` or `SubE` is reproved: every step below is an application of a closure lemma from
`Basalt/GradedRun.lean`, plus a size obligation discharged by the invariant above. The one piece of
plumbing `GradedRun` does not ship is the `ite` case, needed for `lookupEnum`'s `σ = τ` side condition. -/

/-- `Agree` through an `if`, the analogue of `Agrees.ite`. `lookupEnumT`'s `Now` rule needs it. -/
theorem agree_iteT {α : Type} {c : Prop} [Decidable c] {x y : LvT α} {m p : Lv α}
    (hx : Agree x m) (hy : Agree y p) : Agree (if c then x else y) (if c then m else p) := by
  by_cases h : c
  · simpa [h] using hx
  · simpa [h] using hy

theorem agree_natStepT (N : Nat) {rec : LvT Nat} {m : Lv Nat}
    (h : Agree rec m) (hsz : rec.size = N + 1) : Agree (natStepT N rec) (natStep m) :=
  (agree_single N 0).union ((h.gmap _).pay) (by simp [hsz])

theorem agree_typeStepT (N : Nat) {rec : LvT type} {m : Lv type}
    (h : Agree rec m) (hsz : rec.size = N + 1) : Agree (typeStepT N rec) (typeStep m) :=
  (agree_single N type.Nat).union (((h.pair h rfl).gmap _).pay) (by simp [hsz])

theorem agree_lookupEnumT (N : Nat) (τ : type) : ∀ Γ : List type,
    Agree (lookupEnumT N Γ τ) (lookupEnum Γ τ)
  | [] => agree_nothing N
  | σ :: Γ => by
      rw [lookupEnumT, lookupEnum]
      refine Agree.union (agree_iteT (agree_single N 0) (agree_nothing N))
        (((agree_lookupEnumT N τ Γ).gmap _).pay) ?_
      by_cases h : σ = τ <;> simp [h]

theorem agree_stlcAFStepT (N : Nat) {natE : LvT Nat} {natM : Lv Nat}
    (hn : Agree natE natM) (hnsz : natE.size = N + 1)
    {rec : TyIx → LvT term} {m : TyIx → Lv term}
    (h : ∀ i, Agree (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, Agree (stlcAFStepT N natE rec i) (stlcAFStep natM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  cases τ with
  | Nat =>
    exact ((agree_lookupEnumT N _ Γ).gmap _).union
      ((hn.gmap _).union
        ((((h (Γ, .Nat)).pair (h (Γ, .Nat)) rfl).gmap _).pay) (by simp [hsz, hnsz]))
      (by simp [hnsz])
  | Fun τ1 τ2 =>
    exact ((agree_lookupEnumT N _ Γ).gmap _).union
      (((h (τ1 :: Γ, τ2)).gmap _).pay) (by simp [hsz])

theorem agree_stlcStepT (N : Nat) {natE : LvT Nat} {natM : Lv Nat}
    (hn : Agree natE natM) (hnsz : natE.size = N + 1)
    {typeE : LvT type} {typeM : Lv type}
    (ht : Agree typeE typeM) (htsz : typeE.size = N + 1)
    {rec : TyIx → LvT term} {m : TyIx → Lv term}
    (h : ∀ i, Agree (rec i) (m i)) (hsz : ∀ i, (rec i).size = N + 1) :
    ∀ i, Agree (stlcStepT N natE typeE rec i) (stlcStep natM typeM m i) := by
  intro i
  obtain ⟨Γ, τ⟩ := i
  exact (agree_stlcAFStepT N hn hnsz h hsz (Γ, τ)).union
    ((ht.bindC (fun τ1 => (((h (Γ, .Fun τ1 τ)).pair (h (Γ, τ1)) (by simp [hsz])).gmap _))
        (fun _ => by simp [hsz, htsz])).pay)
    (by simp [htsz])

theorem agree_gradedIterT {α : Type} (N : Nat) {stepT : LvT α → LvT α} {step : Lv α → Lv α}
    (hstep : ∀ x m, Agree x m → x.size = N + 1 → Agree (stepT x) (step m))
    (hsize : ∀ x, (stepT x).size = N + 1) :
    ∀ l, Agree (gradedIterT N stepT l) (gradedIter step l)
  | 0 => agree_nothing N
  | l + 1 =>
      hstep _ _ (agree_gradedIterT N hstep hsize l) (size_gradedIterT N hsize l)

theorem agree_gradedIterIxT {α ι : Type} (N : Nat) {stepT : (ι → LvT α) → ι → LvT α}
    {step : (ι → Lv α) → ι → Lv α}
    (hstep : ∀ x m, (∀ i, Agree (x i) (m i)) → (∀ i, (x i).size = N + 1) →
      ∀ i, Agree (stepT x i) (step m i))
    (hsize : ∀ x i, (stepT x i).size = N + 1) :
    ∀ l i, Agree (gradedIterIxT N stepT l i) (gradedIterIx step l i)
  | 0, _ => agree_nothing N
  | l + 1, i =>
      hstep _ _ (agree_gradedIterIxT N hstep hsize l) (size_gradedIterIxT N hsize l) i

/-! ## The executable enumeration, and its agreement -/

/-- **The STLC enumeration that runs.** Array width `N + 1` (levels `0..N`), leaf budget `L`, `levels`
iterations. Definitionally the `Lv` enumeration of `stlc_mem_iff_budget` with `LvT` operations in place of
`Lv` ones and the width threaded. -/
def enumT (N L levels : Nat) : TyIx → LvT term :=
  gradedIterIxT N
    (stlcStepT N (gradedIterT N (natStepT N) L) (gradedIterT N (typeStepT N) L)) levels

/-- The `Lv` enumeration `enumT` mirrors — the right-hand side of `stlc_mem_iff_budget`. -/
abbrev enumLv (L levels : Nat) : TyIx → Lv term :=
  gradedIterIx (stlcStep (gradedIter natStep L : Lv Nat) (gradedIter typeStep L : Lv type)) levels

@[simp] theorem size_enumT (N L levels : Nat) (i : TyIx) : (enumT N L levels i).size = N + 1 :=
  size_gradedIterIxT N (fun _ _ => size_stlcStepT ..) levels i

/-- **The carrier change is sound and loses nothing within the width.** Every level the array stores reads
exactly as the `Lv` enumeration does. -/
theorem agree_enumT (N L levels : Nat) (i : TyIx) :
    Agree (enumT N L levels i) (enumLv L levels i) :=
  agree_gradedIterIxT N
    (fun _ _ hx hsz =>
      agree_stlcStepT N
        (agree_gradedIterT N (fun _ _ h hs => agree_natStepT N h hs) (fun _ => size_natStepT ..) L)
        (size_gradedIterT N (fun _ => size_natStepT ..) L)
        (agree_gradedIterT N (fun _ _ h hs => agree_typeStepT N h hs) (fun _ => size_typeStepT ..) L)
        (size_gradedIterT N (fun _ => size_typeStepT ..) L)
        hx hsz)
    (fun _ _ => size_stlcStepT ..) levels i

/-- The level-by-level form, for a caller whose width is already fixed. -/
theorem mem_enumT_iff (N L levels : Nat) (i : TyIx) (n : Nat) (hn : n < N + 1) (e : term) :
    e ∈ (enumT N L levels i).get n ↔ e ∈ enumLv L levels i n := by
  rw [agree_enumT N L levels i n (by simpa using hn)]

/-- **`typing` is exactly the enumeration that runs.**

Same content as `stlc_mem_iff_budget`, on `Array (Thunk (List term))` instead of `Nat → List term` — so
the theorem is now about code with the right cost model: levels are memoised by the array and deferred by
the thunks, rather than recomputed `(k+1)^n` times by a function carrier.

The extra `N` is the array width and the extra `n < N + 1` is `Agree`'s bound. Neither weakens the
biconditional: `→` produces its own level and may take `N := n`; `←` is the `Lv` soundness result
transported over one level the array actually stores. -/
theorem stlc_mem_iff_run (Γ : List type) (e : term) (τ : type) :
    typing Γ e τ ↔ ∃ N L levels n, n < N + 1 ∧ e ∈ (enumT N L levels (Γ, τ)).get n := by
  rw [stlc_mem_iff_budget Γ e τ]
  constructor
  · rintro ⟨L, levels, n, h⟩
    exact ⟨n, L, levels, n, Nat.lt_succ_self n,
      (mem_enumT_iff n L levels (Γ, τ) n (Nat.lt_succ_self n) e).mpr h⟩
  · rintro ⟨N, L, levels, n, hn, h⟩
    exact ⟨L, levels, n, (mem_enumT_iff N L levels (Γ, τ) n hn e).mp h⟩

/-! ## The carrier change did not alter the enumeration

`agree_enumT` proves this, but a proof about `LvT.get` is only as good as the definitions being the ones
that run. These `#guard_msgs` compare the two carriers *by evaluation*, level for level and term for term,
which is the check that catches a definition drifting apart from the one the theorem is about. -/

private def widthT : Nat := 3
private def fullLvT : TyIx → LvT term := enumT widthT 6 4
private def fullLvRef : TyIx → Lv term := enumLv 6 4

-- The same terms, in the same order, at every level the array stores. This is `agree_enumT` run.
/-- info: [true, true, true, true] -/
#guard_msgs in
#eval ((List.range 4).map fun n =>
  (fullLvT ([], .Nat)).get n == fullLvRef ([], .Nat) n)

-- And at a function type, where level 0 is empty because `TAbs` has to pay.
/-- info: [true, true, true, true] -/
#guard_msgs in
#eval ((List.range 4).map fun n =>
  (fullLvT ([], .Fun .Nat .Nat)).get n == fullLvRef ([], .Fun .Nat .Nat) n)

-- The counts `GradedStlcTest.lean` pins for the `Lv` enumeration, reproduced from the array.
/-- info: [1, 2, 7, 28] -/
#guard_msgs in
#eval ((List.range 4).map fun n => ((fullLvT ([], .Nat)).get n).length)

-- Including the two applications that the `bind`-vs-`bindC` fix added at level 2, so the regression this
-- family exists to guard is guarded on the executable carrier too.
/--
info: [term.App (term.Abs (type.Nat) (term.Var 0)) (term.Const 0),
 term.App (term.Abs (type.Nat) (term.Const 0)) (term.Const 0)]
-/
#guard_msgs in
#eval ((fullLvT ([], .Nat)).get 2).filter fun t =>
  !((fullLvT ([], .Nat)).get 1).contains t && t matches term.App _ _

-- Past the width the array is empty while `Lv` keeps going: `Agree`'s `n < x.size` is load-bearing, not
-- bureaucratic. `widthT = 3` stores levels `0..3`, so level 4 is out of range.
/-- info: (0, true) -/
#guard_msgs in
#eval (((fullLvT ([], .Nat)).get 4).length, !(fullLvRef ([], .Nat) 4).isEmpty)

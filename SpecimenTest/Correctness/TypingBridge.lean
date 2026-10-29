import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.STLCBasaltGenerators
import Specimen
import Specimen.Basalt
import Specimen.Correctness.GenInterpSPMF
import SpecimenTest.Correctness.StlcMeasures

/-!
# The derived `typing` generator, as one generic interpreter

`DerivedGeneratorViaInterp.lean` bridges the simplest derived generator (`lookup`) to `genRelB`.
This file does the real one: the `typing` generator, whose step has five branches, input-dispatch
guards, size halving, an unconstrained type draw, and a delegated external sub-producer. `typ_bridge`
proves the emitted definition *is* `genRelB (typStep iS)`, and soundness and completeness then come
from the generic theorems, with all relation-specific content confined to per-branch obligations.

The default scorer schedules `TApp` by *drawing* the argument type from the unconstrained
`ArbitraryFueled type` generator, so `derive_mutual` emits a single self-recursive `typing` worker:
the bridge is through `genRelB`, not `genRelFam` (which keeps its generic theory and its
`EvGenSPMF`-style uses, but has no emitted instance here). What makes `typing` genuinely harder than
`lookup`:

* **Input dispatch.** `TConst`/`TAdd` are guarded on the target type being `Nat`, `TAbs` on it being
  an arrow, so the pool is `List.filterMap id` over guarded options and its shape depends on the
  input. The step reproduces the guards verbatim; the proofs case on the target type first.
* **Size halving.** `TAdd` and `TApp` recurse at `Nat.div size' 2`, `TAbs` at `size'`. Since the step
  receives `prev` as a family over size, all three are ordinary applications.
* **External sub-producers.** The `TVar` branch calls `BacktrackGenFor.gen` for `lookup`, and
  `TConst`/`TApp` call `ArbitraryFueled.arbitraryFueled`. These are *not* part of the recursion; they
  appear in the step as constants, which is the right treatment — their own correctness is a separate
  obligation (`lookup` in `DerivedGeneratorViaInterp.lean`, the unconstrained draws in
  `StlcMeasures.lean`), taken here as hypotheses (`LookupSound`, `LookupComplete`).

## What is proved here

* `typ_bridge` — the emitted generator is `genRelB (typStep iS)`.
* `typStep_sound` / `typing_emitted_sound` — soundness, with the external `lookup` producer's
  soundness as a hypothesis.
* `typStep_complete` / `typing_emitted_complete` — completeness relative to the measures of
  `StlcMeasures.lean`. The `initSize`-dependent conditions (`leafBound`, `tyNeed`) cannot live in the
  measure pair, which budgets fuel and size, so they go into the *specification* (`typSpecC`). The
  interpreter allows this because the soundness and completeness predicates are independent:
  soundness concludes only `typing`, completeness assumes the `initSize`-bounded strengthening.
* `typing_emitted_complete_depth` — the closed-form corollary via `budget_lt_sizeMeasure`.

The completeness side conditions come out identical to the ones `StlcCompleteness.lean` derives by
hand, which is the cross-check that the generic route computes the *right* budgets rather than merely
sufficient ones.
-/

open Plausible Basalt Specimen.Correctness

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true
-- The pool-membership simp set below is shared across guard configurations; which guard-reduction
-- lemmas fire depends on how the guards evaluate.
set_option linter.unusedSimpArgs false

-- Namespaced so the derived `BacktrackGenFor` instances cannot collide with another module's
-- derivation of the same producers when the whole library is built under `specimen.emitBasalt`.
namespace TypingBridge

#guard_msgs(drop info) in
derive_mutual generator (fun G t => ∃ e, typing G e t)

-- Reconstruct the emitted step, verbatim: input-dispatch guards, `filterMap` pool, weight literals,
-- `Unit`-function branches, the delegated `lookup` instance, the unconstrained draws.
noncomputable def typStep (iS : Nat) : SGenStep (List type × type) term :=
  fun prev sz i =>
    match sz with
    | 0 =>
      Specimen.Backtrack.backtrack
        (List.filterMap (fun o => o)
          [if (match i.2 with | type.Nat => true | _ => false) then
              some (4, fun (_ : Unit) =>
                match i.2 with
                | type.Nat =>
                  (Basalt.ArbitraryFueled.arbitraryFueled iS) >>=
                    fun n => pure (term.Const n)
                | _ => Specimen.refute)
            else none,
            some (3, fun (_ : Unit) =>
              @BacktrackGenFor.gen _ (fun (x : Nat) => @lookup i.1 x i.2) _ SGen _ _ _ _ _ _ iS iS >>=
                fun x => pure (term.Var x)),
            if (match i.2 with | type.Nat => true | _ => false) then
              some (1, fun (_ : Unit) =>
                match i.2 with
                | type.Nat => Specimen.truncated
                | _ => Specimen.refute)
            else none,
            if (match i.2 with | type.Fun _ _ => true | _ => false) then
              some (1, fun (_ : Unit) =>
                match i.2 with
                | type.Fun _ _ => Specimen.truncated
                | _ => Specimen.refute)
            else none,
            some (1, fun (_ : Unit) => Specimen.truncated)])
    | Nat.succ size' =>
      Specimen.Backtrack.backtrack
        (List.filterMap (fun o => o)
          [if (match i.2 with | type.Nat => true | _ => false) then
              some (4, fun (_ : Unit) =>
                match i.2 with
                | type.Nat =>
                  (Basalt.ArbitraryFueled.arbitraryFueled iS) >>=
                    fun n => pure (term.Const n)
                | _ => Specimen.refute)
            else none,
            some (3, fun (_ : Unit) =>
              @BacktrackGenFor.gen _ (fun (x : Nat) => @lookup i.1 x i.2) _ SGen _ _ _ _ _ _ iS iS >>=
                fun x => pure (term.Var x)),
            if (match i.2 with | type.Nat => true | _ => false) then
              some (3, fun (_ : Unit) =>
                match i.2 with
                | type.Nat =>
                  prev (Nat.div size' 2) (i.1, type.Nat) >>= fun e1 =>
                    prev (Nat.div size' 2) (i.1, type.Nat) >>= fun e2 =>
                      pure (term.Add e1 e2)
                | _ => Specimen.refute)
            else none,
            if (match i.2 with | type.Fun _ _ => true | _ => false) then
              some (3, fun (_ : Unit) =>
                match i.2 with
                | type.Fun τ1 τ2 =>
                  prev size' (List.cons τ1 i.1, τ2) >>= fun e =>
                    pure (term.Abs τ1 e)
                | _ => Specimen.refute)
            else none,
            some (3, fun (_ : Unit) =>
              (Basalt.ArbitraryFueled.arbitraryFueled iS) >>=
                fun τ1 =>
                  prev (Nat.div size' 2) (i.1, type.Fun τ1 i.2) >>= fun e1 =>
                    prev (Nat.div size' 2) (i.1, τ1) >>= fun e2 =>
                      pure (term.App e1 e2))])

/-- **Adequacy bridge**: the emitted `typing` generator IS the generic interpreter at `typStep`. -/
theorem typ_bridge (iS : Nat) :
    ∀ (fuel sz : Nat) (Γ : List type) (τ : type),
      (specimen_gen_typing_1__SpecimenTest_Correctness_TypingBridge_TypingBridge
          (G := SGen) fuel iS sz Γ τ)
        = genRelB (typStep iS) fuel sz (Γ, τ) := by
  intro fuel
  induction fuel with
  | zero => intro sz Γ τ; rfl
  | succ fuel ih =>
    intro sz Γ τ
    cases sz with
    | zero => rfl
    | succ sz =>
      simp only [specimen_gen_typing_1__SpecimenTest_Correctness_TypingBridge_TypingBridge,
        genRelB, typStep, ih]

/-- The specification: a produced term is well typed at the input context and type. -/
def typSpec : (List type × type) → term → Prop := fun i e => typing i.1 e i.2

/-- Soundness of the *external* `lookup` sub-producer, as a hypothesis.
`DerivedGeneratorViaInterp.lean` discharges exactly this statement for its own derivation. -/
def LookupSound (iS : Nat) : Prop :=
  ∀ (Γ : List type) (τ : type) (x : Nat),
    Produces (BacktrackGenFor.gen (α := Nat) (P := fun x => lookup Γ x τ) (G := SGen) iS iS) x →
    lookup Γ x τ

theorem typStep_sound (iS : Nat) (hlk : LookupSound iS) : StepGenSoundB (typStep iS) typSpec := by
  intro prev hprev sz i x hx
  obtain ⟨Γ, τ⟩ := i
  -- The two unguarded-or-`Nat`-guarded base branches, shared by every pool that contains them.
  have tconst : ∀ (g : SGen Nat),
      Produces ((g >>= fun n => pure (term.Const n))
        : SGen term) x → typing Γ x type.Nat := by
    intro g hqa
    obtain ⟨n, _, he⟩ := produces_bind_iff.mp hqa
    cases produces_pure_iff.mp he
    exact typing.TConst Γ n
  have tvar : ∀ τ,
      Produces ((@BacktrackGenFor.gen _ (fun (x : Nat) => @lookup Γ x τ) _ SGen _ _ _ _ _ _ iS iS >>=
        fun x => pure (term.Var x)) : SGen term) x → typing Γ x τ := by
    intro τ hqa
    obtain ⟨n, hn, he⟩ := produces_bind_iff.mp hqa
    cases produces_pure_iff.mp he
    exact typing.TVar Γ n τ (hlk Γ τ n hn)
  cases τ with
  | Nat =>
    cases sz with
    | zero =>
      simp only [typStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact tconst _ hpx
      · exact tvar _ hpx
      · simp at hpx
      · simp at hpx
    | succ sz =>
      simp only [typStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact tconst _ hpx
      · exact tvar _ hpx
      · -- TAdd
        obtain ⟨e1, h1, hrest⟩ := produces_bind_iff.mp hpx
        obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest
        cases produces_pure_iff.mp he
        exact typing.TAdd Γ e1 e2 (hprev _ _ _ h1) (hprev _ _ _ h2)
      · -- TApp
        obtain ⟨τ1, _, hrest⟩ := produces_bind_iff.mp hpx
        obtain ⟨e1, h1, hrest2⟩ := produces_bind_iff.mp hrest
        obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest2
        cases produces_pure_iff.mp he
        exact typing.TApp Γ e1 e2 τ1 type.Nat (hprev _ _ _ h2) (hprev _ _ _ h1)
  | Fun τ1 τ2 =>
    cases sz with
    | zero =>
      simp only [typStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact tvar _ hpx
      · simp at hpx
      · simp at hpx
    | succ sz =>
      simp only [typStep] at hx
      obtain ⟨p, hp, _, hpx⟩ := produces_backtrack_ok _ _ hx
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
        ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact tvar _ hpx
      · -- TAbs
        obtain ⟨e0, h0, he⟩ := produces_bind_iff.mp hpx
        cases produces_pure_iff.mp he
        exact typing.TAbs Γ e0 τ1 τ2 (hprev _ _ _ h0)
      · -- TApp
        obtain ⟨τ0, _, hrest⟩ := produces_bind_iff.mp hpx
        obtain ⟨e1, h1, hrest2⟩ := produces_bind_iff.mp hrest
        obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest2
        cases produces_pure_iff.mp he
        exact typing.TApp Γ e1 e2 τ0 _ (hprev _ _ _ h2) (hprev _ _ _ h1)

/-- **Soundness of the emitted `typing` generator, through the generic interpreter.** -/
theorem typing_emitted_sound (iS : Nat) (hlk : LookupSound iS)
    (fuel sz : Nat) (Γ : List type) (τ : type) (e : term)
    (hx : Produces (specimen_gen_typing_1__SpecimenTest_Correctness_TypingBridge_TypingBridge
        (G := SGen) fuel iS sz Γ τ) e) :
    typing Γ e τ := by
  rw [Produces, typ_bridge] at hx
  exact genRelB_produces_sound (typStep_sound iS hlk) fuel sz (Γ, τ) e hx

/-! ## Completeness -/

/-- The strengthened specification completeness is relative to: the `initSize`-dependent bounds
live here, because the measure pair only budgets fuel and size. -/
def typSpecC (iS : Nat) : (List type × type) → term → Prop := fun i e =>
  typing i.1 e i.2 ∧ leafBound e ≤ iS ∧ varBound e ≤ 10000 ∧ tyNeed i.1 e ≤ iS

/-- Fuel measure: `tdepth`, one level per constructor. -/
def typPhi : (List type × type) → term → Nat := fun _ e => tdepth e

/-- Size measure: `budget`, doubling at the halving constructors. -/
def typSigma : (List type × type) → term → Nat := fun _ e => budget e

/-- Completeness of the *external* `lookup` sub-producer, as a hypothesis. The two side conditions
are the emitted instance's: it runs the `lookup` worker at size `iS` and at the hard-wired fuel
`10000`. -/
def LookupComplete (iS : Nat) : Prop :=
  ∀ (Γ : List type) (τ : type) (x : Nat), lookup Γ x τ → x < iS → x < 10000 →
    Produces (BacktrackGenFor.gen (α := Nat) (P := fun x => lookup Γ x τ) (G := SGen) iS iS) x

theorem typStep_complete (iS : Nat) (hlkc : LookupComplete iS) :
    StepGenCompleteB (typStep iS) (typSpecC iS) typPhi typSigma := by
  intro prev sz i a hP hsz hrec
  obtain ⟨Γ, τ⟩ := i
  obtain ⟨hty, hv, hlf, ht⟩ := hP
  cases hty with
  | TConst =>
    rename_i n
    have body : Produces (((Basalt.ArbitraryFueled.arbitraryFueled iS) >>= fun n => pure (term.Const n))
        : SGen term) (term.Const n) :=
      produces_bind_of (produces_arbitraryFueled_nat _ n (by simpa only [leafBound] using hv))
        (produces_pure_iff.mpr rfl)
    cases sz with
    | zero =>
      simp only [typStep]
      exact produces_backtrack_of_branch _ _ (List.Mem.head _)
        (by exact Nat.zero_lt_succ _) _ body
    | succ sz =>
      simp only [typStep]
      exact produces_backtrack_of_branch _ _ (List.Mem.head _)
        (by exact Nat.zero_lt_succ _) _ body
  | TVar =>
    rename_i x hlkd
    simp only [leafBound] at hv
    simp only [varBound] at hlf
    have body : Produces ((@BacktrackGenFor.gen _ (fun (x : Nat) => @lookup Γ x τ) _ SGen _ _ _ _ _ _ iS iS >>=
        fun x => pure (term.Var x)) : SGen term) (term.Var x) :=
      produces_bind_of (hlkc Γ τ x hlkd (by omega) (by omega)) (produces_pure_iff.mpr rfl)
    cases τ with
    | Nat =>
      cases sz with
      | zero =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _
          (List.Mem.tail _ (List.Mem.head _)) (by exact Nat.zero_lt_succ _) _ body
      | succ sz =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _
          (List.Mem.tail _ (List.Mem.head _)) (by exact Nat.zero_lt_succ _) _ body
    | Fun τ1 τ2 =>
      cases sz with
      | zero =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _ (List.Mem.head _)
          (by exact Nat.zero_lt_succ _) _ body
      | succ sz =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _ (List.Mem.head _)
          (by exact Nat.zero_lt_succ _) _ body
  | TAdd =>
    rename_i e1 e2 h1 h2
    cases sz with
    | zero => exact absurd hsz (by simp only [typSigma, budget]; omega)
    | succ sz =>
      simp only [typSigma, budget] at hsz
      simp only [leafBound] at hv
      simp only [varBound] at hlf
      simp only [tyNeed] at ht
      simp only [typStep]
      refine produces_backtrack_of_branch _ _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by exact Nat.zero_lt_succ _) _ ?_
      refine produces_bind_of
        (hrec (Γ, type.Nat) e1 ⟨h1, by omega, by omega, by dsimp only; omega⟩
          (by simp only [typPhi, tdepth]; omega) (sz / 2)
          (by simpa only [typSigma] using budget_children hsz |>.1)) ?_
      exact produces_bind_of
        (hrec (Γ, type.Nat) e2 ⟨h2, by omega, by omega, by dsimp only; omega⟩
          (by simp only [typPhi, tdepth]; omega) (sz / 2)
          (by simpa only [typSigma] using (budget_children hsz).2.1))
        (produces_pure_iff.mpr rfl)
  | TAbs =>
    rename_i e0 τ1 τ2 hbody
    cases sz with
    | zero => exact absurd hsz (by simp only [typSigma, budget]; omega)
    | succ sz =>
      simp only [typSigma, budget] at hsz
      simp only [typStep]
      refine produces_backtrack_of_branch _ _
        (List.Mem.tail _ (List.Mem.head _)) (by exact Nat.zero_lt_succ _) _ ?_
      refine produces_bind_of
        (hrec (τ1 :: Γ, τ2) e0
          ⟨hbody, by simpa only [leafBound] using hv, by simpa only [varBound] using hlf,
            by simpa only [tyNeed] using ht⟩
          (by simp only [typPhi, tdepth]; omega) sz
          (by simp only [typSigma]; omega)) ?_
      exact produces_pure_iff.mpr rfl
  | TApp =>
    rename_i e1 e2 τ1 h2 h1
    cases sz with
    | zero => exact absurd hsz (by simp only [typSigma, budget]; omega)
    | succ sz =>
      simp only [typSigma, budget] at hsz
      simp only [leafBound] at hv
      simp only [varBound] at hlf
      simp only [tyNeed, typing_outTy h2, Option.elim] at ht
      have hbody : Produces (((Basalt.ArbitraryFueled.arbitraryFueled iS) >>= fun τ1' =>
            prev (Nat.div sz 2) (Γ, type.Fun τ1' τ) >>= fun e1 =>
              prev (Nat.div sz 2) (Γ, τ1') >>= fun e2 =>
                pure (term.App e1 e2)) : SGen term) (term.App e1 e2) := by
        refine produces_bind_of
          (type_gen_produces τ1 iS (by omega)) ?_
        refine produces_bind_of
          (hrec (Γ, type.Fun τ1 τ) e1 ⟨h1, by omega, by omega, by dsimp only; omega⟩
            (by simp only [typPhi, tdepth]; omega) (sz / 2)
            (by simpa only [typSigma] using (budget_children hsz).1)) ?_
        exact produces_bind_of
          (hrec (Γ, τ1) e2 ⟨h2, by omega, by omega, by dsimp only; omega⟩
            (by simp only [typPhi, tdepth]; omega) (sz / 2)
            (by simpa only [typSigma] using (budget_children hsz).2.1))
          (produces_pure_iff.mpr rfl)
      -- The pool position of `TApp` depends on which guarded branches dispatch kept.
      cases τ with
      | Nat =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          (by exact Nat.zero_lt_succ _) _ hbody
      | Fun _ _ =>
        simp only [typStep]
        exact produces_backtrack_of_branch _ _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
          (by exact Nat.zero_lt_succ _) _ hbody

/-- **Completeness of the emitted `typing` generator, through the generic interpreter.** The side
conditions are the measures of `StlcMeasures.lean`, and they match the hand-rolled proof in
`StlcCompleteness.lean` — the cross-check that the generic route computes the same budgets. -/
theorem typing_emitted_complete (iS : Nat) (hlkc : LookupComplete iS)
    (Γ : List type) (τ : type) (e : term) (h : typing Γ e τ)
    (fuel sz : Nat) (hf : tdepth e < fuel) (hs : budget e ≤ sz)
    (hv : leafBound e ≤ iS) (hlf : varBound e ≤ 10000) (ht : tyNeed Γ e ≤ iS) :
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_TypingBridge_TypingBridge
      (G := SGen) fuel iS sz Γ τ) e := by
  rw [Produces, typ_bridge]
  exact genRelB_complete (typStep_complete iS hlkc) fuel (Γ, τ) e ⟨h, hv, hlf, ht⟩ hf sz hs

/-- The closed-form corollary, with the readable depth budget from `StlcMeasures.lean`. -/
theorem typing_emitted_complete_depth (iS : Nat) (hlkc : LookupComplete iS)
    (Γ : List type) (τ : type) (e : term) (h : typing Γ e τ)
    (fuel sz : Nat) (hf : tdepth e < fuel) (hs : sizeMeasure e ≤ sz + 1)
    (hv : leafBound e ≤ iS) (hlf : varBound e ≤ 10000) (ht : tyNeed Γ e ≤ iS) :
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_TypingBridge_TypingBridge
      (G := SGen) fuel iS sz Γ τ) e := by
  have hdom := budget_lt_sizeMeasure e
  exact typing_emitted_complete iS hlkc Γ τ e h fuel sz hf (by omega) hv hlf ht

-- Pinned: the generic route introduces no axioms beyond `SPMF`'s classicality.
/-- info: 'TypingBridge.typing_emitted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms typing_emitted_sound

/-- info: 'TypingBridge.typing_emitted_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms typing_emitted_complete

end TypingBridge

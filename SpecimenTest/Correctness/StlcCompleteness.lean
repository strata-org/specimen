import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.STLCBasaltGenerators
import SpecimenTest.Correctness.StlcMeasures
import Specimen
import Specimen.Basalt
import Specimen.Correctness.GenInterpSPMF


/-!
# Conditional completeness of the derived STLC well-typed-term generator

Companion to `SpecimenTest/Correctness/StlcGeneratorSoundness.lean`.  Soundness says every term the
derived generator produces is well typed; this file proves the converse direction — every well-typed
term *is* reachable, provided the budgets are big enough.  Both files are statements about Basalt's
`SPMF`, the sub-probability interpretation of Basalt's `Gen` class, whose support contains exactly
what some seed could produce — so they are about the same emitted code that runs at `Plausible.Gen`,
not about a model of it.

## What is proved

Everything below is complete — no `sorry`, no new axiom, every emitted branch closed:

* `lookup_gen_complete` — the `lookup` producer.
* `type_gen_complete` (imported from `StlcMeasures.lean`) — completeness of the *unconstrained*
  derived `ArbitrarySized type` generator, which the constrained generator's `TApp` branch
  depends on.
* `stlc_gen_complete_worker` — the main theorem, by structural induction on the term.
* `stlc_gen_complete` — the headline corollary, stated at the *emitted `BacktrackGenFor` instance*
  rather than at the internal worker.
* `stlc_gen_complete_depth` — the same result with a readable closed-form size budget.
* Machine-checked non-vacuity witnesses, every hypothesis `by decide`.

## What is NOT proved

* **Tightness.**  Only the sufficient direction (`budget e ≤ sz` ⟹ reachable) is proved.
  `budget` mirrors the emitted recursion — halving at `Add`/`App`, decrementing at `Abs`, floored
  at `2` because the `size = 0` pool withholds every recursive constructor — but the current scorer
  gives recursive branches *positive literal weights* at every `size ≥ 1`, so some terms may be
  reachable one size earlier than `budget` demands.  The measure is an upper bound, proved; its
  exactness is not claimed.
* **Monotonicity in `sz`.**  Not stated and not needed: the budget hypotheses are already
  upward-closed by construction, so no combination lemma is required.
* **Anything about `Plausible.Gen` probabilities.**  Support membership says a term is *reachable*,
  not that it is reached with any particular probability, and says nothing about how many draws it
  takes.
* **Independence from the emitter's current choices.**  The proof pins the emitted branch *order*
  (`TConst, TVar, TAdd, TAbs, TApp`, selected positionally by `List.Mem.tail` chains **after** input
  dispatch has filtered the pool), the input-dispatch guards themselves, and the emitted weight
  literals that `by decide` evaluates.  Reordering emitted branches, changing `specimen.weightFn`,
  or turning `specimen.dispatchInputs` off breaks the branch and weight subgoals.  Same exposure as
  the soundness file.

## Why the budget condition is necessary

Unconditional completeness is **false**: the emitted `size = 0` branch list contains only the
non-recursive constructors (and input dispatch may filter further), so at `size = 0` nothing
recursive is reachable, and the recursion halves `size` at `Add`/`App`.  A balanced `Add` tree of
constructor depth `d` genuinely needs `size ≈ 2^d`.  Separately, `TVar` delegates to the `lookup`
producer at `initSize`, and `TConst` draws its literal at `initSize`, so the reachable de Bruijn
indices and literals are capped by the size axis too.

## The four budget axes

The emitted worker threads three numbers, and the emitted instance adds a constant:

* `size` — halved at `TAdd`/`TApp` (`Nat.div size' 2`), decremented at `TAbs` and at `lookup`'s
  `Later`.  Measured by `budget` (and by `varBound` for the delegated `lookup`).
* `initSize` — threaded through **unchanged**; it is the size the delegated `lookup` producer gets
  and the size of every unconstrained draw (`TConst`'s `Nat`, `TApp`'s argument type).  Measured by
  `leafBound` and `tyNeed`.
* `fuel` — decremented once per recursive step.  Measured by `tdepth`.
* the hard-wired `10000` that the emitted `BacktrackGenFor` instance hands the `lookup` worker as
  *its* fuel.  Measured by `varBound` again — and this is not redundant with the `initSize`
  condition: a de Bruijn index above `10000` is genuinely unreachable however large `initSize` is,
  a real (if remote) incompleteness ceiling baked into the emitter.

`budget` is kept a *linear* recurrence precisely so that `omega` — which understands `Nat.div _ 2`
and `max` natively — discharges every size side condition in one step; the closed form
`2 ^ hdepth e * (ldepth e + 2)` is exported as a corollary instead of being used as the induction
hypothesis.

## The type budget needs the term's *types*, not just the term

The deriver's schedule for `TApp` **draws** the argument type `τ1` from the unconstrained
`ArbitrarySized type` generator; there is no auxiliary pair mode synthesising `τ1` by a second
`typing` mode.  Completeness of that draw needs `typeDepth τ1 ≤ initSize`, and `τ1` is *not* a subterm of
`App e1 e2` — it is the type the derivation assigns to `e2`.  Since `typing` is syntax-directed and
deterministic, that type is computable: `outTy Γ e` recovers it, `typing_outTy` proves the recovery
correct, and `tyNeed Γ e` accumulates `typeDepth (outTy Γ e2)` over every `App` node.

## The induction

Structural on the term, with the typing derivation inverted in each case — not on fuel, because the
size budget shrinks non-uniformly; not on the derivation, because inverting `typing` per constructor
keeps `Γ` and `τ` universally quantified inside the motive, which the `TApp` case needs (it applies
the IH for `e1` at target type `Fun τ1 τ`, not at its own `τ`).  Every recursive call goes to a
strict subterm, so plain `term.rec` suffices.

## Axioms

`[propext, Classical.choice, Quot.sound]` throughout: `SPMF` is classical, and the `TConst` branches
unfold `Basalt.Nat.arbitraryGen`, a `partial_fixpoint`.  What matters is what is *absent*: no
custom axioms: the support laws these proofs use are theorems at `SPMF`.
-/

open Plausible Basalt Specimen.Correctness

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true
-- The pool-membership simp sets below are shared across every (input, size) configuration, and which
-- of their guard-reduction lemmas fire depends on which guards are present and how they evaluate.
set_option linter.unusedSimpArgs false

-- Namespaced so the derived `BacktrackGenFor` instances (whose auto-generated names are determined
-- by their types) cannot collide with another module's derivation of the same producers when the
-- whole library is built under `specimen.emitBasalt`.
namespace StlcCompleteness

#guard_msgs(warning, drop info) in
derive_mutual generator (fun Γ τ => ∃ e, typing Γ e τ)

/-! ## The measures

`budget` (size), `tdepth` (fuel), `leafBound` (lookup's and the literals' `initSize`), `varBound`
(lookup's fuel) and `typeDepth`/`outTy`/`tyNeed`
(the unconstrained type draws) are imported from `StlcMeasures.lean`, together with the closed form
`sizeMeasure` and `budget_lt_sizeMeasure` — this file and `TypingBridge.lean` prove completeness by
different routes over the same budgets, which is the cross-check that the budgets are right. -/

/-! ### Budget arithmetic, factored out so every branch is one `omega` -/

theorem need_rec_pos {a b : term} {size' : Nat}
    (h : max 2 (2 * max (budget a) (budget b) + 1) ≤ size' + 1) : size' ≠ 0 := by omega

theorem need_rec_left {a b : term} {size' : Nat}
    (h : max 2 (2 * max (budget a) (budget b) + 1) ≤ size' + 1) :
    budget a ≤ size' / 2 := by
  have := Nat.le_max_left (budget a) (budget b); omega

theorem need_rec_right {a b : term} {size' : Nat}
    (h : max 2 (2 * max (budget a) (budget b) + 1) ≤ size' + 1) :
    budget b ≤ size' / 2 := by
  have := Nat.le_max_right (budget a) (budget b); omega

theorem need_abs_body {t : type} {e : term} {size' : Nat}
    (h : budget (.Abs t e) ≤ size' + 1) : budget e ≤ size' := by
  simp only [budget] at h; omega

/-! ## The unconstrained draws -/

/-! ## The `lookup` stratum -/

/-- **Conditional completeness of the derived `lookup` producer**: every derivable index is
reachable given enough fuel and size.  Each `Later` step costs one size (the recursion decrements
`size`, and the `size = 0` pool offers only `Now`) and one fuel. -/
theorem lookup_gen_complete :
    ∀ (Γ : List type) (x : Nat) (τ : type), lookup Γ x τ →
      ∀ (iS fuel sz : Nat), x < fuel → x < sz →
      Produces (specimen_gen_lookup_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness
        (G := SGen) fuel iS sz Γ τ) x := by
  intro Γ x τ hlk
  induction hlk with
  | Now τ' Γ' =>
    intro iS fuel sz hf hs
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      cases sz with
      | zero => exact absurd hs (by omega)
      | succ sz =>
        simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
        refine produces_backtrack_of_branch _ _ (List.Mem.head _)
          (by dsimp only; decide) _ ?_
        -- The `DecOpt` side condition `τ' = τ'` answers `.ok true`, so the branch is a `pure`.
        simp only [DecOpt.decOpt]
        exact produces_pure_iff.mpr rfl
  | Later τ' τ'' n Γ' hn ih =>
    intro iS fuel sz hf hs
    cases fuel with
    | zero => exact absurd hf (by omega)
    | succ fuel =>
      cases sz with
      | zero => exact absurd hs (by omega)
      | succ sz =>
        simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
        refine produces_backtrack_of_branch _ _
          (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
        exact produces_bind_of (ih iS fuel sz (by omega) (by omega))
          (produces_pure_iff.mpr rfl)

/-! ## The main induction -/

/-- The completeness statement carried through the structural induction: for every typing of `e`,
at every sufficient budget, the worker reaches `e`. -/
def Reach (e : term) : Prop :=
  ∀ (Γ : List type) (τ : type) (iS fuel sz : Nat), typing Γ e τ →
    budget e ≤ sz → leafBound e ≤ iS → varBound e ≤ 10000 →
    tyNeed Γ e ≤ iS → tdepth e < fuel →
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness
      (G := SGen) fuel iS sz Γ τ) e

/-- **Conditional completeness of the derived well-typed-term generator.**

Structural induction on the term, with the typing derivation inverted in each case.  Because input
dispatch filters the branch pool by the target type's head constructor, each case first fixes that
constructor (by inversion where the typing rule determines it, by `cases τ` where it does not —
`TVar` and `TApp` are in every pool) and then selects its branch positionally. -/
theorem stlc_gen_complete_mutual (e : term) : Reach e := by
  induction e with
  | Const n =>
    intro Γ τ iS fuel sz hty _ hv _ _ hf
    cases hty
    case TConst =>
      cases fuel with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ fuel =>
        have body : Produces (((Basalt.ArbitrarySized.arbitrarySized iS) >>= fun n => pure (term.Const n))
            : SGen term) (term.Const n) :=
          produces_bind_of (produces_arbitrarySized_nat _ n (by simpa only [leafBound] using hv))
            (produces_pure_iff.mpr rfl)
        cases sz with
        | zero =>
          simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
          exact produces_backtrack_of_branch _ _ (List.Mem.head _)
            (by dsimp only; decide) _ body
        | succ sz =>
          simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
          exact produces_backtrack_of_branch _ _ (List.Mem.head _)
            (by dsimp only; decide) _ body
  | Var x =>
    intro Γ τ iS fuel sz hty _ hv hlf _ hf
    simp only [leafBound] at hv
    simp only [varBound] at hlf
    cases hty
    case TVar =>
      rename_i hlk
      cases fuel with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ fuel =>
        have body : Produces ((BacktrackGenFor.gen (α := Nat) (P := fun x => lookup Γ x τ)
            (G := SGen) iS iS >>= fun x => pure (term.Var x)) : SGen term)
            (term.Var x) := by
          refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
          simp only [BacktrackGenFor.gen]
          exact lookup_gen_complete _ x _ hlk iS 10000 iS (by omega) (by omega)
        -- The pool position of `TVar` depends on which other branches dispatch survived.
        cases τ with
        | Nat =>
          cases sz with
          | zero =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _
              (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ body
          | succ sz =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _
              (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ body
        | Fun τ1 τ2 =>
          cases sz with
          | zero =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _ (List.Mem.head _)
              (by dsimp only; decide) _ body
          | succ sz =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _ (List.Mem.head _)
              (by dsimp only; decide) _ body
  | Add a b iha ihb =>
    intro Γ τ iS fuel sz hty hs hv hlf ht hf
    cases hty
    case TAdd =>
      rename_i h1 h2
      cases fuel with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ fuel =>
        cases sz with
        | zero => exact absurd hs (by simp only [budget]; omega)
        | succ sz =>
          simp only [budget] at hs
          simp only [leafBound] at hv
          simp only [varBound] at hlf
          simp only [tyNeed] at ht
          simp only [tdepth] at hf
          simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
          refine produces_backtrack_of_branch _ _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by dsimp only; decide) _ ?_
          refine produces_bind_of
            (iha Γ type.Nat iS fuel (sz / 2) h1 (need_rec_left hs) (by omega) (by omega)
              (by omega) (by omega)) ?_
          exact produces_bind_of
            (ihb Γ type.Nat iS fuel (sz / 2) h2 (need_rec_right hs) (by omega) (by omega)
              (by omega) (by omega))
            (produces_pure_iff.mpr rfl)
  | Abs t body ih =>
    intro Γ τ iS fuel sz hty hs hv hlf ht hf
    cases hty
    case TAbs =>
      rename_i τ2 hbody
      cases fuel with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ fuel =>
        cases sz with
        | zero => exact absurd hs (by simp only [budget]; omega)
        | succ sz =>
          simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
          refine produces_backtrack_of_branch _ _
            (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
          refine produces_bind_of
            (ih (t :: Γ) τ2 iS fuel sz hbody (need_abs_body hs)
              (by simpa only [leafBound] using hv) (by simpa only [varBound] using hlf)
              (by simpa only [tyNeed] using ht) (by simp only [tdepth] at hf; omega))
            (produces_pure_iff.mpr rfl)
  | App a b iha ihb =>
    intro Γ τ iS fuel sz hty hs hv hlf ht hf
    cases hty
    case TApp =>
      rename_i τ1 h2 h1
      cases fuel with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ fuel =>
        cases sz with
        | zero => exact absurd hs (by simp only [budget]; omega)
        | succ sz =>
          simp only [budget] at hs
          simp only [leafBound] at hv
          simp only [varBound] at hlf
          simp only [tyNeed, typing_outTy h2, Option.elim] at ht
          simp only [tdepth] at hf
          -- The drawn argument type is exactly the one the derivation assigns to `b`.
          have hdraw : Produces ((Basalt.ArbitrarySized.arbitrarySized iS) : SGen type) τ1 :=
            type_gen_produces τ1 iS (by omega)
          have hbody :
              Produces (((Basalt.ArbitrarySized.arbitrarySized iS) >>= fun τ1 =>
                specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness
                  (G := SGen) fuel iS (sz / 2) Γ (type.Fun τ1 τ) >>= fun e1 =>
                specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness
                  (G := SGen) fuel iS (sz / 2) Γ τ1 >>= fun e2 =>
                pure (term.App e1 e2)) : SGen term) (term.App a b) := by
            refine produces_bind_of hdraw ?_
            refine produces_bind_of
              (iha Γ (type.Fun τ1 τ) iS fuel (sz / 2) h1 (need_rec_left hs) (by omega)
                (by omega) (by omega) (by omega)) ?_
            exact produces_bind_of
              (ihb Γ τ1 iS fuel (sz / 2) h2 (need_rec_right hs) (by omega) (by omega)
                (by omega) (by omega))
              (produces_pure_iff.mpr rfl)
          -- The pool position of `TApp` depends on which guarded branches dispatch kept.
          cases τ with
          | Nat =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              (by dsimp only; decide) _ hbody
          | Fun _ _ =>
            simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness]
            exact produces_backtrack_of_branch _ _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              (by dsimp only; decide) _ hbody

/-- Completeness, unpacked from the induction motive. -/
theorem stlc_gen_complete_worker (Γ : List type) (e : term) (τ : type) (h : typing Γ e τ)
    (iS fuel sz : Nat) (hs : budget e ≤ sz) (hv : leafBound e ≤ iS) (hlf : varBound e ≤ 10000)
    (ht : tyNeed Γ e ≤ iS) (hf : tdepth e < fuel) :
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_StlcCompleteness_StlcCompleteness
      (G := SGen) fuel iS sz Γ τ) e :=
  stlc_gen_complete_mutual e Γ τ iS fuel sz h hs hv hlf ht hf

/-! ## At the emitted `BacktrackGenFor` instance

The instance is `fun size leafSize => worker 10000 leafSize size …`, i.e. it sets
`initSize := leafSize` and hard-wires `fuel := 10000`.  So the axes are the size `sz`, the leaf size
`iS`, and two constant side conditions, both `by decide` for any concrete term. -/

/-- **Conditional completeness at the derived instance** — the headline statement. -/
theorem stlc_gen_complete (Γ : List type) (e : term) (τ : type) (h : typing Γ e τ) (sz iS : Nat)
    (hs : budget e ≤ sz) (hv : leafBound e ≤ iS) (ht : tyNeed Γ e ≤ iS)
    (hlf : varBound e ≤ 10000) (hfd : tdepth e < 10000) :
    Produces (BacktrackGenFor.gen (α := term) (P := fun e => typing Γ e τ) (G := SGen) sz iS) e := by
  simp only [BacktrackGenFor.gen]
  exact stlc_gen_complete_worker Γ e τ h iS 10000 sz hs hv hlf ht hfd

/-- **Closed-form conditional completeness.**  Stated with the readable depth budget
`2 ^ hdepth e * (ldepth e + 2) - 1 ≤ sz`, obtained from the exact statement for free. -/
theorem stlc_gen_complete_depth (Γ : List type) (e : term) (τ : type) (h : typing Γ e τ)
    (sz iS : Nat) (hs : sizeMeasure e ≤ sz + 1) (hv : leafBound e ≤ iS) (ht : tyNeed Γ e ≤ iS)
    (hlf : varBound e ≤ 10000) (hfd : tdepth e < 10000) :
    Produces (BacktrackGenFor.gen (α := term) (P := fun e => typing Γ e τ) (G := SGen) sz iS) e := by
  have hdom := budget_lt_sizeMeasure e
  exact stlc_gen_complete Γ e τ h sz iS (by omega) hv ht hlf hfd

/-! ## The measure on concrete terms

Pinned so the numbers quoted in the module docstring cannot drift.  These are `budget` values
only — a decidable fact about the measure.  (The measure is a proved *upper* bound on the producing
size, not necessarily the smallest one: the scorer keeps recursive weights positive at `size ≥ 1`, so
the two can be one apart.) -/

#guard budget (term.Const 0) = 0
#guard budget (term.Var 1) = 0
#guard budget (term.Abs type.Nat (term.Var 0)) = 2
#guard budget (term.Add (term.Const 0) (term.Const 0)) = 2
#guard budget (term.Add (term.Add (term.Const 0) (term.Const 0)) (term.Const 0)) = 5
#guard budget (term.App (term.Abs type.Nat (term.Const 0)) (term.Const 0)) = 5
#guard budget (term.Abs type.Nat (term.Add (term.Var 0) (term.Const 0))) = 3
#guard budget
  (term.Abs type.Nat (term.Add (term.Add (term.Var 0) (term.Var 0)) (term.Var 0))) = 6
-- The `leafBound` axis is independent of `budget`: `Var 1` needs `sz ≥ 2` for the *index*, and
-- `Const 7` needs `sz ≥ 7` for the literal, though both have size requirement `0`.
#guard leafBound (term.Var 1) = 2
#guard leafBound (term.Const 7) = 7
#guard tdepth (term.App (term.Abs type.Nat (term.Const 0)) (term.Const 0)) = 2
-- The `TApp` type draw is budgeted from the argument's computed type.
#guard tyNeed [] (term.App (term.Abs (type.Fun type.Nat type.Nat) (term.Const 0))
  (term.Abs type.Nat (term.Var 0))) = 1
-- The closed-form budget over-approximates the exact one; here by 6 vs 5.
#guard sizeMeasure (term.App (term.Abs type.Nat (term.Const 0)) (term.Const 0)) = 6

/-! ## Non-vacuity

Every hypothesis is `by decide` for a concrete term, so these are unconditional theorems about the
derived generator's support.  The sizes used are the `budget` values pinned just above. -/

/-- `Abs Nat (Var 0) : Nat → Nat` at exactly `budget = 2`. -/
example :
    Produces (BacktrackGenFor.gen (α := term)
      (P := fun e => typing [] e (type.Fun type.Nat type.Nat)) (G := SGen) 2 2)
      (term.Abs type.Nat (term.Var 0)) :=
  stlc_gen_complete [] _ _
    (typing.TAbs [] (term.Var 0) type.Nat type.Nat
      (typing.TVar [type.Nat] 0 type.Nat (lookup.Now type.Nat [])))
    2 2 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `Add (Const 0) (Const 0) : Nat` — a halving branch — at exactly `budget = 2`. -/
example :
    Produces (BacktrackGenFor.gen (α := term) (P := fun e => typing [] e type.Nat)
      (G := SGen) 2 2) (term.Add (term.Const 0) (term.Const 0)) :=
  stlc_gen_complete [] _ _
    (typing.TAdd [] (term.Const 0) (term.Const 0) (typing.TConst [] 0) (typing.TConst [] 0))
    2 2 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `App (Abs Nat (Const 0)) (Const 0) : Nat` — the branch whose argument type is *drawn* — at
exactly `budget = 5`. -/
example :
    Produces (BacktrackGenFor.gen (α := term) (P := fun e => typing [] e type.Nat)
      (G := SGen) 5 5) (term.App (term.Abs type.Nat (term.Const 0)) (term.Const 0)) :=
  stlc_gen_complete [] _ _
    (typing.TApp [] (term.Abs type.Nat (term.Const 0)) (term.Const 0) type.Nat type.Nat
      (typing.TConst [] 0)
      (typing.TAbs [] (term.Const 0) type.Nat type.Nat (typing.TConst [type.Nat] 0)))
    5 5 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The `leafBound` axis in isolation: `budget (Var 1) = 0`, yet index `1` needs `sz ≥ 2`. -/
example :
    Produces (BacktrackGenFor.gen (α := term)
      (P := fun e => typing [type.Nat, type.Fun type.Nat type.Nat] e
        (type.Fun type.Nat type.Nat)) (G := SGen) 2 2) (term.Var 1) :=
  stlc_gen_complete _ _ _
    (typing.TVar _ 1 _
      (lookup.Later _ type.Nat 0 _ (lookup.Now (type.Fun type.Nat type.Nat) [])))
    2 2 (by decide) (by decide) (by decide) (by decide) (by decide)

-- Pinned: only Lean's standard axioms. `Classical.choice` comes from `SPMF` and the `partial_fixpoint`
-- unfolding.
/-- info: 'StlcCompleteness.stlc_gen_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stlc_gen_complete

/-- info: 'StlcCompleteness.lookup_gen_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_gen_complete

end StlcCompleteness

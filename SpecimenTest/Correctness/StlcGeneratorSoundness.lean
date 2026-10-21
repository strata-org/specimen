import SpecimenTest.CommonDefinitions.STLCDefinitions
import SpecimenTest.CommonDefinitions.STLCBasaltGenerators
import Specimen
import Specimen.Basalt
import Specimen.Correctness.GenInterpSPMF

/-!
# Soundness of the derived STLC well-typed-term generator

`derive_mutual generator (fun G t => ∃ e, typing G e t)` produces a generator for well-typed
simply-typed lambda terms. This file proves that generator **sound**: every term it can produce
really is well typed.

    stlc_gen_sound :
      Produces (BacktrackGenFor.gen (P := fun e => typing G e t) …) e → typing G e t

Nothing here is a transcription: the statements are about the `BacktrackGenFor` instance the deriver
actually emits, so this file is also a regression guard on emission *shape* — change how generators
are emitted and the proof stops compiling.

## Why the `SPMF` interpretation

The emitted worker is polymorphic in the generator monad. Instantiated at `SGen` (Basalt's `SPMF`
under the sampler's `OptionT` and `ExceptT`) it denotes a sub-probability distribution over outcomes,
and `Produces g x` says `x` is a success in the distribution's *support* — producible with nonzero
probability, whatever the seed. Basalt's search lemmas decompose that support through the `backtrack`
every derived generator is built from, and `Specimen.Correctness.GenInterpSPMF` packages them, with
the `bind`/`pure` steps, as a `Produces` algebra. So "sound at `SPMF`" is the strong, seed-independent statement.

## Structure of the proof

`autoDeriveDeps` emits **two** workers, and their call graph decides the proof shape:

| worker | recurses into |
|---|---|
| `lookup_1` (Γ, τ in; index out)  | itself |
| `typing_1` (Γ, τ in; term out)   | `lookup_1`, itself |

Each gets its own `induction fuel`. The schedule the deriver picks for `TApp` draws the argument
type `τ1` from the *unconstrained* `ArbitrarySized type` and then produces both subterms through
`typing_1` itself — there is no auxiliary pair mode (`typing_1_2`) and therefore no simultaneous
induction. (A scorer that scheduled `TApp` through a pair mode would force a mutual induction over
both modes; the single-mode schedule keeps the proof to one.)

The `typing → lookup` edge does **not** join the cycle: those calls go through the emitted
`BacktrackGenFor` instance, whose `gen` field is `fun size leafSize => worker 10000 leafSize size args`, resetting
fuel to the literal `10000`. That is why the `lookup` lemma is quantified over all fuel and is then
applied at `10000`.

## Input dispatch shapes the pools

`specimen.dispatchInputs` (on by default) emits each branch whose conclusion constrains an *input*
behind a guard — `if (match c_1 with | type.Nat => true | _ => false) then some (w, branch) else
none` — and the pool is `List.filterMap id` over those options, so a branch whose guard fails is not
in the pool at all. The proofs therefore case on the dispatching input (`Γ` for `lookup`, the target
type `t` for `typing`) *before* decomposing pool membership; with the input a literal constructor,
the guards and the `filterMap` reduce and membership is a plain `List.mem_cons` disjunction.

## Three things that are load-bearing

* **Every statement quantifies over `initSize` and `size` separately from `fuel`.** `TAdd`/`TApp`
  recurse at `Nat.div size' 2` and `TAbs` at `size'` unchanged, so no monotone relation to `fuel`
  exists; only `fuel` decrements, which is what the induction uses.
* **`TVar` bottoms out in the derived `lookup` producer**, invoked at `initSize`, so the `lookup`
  lemma is a genuine dependency rather than a side result.
* **`STLCBasaltGenerators` must be imported.** `TConst` draws its literal and `TApp` its argument
  type from an unconstrained `Basalt.ArbitrarySized`; without those instances the *derivation*
  fails before any proof is attempted.

## Generic machinery this leans on

* `produces_backtrack_ok` — a success in `backtrack gs` came from some branch of
  `gs`. It is weight-agnostic, so soundness never has to evaluate a weight term.
* `produces_truncated_iff` — the `size = 0` pool's truncation branches produce nothing.
* `Produces` and its algebra (`produces_bind_iff`, `produces_pure_iff`, `not_produces_refute`)
  from `GenInterpSPMF` — each `do` bind in a branch decomposes through
  these instead of through raw `SPMF` support reasoning.
* `Specimen.DecOpt`'s `[Decidable P]` instance, consumed via `of_decide_eq_true` — the single side
  condition in the whole component is `lookup_1`'s `τ₁ = τ` check.
* `produces_backtrack_of_branch` — the converse, used *only* by the non-vacuity
  witnesses at the end of the file.

## Non-vacuity is proved too

`stlc_gen_nonvacuous` and `stlc_gen_nonvacuous_abs` exhibit members of the very supports the theorems
quantify over — the second one through the *recursive* `TAbs` branch — so the hypothesis is
satisfiable and the theorem is not vacuously true.

## Scope: what is *not* proved here

* **Completeness** is not proved here; `TypingBridge.lean` proves it through the generic interpreter.
* **Soundness at `Plausible.Gen`**, the interpretation the tests execute at, is not proved. It would
  need a separate adequacy result relating that interpretation to `SPMF`. What *is* proved covers
  every seed a run could use: the `SPMF` support contains everything any seed can produce.

## Requires `specimen.emitBasalt`

Set in-file, deliberately: these theorems are *about* the Basalt-targeted generator, which only
exists on that emission path.

## A note on the worker names

`specimen_gen_*` names embed the declaring module, so they change if this file moves. Rediscover them
by stating the goal against `BacktrackGenFor.gen`, applying `simp only [BacktrackGenFor.gen]`, and
reading the name off the goal with `trace_state`.
-/

open Plausible Basalt Specimen.Correctness

-- Set explicitly rather than inherited from the build: this proof is *about* the Basalt-targeted
-- generator, so it must be derived as `BacktrackGenFor` regardless of the library-wide flag. Built
-- flag-off without this, the derive emits Plausible-shaped code, `G` resolves to `Plausible.Gen`, and
-- every statement here becomes ill-typed.
set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true
-- The pool-membership simp set below is shared across every (input, size) configuration, and which
-- of its guard-reduction lemmas fire depends on which guards are present and how they evaluate.
set_option linter.unusedSimpArgs false

-- Namespaced so the derived `BacktrackGenFor` instances (whose auto-generated names are determined
-- by their types) cannot collide with another module's derivation of the same producers when the
-- whole library is built under `specimen.emitBasalt`.
namespace StlcGeneratorSoundness

#guard_msgs(warning, drop info) in
derive_mutual generator (fun G t => ∃ e, typing G e t)

/-! ## The `lookup` stratum

Self-recursive only, so it gets its own `induction fuel`. It draws no unconstrained value.
-/

/-- Soundness of the derived `lookup` producer: context and type in, de Bruijn index out.
This mode carries the only `DecOpt` side condition in the whole component (`Now`'s `τ₁ = τ`). -/
theorem lookup_gen_sound : ∀ (fuel iS sz : Nat) (Γ : List type) (τ : type) (x : Nat),
    Produces (specimen_gen_lookup_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness
        (G := SGen) fuel iS sz Γ τ) x →
    lookup Γ x τ := by
  intro fuel
  induction fuel with
  | zero =>
    intro iS sz Γ τ x h
    simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness] at h
    exact absurd h (not_produces_outOfFuel x)
  | succ fuel ih =>
    intro iS sz Γ τ x h
    simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness] at h
    -- Dispatch: both branches are guarded on `Γ` being a cons, so with `Γ = []` the pool is empty.
    cases Γ with
    | nil =>
      cases sz with
      | zero =>
        obtain ⟨q, hq, _, _⟩ := produces_backtrack_ok _ x
          h
        simp at hq
      | succ sz =>
        obtain ⟨q, hq, _, _⟩ := produces_backtrack_ok _ x h
        simp at hq
    | cons τ_1 Γ' =>
      -- `Now`, shared by the truncated `size = 0` pool and the full pool.
      have now_branch :
          Produces (match @DecOpt.decOpt (τ_1 = τ) inferInstance iS with
            | Except.ok true => (pure Nat.zero : SGen Nat)
            | Except.ok false => Specimen.refute
            -- The third arm is `inconclusive`, not `refute`: `DecOpt` is three-valued and an
            -- inconclusive check must not be reported as a definite refutation. Dead for a
            -- `Decidable`-derived instance like this one, which always answers `ok`.
            | _ => Specimen.inconclusive) x → lookup (τ_1 :: Γ') x τ := by
        intro hqa
        simp only [DecOpt.decOpt] at hqa
        cases hdec : decide (τ_1 = τ) with
        | false =>
          simp only [hdec] at hqa
          exact absurd hqa (not_produces_refute x)
        | true =>
          simp only [hdec] at hqa
          cases produces_pure_iff.mp hqa
          cases of_decide_eq_true hdec
          exact lookup.Now τ Γ'
      cases sz with
      | zero =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ x
          h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact now_branch hqa
        · simp at hqa
      | succ sz =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ x h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact now_branch hqa
        · -- `Later`: one self-call on the tail, at the decremented fuel.
          obtain ⟨n, hn, he⟩ := produces_bind_iff.mp hqa
          cases produces_pure_iff.mp he
          exact lookup.Later τ τ_1 n Γ' (ih iS sz Γ' τ n hn)

/-! ## The `typing` stratum

Also self-recursive only under the single-mode schedule: `TApp` draws `τ1` unconstrained and recurses
into this same mode at `Fun τ1 t` and at `τ1`. The two base branches differ in dispatch: `TConst` is
guarded on the target type being `Nat`, `TVar` is unguarded.
-/

/-- Soundness of the derived `typing` generator: context and type in, term out. -/
theorem typing_gen_sound : ∀ (fuel iS sz : Nat) (G : List type) (t : type) (e : term),
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness
        (G := SGen) fuel iS sz G t) e →
    typing G e t := by
  intro fuel
  induction fuel with
  | zero =>
    intro iS sz G t e h
    simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness] at h
    exact absurd h (not_produces_outOfFuel e)
  | succ fuel ih =>
    intro iS sz G t e h
    simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness] at h
    -- `TConst` at `t = Nat`, shared by the truncated and the full pool.
    have tconst :
        Produces (((Basalt.ArbitrarySized.arbitrarySized iS) >>= fun n => pure (term.Const n))
            : SGen term) e → typing G e type.Nat := by
      intro hqa
      obtain ⟨n, _, he⟩ := produces_bind_iff.mp hqa
      cases produces_pure_iff.mp he
      exact typing.TConst G n
    -- `TVar`, unguarded, in both pools and at every target type: the delegated `lookup` producer at
    -- the emitted instance's literal fuel `10000`.
    have tvar : ∀ t,
        Produces ((BacktrackGenFor.gen (α := Nat) (P := fun x => lookup G x t) (G := SGen) iS iS
            >>= fun x => pure (term.Var x)) : SGen term) e → typing G e t := by
      intro t hqa
      obtain ⟨x, hx, he⟩ := produces_bind_iff.mp hqa
      cases produces_pure_iff.mp he
      -- `simp only [BacktrackGenFor.gen]` reduces the emitted instance to the `lookup` worker at
      -- the literal fuel `10000`; the instance itself never has to be named.
      simp only [BacktrackGenFor.gen] at hx
      exact typing.TVar G x t (lookup_gen_sound 10000 iS iS G t x hx)
    -- Dispatch: `TConst`/`TAdd` are guarded on `t = Nat`, `TAbs` on `t = Fun _ _`, so the pool's
    -- shape depends on `t`'s head constructor; case on it before decomposing membership.
    cases t with
    | Nat =>
      cases sz with
      | zero =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ _
          h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact tconst hqa
        · exact tvar _ hqa
        · simp at hqa
        · simp at hqa
      | succ sz =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ _ h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact tconst hqa
        · exact tvar _ hqa
        · -- TAdd: two self-calls at HALVED size; `ih` is quantified over size, so that is fine.
          obtain ⟨e1, h1, hrest⟩ := produces_bind_iff.mp hqa
          obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest
          cases produces_pure_iff.mp he
          exact typing.TAdd G e1 e2 (ih _ _ _ _ _ h1) (ih _ _ _ _ _ h2)
        · -- TApp: `τ1` is drawn unconstrained, then both subterms come from this same mode.
          obtain ⟨τ1, _, hrest⟩ := produces_bind_iff.mp hqa
          obtain ⟨e1, h1, hrest2⟩ := produces_bind_iff.mp hrest
          obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest2
          cases produces_pure_iff.mp he
          exact typing.TApp G e1 e2 τ1 type.Nat (ih _ _ _ _ _ h2) (ih _ _ _ _ _ h1)
    | Fun τ1 τ2 =>
      cases sz with
      | zero =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ _
          h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact tvar _ hqa
        · simp at hqa
        · simp at hqa
      | succ sz =>
        obtain ⟨q, hq, _, hqa⟩ := produces_backtrack_ok _ _ h
        simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, eq_self_iff_true,
          ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact tvar _ hqa
        · -- TAbs: one self-call at the *unchanged* size, in the extended context.
          obtain ⟨e0, h0, he⟩ := produces_bind_iff.mp hqa
          cases produces_pure_iff.mp he
          exact typing.TAbs G e0 τ1 τ2 (ih _ _ _ _ _ h0)
        · -- TApp at a function target type, same shape as at `Nat`.
          obtain ⟨τ0, _, hrest⟩ := produces_bind_iff.mp hqa
          obtain ⟨e1, h1, hrest2⟩ := produces_bind_iff.mp hrest
          obtain ⟨e2, h2, he⟩ := produces_bind_iff.mp hrest2
          cases produces_pure_iff.mp he
          exact typing.TApp G e1 e2 τ0 _ (ih _ _ _ _ _ h2) (ih _ _ _ _ _ h1)

/-! ## User-facing statements

Stated against `BacktrackGenFor.gen` — the interface a caller actually uses — rather than against the
emitted worker. `simp only [BacktrackGenFor.gen]` reduces the instance to `worker 10000 leaf sz args`,
which is where the literal fuel `10000` comes from.
-/

/-- **Soundness of the derived well-typed-term generator.** Every term the generator for
`fun e => typing G e t` can produce, at the `SPMF` interpretation and at any size and leaf size,
really has type `t` in context `G`. -/
theorem stlc_gen_sound (G : List type) (t : type) (sz leaf : Nat) (e : term)
    (h : Produces (BacktrackGenFor.gen (P := fun e => typing G e t) (G := SGen) sz leaf) e) :
    typing G e t := by
  simp only [BacktrackGenFor.gen] at h
  exact typing_gen_sound 10000 leaf sz G t e h

/-- Soundness of the derived `lookup` producer, at the `BacktrackGenFor` interface. -/
theorem lookup_gen_sound' (G : List type) (t : type) (sz leaf : Nat) (x : Nat)
    (h : Produces (BacktrackGenFor.gen (P := fun x => lookup G x t) (G := SGen) sz leaf) x) :
    lookup G x t := by
  simp only [BacktrackGenFor.gen] at h
  exact lookup_gen_sound 10000 leaf sz G t x h

/-! ## Non-vacuity

A soundness theorem is worthless if its hypothesis is unsatisfiable, so the support really is shown
to be inhabited — and not only in the truncated `size = 0` pool: `stlc_gen_nonvacuous_abs` goes
through the *recursive* `TAbs` branch. This is the completeness direction, which is why these are the
only proofs in the file that use `produces_backtrack_of_branch` and therefore the
only ones that have to evaluate a branch weight (`by decide`).
-/

/-- The `lookup.Now` branch really is reachable, at every fuel, `initSize` and `size`. -/
theorem lookup_now_witness (fuel iS sz : Nat) (τ : type) (Γ : List type) :
    Produces (specimen_gen_lookup_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness
        (G := SGen) (fuel + 1) iS sz (τ :: Γ) τ) 0 := by
  simp only [specimen_gen_lookup_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness]
  cases sz with
  | zero =>
    refine produces_backtrack_of_branch _ _ (List.Mem.head _)
      (by dsimp only; decide) _ ?_
    -- The `DecOpt` side condition `τ = τ` answers `.ok true`, so the branch is a `pure`.
    simp only [DecOpt.decOpt]
    exact produces_pure_iff.mpr rfl
  | succ sz =>
    refine produces_backtrack_of_branch _ _ (List.Mem.head _)
      (by dsimp only; decide) _ ?_
    simp only [DecOpt.decOpt]
    exact produces_pure_iff.mpr rfl

/-- The `typing.TVar` branch really is reachable, at every fuel, `initSize` and `size`; it bottoms
out in the delegated `lookup` producer at the literal fuel `10000`. -/
theorem typing_var_witness (fuel iS sz : Nat) (τ : type) (Γ : List type) :
    Produces (specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness
        (G := SGen) (fuel + 1) iS sz (τ :: Γ) τ) (term.Var 0) := by
  simp only [specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness]
  cases τ with
  | Nat =>
    cases sz with
    | zero =>
      refine produces_backtrack_of_branch _ _
        (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
      refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
      simp only [BacktrackGenFor.gen]
      exact lookup_now_witness 9999 iS iS type.Nat Γ
    | succ sz =>
      refine produces_backtrack_of_branch _ _
        (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
      refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
      simp only [BacktrackGenFor.gen]
      exact lookup_now_witness 9999 iS iS type.Nat Γ
  | Fun τ1 τ2 =>
    cases sz with
    | zero =>
      refine produces_backtrack_of_branch _ _ (List.Mem.head _)
        (by dsimp only; decide) _ ?_
      refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
      simp only [BacktrackGenFor.gen]
      exact lookup_now_witness 9999 iS iS (type.Fun τ1 τ2) Γ
    | succ sz =>
      refine produces_backtrack_of_branch _ _ (List.Mem.head _)
        (by dsimp only; decide) _ ?_
      refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
      simp only [BacktrackGenFor.gen]
      exact lookup_now_witness 9999 iS iS (type.Fun τ1 τ2) Γ

/-- `stlc_gen_sound`'s hypothesis is satisfiable: the generator for `[Nat] ⊢ ? : Nat` can produce
`Var 0` already at size `0`. -/
theorem stlc_gen_nonvacuous :
    Produces (BacktrackGenFor.gen (P := fun e => typing [type.Nat] e type.Nat)
        (G := SGen) 0 0) (term.Var 0) := by
  simp only [BacktrackGenFor.gen]
  exact typing_var_witness 9999 0 0 type.Nat []

/-- …and satisfiable through a *recursive* branch: at size `2` the generator for
`[] ⊢ ? : Nat → Nat` can produce `λx:Nat. x`, via `TAbs` over `TVar` over `lookup.Now`. So the
soundness theorem is not confined to the base constructors. -/
theorem stlc_gen_nonvacuous_abs :
    Produces (BacktrackGenFor.gen (P := fun e => typing [] e (type.Fun type.Nat type.Nat))
        (G := SGen) 2 2) (term.Abs type.Nat (term.Var 0)) := by
  simp only [BacktrackGenFor.gen,
    specimen_gen_typing_1__SpecimenTest_Correctness_StlcGeneratorSoundness_StlcGeneratorSoundness]
  refine produces_backtrack_of_branch _ _
    (List.Mem.tail _ (List.Mem.head _)) (by dsimp only; decide) _ ?_
  refine produces_bind_of ?_ (produces_pure_iff.mpr rfl)
  exact typing_var_witness 9998 2 1 type.Nat []

/-- The payoff, spelled out: soundness applied to a witness yields a real typing judgement. -/
example : typing [type.Nat] (term.Var 0) type.Nat :=
  stlc_gen_sound [type.Nat] type.Nat 0 0 (term.Var 0) stlc_gen_nonvacuous

example : typing [] (term.Abs type.Nat (term.Var 0)) (type.Fun type.Nat type.Nat) :=
  stlc_gen_sound [] (type.Fun type.Nat type.Nat) 2 2 _ stlc_gen_nonvacuous_abs

/-- info: 'StlcGeneratorSoundness.stlc_gen_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stlc_gen_sound

/-- info: 'StlcGeneratorSoundness.lookup_gen_sound'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_gen_sound'

/-- info: 'StlcGeneratorSoundness.stlc_gen_nonvacuous_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stlc_gen_nonvacuous_abs

end StlcGeneratorSoundness

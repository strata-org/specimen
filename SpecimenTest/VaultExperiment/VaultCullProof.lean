import SpecimenTest.VaultExperiment.VaultUnrolledAll

open Plausible

-- Several culling lemmas below state a constructor's premise block verbatim and
-- prove `False`; `simp_all` often closes them from a subset of the hypotheses,
-- so the rest are reported unused. That is expected (Lean finds the minimal
-- contradiction), not a defect.
set_option linter.unusedVariables false

namespace Vault

/-!
# Proof-of-concept: culling unsatisfiable step-combinations with Lean itself

`VaultUnrolledAll` emits `b^k` constructors (II, IR, RI, RR) and eliminates the
infeasible ones only at *runtime*, by backtracking. This file shows the
elimination can be moved to *derivation time* by asking **Lean** to prove a
combination's inlined premises are jointly unsatisfiable — the exact
theorem-proving goal a static-pruning pass would discharge.

Each combination's premise block is a conjunction of equations over the state
variables (and the linking arithmetic). "This combination is dead" is precisely
"the premises entail `False`". We phrase that as a lemma and try to close it with
a general-purpose tactic. If the tactic succeeds, a pruning pass would drop the
constructor before generating any code for it.

Two flavors of deadness, matching §5 of the write-up:
  * start-INDEPENDENT: contradictory regardless of the start state (II, RR).
  * start-DEPENDENT: consistent in isolation, but contradicts a *given* start
    (RI, once we fix the generator's start state to `none`).
-/

--------------------------------------------------------------------------------
-- 1. Start-independent deadness: II and RR are contradictory for ANY start `s`.
--
-- The premise block of `II` binds `sa = some t1` and `sa = none`; likewise `RR`
-- binds `sa = none` and `sa = some (sq k2)`. These are contradictory on their
-- own. We state exactly the premise conjunction and ask Lean to derive `False`.
--------------------------------------------------------------------------------

-- II premises, verbatim, with the target `False`.
theorem II_dead
    (s sa sb : Vault) (t1 t2 : Nat)
    (h1 : s = none) (h2 : sa = some t1)
    (h3 : sa = none) (h4 : sb = some t2) : False := by
  simp_all

-- RR premises, verbatim.
theorem RR_dead
    (s sa sb : Vault) (k1 k2 : Nat)
    (h1 : s = some (sq k1)) (h2 : sa = none)
    (h3 : sa = some (sq k2)) (h4 : sb = none) : False := by
  simp_all

--------------------------------------------------------------------------------
-- 2. Start-dependent deadness: RI is consistent in isolation, but if the
-- generator's start state is `none`, RI's `s = some (sq k1)` is impossible.
--
-- A pruning pass parameterized by a known start state would discharge this.
--------------------------------------------------------------------------------

theorem RI_dead_from_none
    (s sa sb : Vault) (k1 t2 : Nat)
    (hstart : s = none)                 -- the generator's start state
    (h1 : s = some (sq k1)) (h2 : sa = none)
    (h3 : sa = none) (h4 : sb = some t2) : False := by
  simp_all

-- ...but RI is NOT dead in general: from a `some (sq _)` start it is realizable.
-- We confirm the premises are satisfiable by exhibiting a witness, so a sound
-- pruning pass must NOT cull RI unconditionally.
example : ∃ (s sa sb : Vault) (k1 t2 : Nat),
    s = some (sq k1) ∧ sa = none ∧ sa = none ∧ sb = some t2 :=
  ⟨some (sq 3), none, some 7, 3, 7, rfl, rfl, rfl, rfl⟩

--------------------------------------------------------------------------------
-- 3. The survivor: IR's premises ARE jointly satisfiable (with the forward-
-- functional link `t = sq k`). A pruning pass must keep IR. We show the premise
-- block has a model, so no `False` proof exists to cull it.
--------------------------------------------------------------------------------

example : ∃ (s sa sb : Vault) (t k : Nat),
    s = none ∧ sa = some t ∧ sa = some (sq k) ∧ sb = none :=
  -- choose k = 4, t = sq 4 = 16, so `sa = some 16 = some (sq 4)` holds.
  ⟨none, some (sq 4), none, sq 4, 4, rfl, rfl, rfl, rfl⟩

/-!
## What this shows

The culling decision for a step-combination is a **closed first-order goal over
the inlined premises**, and the goals arising here are exactly the kind Lean's
automation closes without help:

  * `II_dead`, `RR_dead`  — `simp_all` (contradictory equalities on an inductive
    datatype: `some _ = none`).
  * `RI_dead_from_none`   — same, once a start state is assumed.

So a derivation-time pruning pass could, for each of the `b^k` candidate
constructors, assemble its premise conjunction and invoke a tactic
(`simp_all` / `omega` / `decide`, escalating as needed) to *try* to prove
`premises → False`:

  * **proof found**  → the combination is dead; emit no generator for it.
  * **no proof / countermodel** → keep it (as IR and the satisfiable RI witness
    show, we must not cull these).

This is sound by construction: we only drop a constructor when Lean has *proved*
it can never fire. It leans on Lean-as-prover exactly where §5 wanted, and it
degrades gracefully — an undecidable or timed-out goal simply means "keep the
constructor", falling back to today's runtime backtracking for that one.
-/

end Vault

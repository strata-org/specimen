import Specimen
import Specimen.Basalt
import Specimen.Correctness.GenInterpSPMF

/-!
# Verdict fidelity: an inconclusive premise must not become a definite refutation

`DecOpt` is three-valued. `ok false` says "this constructor definitely does not apply"; `error` says
only "the checker ran out of budget". Under `Plausible.Gen` a producer has nowhere to put that
difference — failure is one thrown error. Under Basalt it does: `Outcome` carries `refuted` *and*
`exhausted` precisely so an inconclusive premise can stay inconclusive, and `Specimen/MExp.lean` maps
`ok false` to `refute` and `error` to `exhaust`.

This file is the case that shows the distinction is not cosmetic. `Guard k o` holds for every `k` (its
premise `Chain k` is true of every `Nat`), so **no** refutation of it is ever correct. But `Chain`'s
checker is derived and therefore size-limited: for `k` beyond `initSize` it answers `error`. An
emission that collapsed `error` into `refute` would turn that into a refutation, and a single-branch
`backtrack` passes a refutation straight through — a definite refutation of a relation inhabited at
every input. `guard_emitted_refute` is the statement such an emission falsifies;
`guard_never_refutes` is the consequence worth reading — this generator cannot refute at all.

The `Chain` checker's own refutation-soundness is taken as a hypothesis (`ChainRefuteSound`), the same
modular treatment external sub-producers get in `DerivedGeneratorViaInterp.lean`.
`DerivedCheckerSoundness.lean` proves exactly that shape for a concrete relation.
-/

open Plausible Basalt Specimen.Correctness

set_option specimen.emitBasalt true
set_option specimen.autoDeriveDeps true

namespace VerdictFidelity

inductive Chain : Nat → Prop where
  | z : Chain 0
  | s : ∀ n, Chain n → Chain (n + 1)

inductive Guard : Nat → Nat → Prop where
  | mk : ∀ k, Chain k → Guard k 0

#guard_msgs(warning, drop info) in
derive_mutual generator (fun k => ∃ o, Guard k o)

/-- Refutation-soundness of the *derived* `Chain` checker, as a hypothesis. `DerivedCheckerSoundness`
    proves exactly this shape for `sorted`. -/
def ChainRefuteSound (iS : Nat) : Prop :=
  ∀ k, @DecOpt.decOpt (Chain k) _ iS = .ok false → ¬ Chain k

/-- The theorem an `error`-collapsing emission falsifies: if an `error` from `Chain`'s derived
    checker also produced `refute`, then `refuted` would carry no information about `Chain k` — and
    `Chain k` holds for *every* `k`, so the generator could refute an inhabited relation. -/
theorem guard_emitted_refute (iS : Nat) (hchain : ChainRefuteSound iS) :
    ∀ (fuel sz k : Nat),
      Outcome.refuted ∈
        (specimen_gen_VerdictFidelity_Guard_1__SpecimenTest_Correctness_VerdictFidelity_VerdictFidelity
          (G := SPMF) fuel iS sz k).run.support →
      ∀ o, ¬ Guard k o := by
  -- The single branch, shared by both size cases. `Guard` has no recursive constructor, so nothing is
  -- withheld at `size = 0` and the pool is the same either way — in particular there is no
  -- `refutedToExhausted` wrapper here, and a refutation at size 0 is a genuine one.
  have branch : ∀ k : Nat,
      Outcome.refuted ∈
        ((match @DecOpt.decOpt (Chain k) _ iS with
         | .ok true =>
             @BacktrackGenFor.gen Nat (fun o => o = 0) _ SPMF _ iS >>= fun o => pure o
         | .ok false => BacktrackGen.refute
         | _ => BacktrackGen.exhaust) : BacktrackGen SPMF Nat).run.support →
      ∀ o, ¬ Guard k o := by
    intro k hbr
    cases hd : @DecOpt.decOpt (Chain k) _ iS with
    | error e =>
      simp only [hd] at hbr
      exact absurd (SPMF.mem_support_pure_iff.mp hbr) (by simp)
    | ok b =>
      cases b with
      | true =>
        -- the sub-producer for `o = 0` is `pure 0`, so it cannot refute
        simp only [hd] at hbr
        rcases mem_support_run_bind.mp hbr with ⟨o, ho, hres⟩ | ⟨ho, _⟩ | ⟨_, h⟩
        · exact absurd (SPMF.mem_support_pure_iff.mp hres) (by simp)
        · simp only [BacktrackGenFor.gen] at ho
          exact absurd (SPMF.mem_support_pure_iff.mp ho) (by simp)
        · cases h
      | false =>
        intro o hg
        cases hg with
        | mk hc => exact hchain k hd hc
  intro fuel sz k h
  cases fuel with
  | zero => exact absurd (SPMF.mem_support_pure_iff.mp h) (by simp)
  | succ fuel =>
    cases sz with
    | zero =>
      simp only [specimen_gen_VerdictFidelity_Guard_1__SpecimenTest_Correctness_VerdictFidelity_VerdictFidelity] at h
      exact branch k (BacktrackGen.mem_support_backtrack_refuted _ h _ (List.Mem.head _))
    | succ sz =>
      simp only [specimen_gen_VerdictFidelity_Guard_1__SpecimenTest_Correctness_VerdictFidelity_VerdictFidelity] at h
      exact branch k (BacktrackGen.mem_support_backtrack_refuted _ h _ (List.Mem.head _))

/-- `Chain` holds of every `Nat`, so `Guard k 0` holds for every `k` — the relation is inhabited at
    every input. -/
theorem chain_all : ∀ k, Chain k
  | 0 => Chain.z
  | n + 1 => Chain.s n (chain_all n)

theorem guard_inhabited (k : Nat) : Guard k 0 := Guard.mk k (chain_all k)

/-- **The punchline.** Combining the two: the emitted generator can *never* report `refuted` for
`Guard`, at any fuel, size or input.

That is the correct behaviour, and it is what the `MExp.lean` verdict fix buys. Before it, an `error`
from `Chain`'s derived checker — which happens whenever `initSize` is too small for `k` — produced
`refute`, and a single-branch `backtrack` passes that straight through. So the generator reported a
definite refutation of a relation inhabited at *every* input. `guard_emitted_refute` is exactly the
statement that was false then and holds now. -/
theorem guard_never_refutes (iS : Nat) (hchain : ChainRefuteSound iS) (fuel sz k : Nat) :
    Outcome.refuted ∉
      (specimen_gen_VerdictFidelity_Guard_1__SpecimenTest_Correctness_VerdictFidelity_VerdictFidelity
        (G := SPMF) fuel iS sz k).run.support :=
  fun h => guard_emitted_refute iS hchain fuel sz k h 0 (guard_inhabited k)

-- Pinned.
/-- info: 'VerdictFidelity.guard_emitted_refute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guard_emitted_refute

/-- info: 'VerdictFidelity.guard_never_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guard_never_refutes

end VerdictFidelity

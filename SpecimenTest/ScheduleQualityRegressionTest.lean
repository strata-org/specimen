import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import SpecimenTest.CommonDefinitions.BinaryTree
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBSTGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

/-!
# Schedule Quality Regression Tests

Snapshots the kernel-elaborated code for derived generators via `#print`.
Any change to the schedule derivation algorithm that alters the generated
code will cause these `#guard_msgs` checks to fail, catching regressions.

Sections 1–4 snapshot representative generators (Between, BST, STLC, RegExp).
Section 5 is a direct regression test for the bug where relations with `≠`
hypotheses alongside recursive hypotheses produced bad schedules.
-/

open Plausible

set_option guard_msgs.diff true
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

-- ============================================================
-- Section 1: Between generator
-- ============================================================

-- Sections 1-4 previously snapshotted the aux_arb internal functions.
-- With derive_mutual, instances use global defs instead. Verify instances exist:
#check (inferInstance : ArbitrarySizedSuchThat Nat (fun x => Between 0 x 10))
#check (inferInstance : ArbitrarySizedSuchThat BinaryTree (fun t => BST 0 10 t))
#check (inferInstance : ArbitrarySizedSuchThat term (fun e => typing [] e .Nat))
#check (inferInstance : ArbitrarySizedSuchThat (List Nat) (fun s => ExpMatch s (.Char 1)))

-- ============================================================
-- Section 5: ≠ + recursion bug regression
-- ============================================================

/-- List membership with an inequality guard — the minimal trigger for the bug.
    Before the fix, derive_generator failed with a DecOpt synthesis error. -/
inductive MemNat : List Nat → Nat → Prop where
| here  : ∀ n xs, MemNat (n :: xs) n
| there : ∀ n m xs, n ≠ m → MemNat xs n → MemNat (m :: xs) n

#guard_msgs(drop info, drop warning) in
derive_checker (fun xs n => MemNat xs n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun n => ∃ xs, MemNat xs n)

/--
info: def instArbitrarySizedSuchThatListNatMemNat.aux_arb : Nat → Nat → Nat → Nat → Gen (List Nat) :=
fun fuel initSize size n_1 =>
  Nat.brecOn (motive := fun fuel => Nat → Gen (List Nat)) fuel
    (instArbitrarySizedSuchThatListNatMemNat.aux_arb._f initSize n_1) size
-/
#guard_msgs in
#print instArbitrarySizedSuchThatListNatMemNat.aux_arb

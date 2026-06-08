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

/--
info: def instArbitrarySizedSuchThatNatBetween.aux_arb : Nat → Nat → Nat → Nat → Gen Nat :=
fun initSize size lo_1 hi_1 =>
  Nat.brecOn (motive := fun size => Nat → Gen Nat) size (instArbitrarySizedSuchThatNatBetween.aux_arb._f initSize lo_1)
    hi_1
-/
#guard_msgs in
#print instArbitrarySizedSuchThatNatBetween.aux_arb

-- ============================================================
-- Section 2: BST generator
-- ============================================================

/--
info: def instArbitrarySizedSuchThatBinaryTreeBST.aux_arb : Nat → Nat → Nat → Nat → Gen BinaryTree :=
fun initSize size lo_1 hi_1 =>
  Nat.brecOn (motive := fun size => Nat → Nat → Gen BinaryTree) size
    (instArbitrarySizedSuchThatBinaryTreeBST.aux_arb._f initSize) lo_1 hi_1
-/
#guard_msgs in
#print instArbitrarySizedSuchThatBinaryTreeBST.aux_arb

-- ============================================================
-- Section 3: STLC typing generator
-- ============================================================

/--
info: def instArbitrarySizedSuchThatTermTyping.aux_arb : Nat → Nat → List type → type → Gen term :=
fun initSize size G_1 t_1 =>
  Nat.brecOn (motive := fun size => List type → type → Gen term) size
    (instArbitrarySizedSuchThatTermTyping.aux_arb._f initSize) G_1 t_1
-/
#guard_msgs in
#print instArbitrarySizedSuchThatTermTyping.aux_arb

-- ============================================================
-- Section 4: RegExp match generator
-- ============================================================

/--
info: def instArbitrarySizedSuchThatListNatExpMatch.aux_arb : Nat → Nat → RegExp → Gen (List Nat) :=
fun initSize size re_1 =>
  Nat.brecOn (motive := fun size => RegExp → Gen (List Nat)) size
    (instArbitrarySizedSuchThatListNatExpMatch.aux_arb._f initSize) re_1
-/
#guard_msgs in
#print instArbitrarySizedSuchThatListNatExpMatch.aux_arb

-- ============================================================
-- Section 5: ≠ + recursion bug regression
-- ============================================================

/-- List membership with an inequality guard — the minimal trigger for the bug.
    Before the fix, derive_generator failed with a DecOpt synthesis error. -/
inductive MemNat : List Nat → Nat → Prop where
| here  : ∀ n xs, MemNat (n :: xs) n
| there : ∀ n m xs, n ≠ m → MemNat xs n → MemNat (m :: xs) n

#guard_msgs(drop info) in
derive_checker (fun xs n => MemNat xs n)

#guard_msgs(drop info) in
derive_generator (fun n => ∃ xs, MemNat xs n)

/--
info: def instArbitrarySizedSuchThatListNatMemNat.aux_arb : Nat → Nat → Nat → Gen (List Nat) :=
fun initSize size n_1 => Nat.brecOn size (instArbitrarySizedSuchThatListNatMemNat.aux_arb._f initSize n_1)
-/
#guard_msgs in
#print instArbitrarySizedSuchThatListNatMemNat.aux_arb

import Specimen.DecOpt
import Specimen.DeriveChecker
import Specimen.EnumeratorCombinators
import Specimen.DeriveConstrainedProducer
import SpecimenTest.DeriveArbitrarySuchThat.SimultaneousMatchingTests

/-! Snapshot test: derived checker for relations with existentially quantified variables. -/

open DecOpt

set_option guard_msgs.diff true

/-- `LessThanEq n m` is an inductive relation that means `n <= m`.
    Adapted from https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html -/
inductive LessThanEq : Nat → Nat → Prop where
  | Refl : ∀ n, LessThanEq n n
  | Succ : ∀ n m, LessThanEq n m → LessThanEq n (.succ m)

/-- `NatChain a b` means there is an ascending chain of `Nat`s under the usual `<=` order,
    where `a` and `b` are the start and end of the chain respectively.
    This is an inductive relation with multiple existentially quantified variables
    (note how `x` and `y` don't appear in the conclusion of the `ChainExists` constructor).

    We use `LessThanEq` (defined above) instead of the `LE.le` operator from the Lean standard library,
    since `LE` is defined as a typeclass and not as an inductive relation. -/
inductive NatChain (a b : Nat) : Prop where
| ChainExists : ∀ (x y : Nat),
    (LessThanEq a x) →
    (LessThanEq x y) ->
    (LessThanEq y b) →
    NatChain a b

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun x => ∃ (a : Nat), LessThanEq a x)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun x => ∃ (y : Nat), LessThanEq x y)

#guard_msgs(drop info, drop warning) in
derive_checker (fun n m => LessThanEq n m)

#guard_msgs(drop info, drop warning) in
derive_checker (fun a b => NatChain a b)

-- Regression test: argument names that collide with internal reserved names
-- (`size'`, `aux_dec`, `aux_arb`, `aux_enum`) should not cause unbound identifier errors.
-- See bug_report_Specimen_DeriveChecker_2026-03-12_06-55_lnao.md

/-- Like `LessThanEq` but with an argument deliberately named `size'`
    to test that the derivation machinery correctly freshens internal names. -/
inductive SizedLe : Nat → Nat → Prop where
  | Refl : ∀ n, SizedLe n n
  | Succ : ∀ size' n, SizedLe size' n → SizedLe size' (Nat.succ n)

#guard_msgs(drop info, drop warning) in
derive_checker (fun size' n => SizedLe size' n)

/-- Like `LessThanEq` but with an argument deliberately named `aux_dec`
    to test that the derivation machinery correctly freshens internal names. -/
inductive AuxDecLe : Nat → Nat → Prop where
  | Refl : ∀ n, AuxDecLe n n
  | Succ : ∀ aux_dec n, AuxDecLe aux_dec n → AuxDecLe aux_dec (Nat.succ n)

#guard_msgs(drop info, drop warning) in
derive_checker (fun aux_dec n => AuxDecLe aux_dec n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun size' => ∃ n, SizedLe size' n)

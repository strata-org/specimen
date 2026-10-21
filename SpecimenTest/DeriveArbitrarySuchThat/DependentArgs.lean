import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.DeriveChecker
import Plausible.Attr
import Specimen.Basalt

/-! Tests for `derive_generator` on inductive relations with dependent arguments. -/

set_option guard_msgs.diff true

-- These relations bind several existentials in one hypothesis (`foo (a b : α) : a = b → …`),
-- so multi-output scheduling asks for a joint `(α × α)` producer instance that nothing derives.
-- This file tests dependent-argument handling, not multi-output, so pin the option off.
set_option specimen.multiOutput false

inductive HasDep {α : Type} (_ : List α) : Nat → Prop where
| foo (a b : α) : a = b → HasDep _ 0

-- The parameter is anonymous, so it elaborates to a binder with a hygienic name, as an unnamed premise
-- does; it is still a variable, not a hypothesis.
#guard_msgs(warning, drop info) in
derive_generator (fun α l => ∃ n, @HasDep α l n)

/-- info: true -/
#guard_msgs in
#eval do
  let xs ← Gen.sampleWithSeed 20
    (fun _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun n => @HasDep Nat [1, 2] n) 5) 5 7
  return (xs.size == 20 && (xs.filterMap id).size == 20 && (xs.filterMap id).all (· == 0))

inductive HasClassDep {α : Type} [h : DecidableEq α] : Nat → Prop where
| foo (a b : α) : a = b → HasClassDep 0

#guard_msgs(warning, drop info) in
derive_generator (fun α inst => ∃ n, @HasClassDep α inst n)

#guard_msgs(warning, drop info) in
derive_checker fun α inst n => @HasClassDep α inst n

#guard_msgs(warning, drop info) in
derive_enumerator (fun α inst => ∃ n, @HasClassDep α inst n)

def f : Nat → Nat := fun _ => 0

inductive HasCall : Nat → Prop where
| foo (n : Nat) : f n = 0 → HasCall n

#guard_msgs(warning, error, whitespace:=lax, drop info) in
derive_generator ∃ n, HasCall n

#guard_msgs(warning, error, whitespace:=lax, drop info) in
derive_enumerator ∃ n, HasCall n

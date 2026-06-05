import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import Specimen.DeriveChecker
import Plausible.Attr

/-! Tests for `derive_generator` on inductive relations with dependent arguments. -/

set_option guard_msgs.diff true


inductive HasDep {α : Type} (_ : List α) : Nat → Prop where
| foo (a b : α) : a = b → HasDep _ 0

/--
error: unable to find unknown x._@.SpecimenTest.DeriveArbitrarySuchThat.DependentArgs.1339814650._hygCtx._hyg.3 in UnknownMap [(n_1,
  Undef Nat),
 (α_1, Fixed),
 (l_1, Fixed),
 (a, Undef α),
 (u_2, Unknown n_1),
 (b, Undef α),
 (u_1, Unknown l_1),
 (unk_0, Undef Nat),
 (α, Unknown u_0),
 (u_0, Unknown α_1)]
-/
#guard_msgs(error, ordering:=sorted) in
derive_generator (fun α l => ∃ n, @HasDep α l n)

inductive HasClassDep {α : Type} [h : DecidableEq α] : Nat → Prop where
| foo (a b : α) : a = b → HasClassDep 0

#guard_msgs(drop info, drop warning) in
derive_generator (fun α inst => ∃ n, @HasClassDep α inst n)

#guard_msgs(drop info, drop warning) in
derive_checker fun α inst n => @HasClassDep α inst n

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun α inst => ∃ n, @HasClassDep α inst n)

def f : Nat → Nat := fun _ => 0

inductive HasCall : Nat → Prop where
| foo (n : Nat) : f n = 0 → HasCall n

#guard_msgs(error, whitespace:=lax, drop info) in
derive_generator ∃ n, HasCall n

#guard_msgs(error, whitespace:=lax, drop info) in
derive_enumerator ∃ n, HasCall n

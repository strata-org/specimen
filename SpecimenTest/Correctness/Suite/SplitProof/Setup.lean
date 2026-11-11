import SpecimenTest.Correctness.Suite.Prelude

/-! A completeness proof split across files: this setup, the part files `Part0` and `Part1`, and
`Finish`. The generators are derived `scoped`, so that their instances are active only where their
namespace is open: the part files open nothing, and run in the scope the setup recorded. -/

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.SplitProof
mutual
  inductive Even : Nat → Prop where
    | zero_is_even : Even .zero
    | succ_of_odd_is_even : ∀ n : Nat, Odd n → Even (.succ n)
  inductive Odd : Nat → Prop where
    | succ_of_even_is_odd : ∀ n : Nat, Even n → Odd (.succ n)
end

namespace Gens
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
scoped derive_mutual generator (∃ (n : Nat), Even n), enumerator (∃ (n : Nat), Odd n)
end Gens
end Suite.SplitProof

open Suite.SplitProof Suite.SplitProof.Gens

set_option specimen.parallelProofs true
set_option specimen.splitMinWorkers 2
#specimen_prove_sound
#specimen_prove_setup

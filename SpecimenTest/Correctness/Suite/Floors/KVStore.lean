import SpecimenTest.Correctness.Suite.KVDefs
open Suite.KVStore

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
namespace SuiteF.KVStore
set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun s => ∃ (kv : StateResult × String × Nat × String), LookupKV s kv),
  generator (fun x => ∃ (foo : StateAPICall × StateResult × List (String × String)), EvalStateApiCall x foo),
  generator (fun s => ∃ (nb : Nat × List (String × String)), GetBucket s nb),
  generator (fun s => ∃ (crns : APICall × Result × (Nat × List (Nat × List (String × String)))), EvalApiCall s crns),
  generator (fun s => ∃ (o : List (APICall × Result) × (Nat × List (Nat × List (String × String)))), EvalApiCalls s o),
  checker (fun s kv => LookupKV s kv),
  checker (fun k s s2 => RemoveKV k s s2)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end SuiteF.KVStore

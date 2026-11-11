import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
namespace Suite.BoundedBuffer
abbrev BB := (List String) × Nat
inductive BBCmd where
| Put (v : String)
| Get
| Size
deriving Repr
inductive BBResult where
| PutOk
| GetOk (v : String)
| SizeOk (n : Nat)
| Error
deriving Repr
deriving instance Basalt.ArbitrarySized for BBCmd
instance : ArbitrarySizedComplete BBCmd := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch BBCmd := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits BBCmd := ⟨by arbitrary_hits_derived⟩
abbrev BBTrace := List (BBCmd × BBResult)
inductive WithinCapacity : List String → Nat → Prop where
| mk : s.length ≤ c → WithinCapacity s c
inductive BBSafeStep : BB → BBCmd → BBResult → BB → Prop where
| PutOp: ∀ s s' c v, WithinCapacity (v :: s) c → s' = List.concat s v →
    BBSafeStep (s,c) (BBCmd.Put v) BBResult.PutOk (s',c)
| GetOp: ∀ s c v, WithinCapacity (v :: s) c → BBSafeStep (v :: s, c) BBCmd.Get (BBResult.GetOk v) (s,c)
| SizeOp: ∀ s c, WithinCapacity s c → BBSafeStep (s,c) BBCmd.Size (BBResult.SizeOk (List.length s)) (s,c)
inductive SafeBBTrace : BB -> BBTrace -> BB -> Prop where
| WF_Empty: ∀ s c, WithinCapacity s c → SafeBBTrace (s,c) [] (s,c)
| WF_Op: ∀ s s' s'' cmd res ps, BBSafeStep s cmd res s' -> SafeBBTrace s' ps s'' ->
    SafeBBTrace s ((cmd, res)::ps) s''
inductive CanStep : BB → BBCmd → Prop where
| intro : ∀ bb c r bb', BBSafeStep bb c r bb' → CanStep bb c
inductive BBStep : BB → BBCmd → BBResult → BB → Prop where
| SafeStep: ∀ bb c r bb', BBSafeStep bb c r bb' → BBStep bb c r bb'
| ErrStep: ∀ bb c, ¬ CanStep bb c → BBStep bb c BBResult.Error bb
inductive EveryBBTrace : BB -> BBTrace -> BB -> Prop where
| All_Empty: ∀ s c, EveryBBTrace (s,c) [] (s,c)
| All_Op: ∀ s s' s'' cmd res ps, BBStep s cmd res s' -> EveryBBTrace s' ps s'' ->
    EveryBBTrace s ((cmd, res)::ps) s''

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun i => ∃ t s, SafeBBTrace i t s),
  generator (fun s => ∃ t i, SafeBBTrace i t s)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.BoundedBuffer

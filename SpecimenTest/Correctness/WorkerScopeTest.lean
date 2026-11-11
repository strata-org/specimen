import SpecimenTest.Correctness.Suite.Prelude
import Specimen.Correctness.Workers

/-! `worker%` picks among derivations of the same mode by which instance is visible: two `scoped`
derivations, in `A` and `B`, of the generator for `Even`. -/

open Lean Meta Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace WorkerScope
inductive Even : Nat → Prop where
  | zero : Even 0
  | ss : ∀ n, Even n → Even (n + 2)

namespace A
scoped derive_mutual generator (∃ n, Even n)
end A
namespace B
scoped derive_mutual generator (∃ n, Even n)
end B
end WorkerScope

/-- The namespace of the worker `worker%` would pick here, if it picks one. -/
def picked (ns? : Option Name := none) : MetaM (Option Name) := do
  try return some (← Specimen.resolveWorker "gen" `WorkerScope.Even [0] ns?).getPrefix
  catch _ => return none

-- neither derivation's instances are visible: none is picked
#eval show MetaM Unit from do guard ((← picked) == none)

open WorkerScope.A in
#eval show MetaM Unit from do guard ((← picked) == some `WorkerScope.A)

open WorkerScope.B in
#eval show MetaM Unit from do guard ((← picked) == some `WorkerScope.B)

-- both visible: ambiguous, unless named
open WorkerScope.A WorkerScope.B in
#eval show MetaM Unit from do
  guard ((← picked) == none)
  guard ((← picked (some `WorkerScope.B)) == some `WorkerScope.B)

-- the current namespace's scoped instances are visible
namespace WorkerScope.A
#eval show MetaM Unit from do guard ((← picked) == some `WorkerScope.A)
end WorkerScope.A

-- `worker%` as a term
open WorkerScope.A in
example : True := by
  have _ := (worker% gen WorkerScope.Even [0] (G := SGen))
  trivial

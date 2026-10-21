import Specimen.Interp.InstanceLeaves
import SpecimenTest.Interp.BSTInterpTest

/-!
# Leaves resolved from the instances in scope

`InterpEnv.withInstanceLeaves` replaces every hand-registered unconstrained leaf with the generator Lean
synthesises *here*, so the interpreter measures the generator the compiled code would run rather than
whatever a separate module registered. `AnyPair a b` constrains neither output, so its generator draws both
`Nat`s unconstrained; `Nat`'s `Arbitrary` resolves here, so one leaf is installed and none is left as
registered.
-/

open Lean Meta Specimen.Interp SpecimenTest.InterpBST

inductive AnyPair : Nat → Nat → Prop where
  | mk : ∀ a b, AnyPair a b

derive_relspec AnyPair

def anyPairKey : Schedules.SpecKey :=
  { inductiveName := ``AnyPair, outputIndices := [0, 1], deriveSort := .Generator }

/-- info: "[instance-leaves] 1 leaf/leaves from instances in scope · 0 not resolvable" -/
#guard_msgs in
#eval show MetaM String from do
  match leaves.deriveClosure [anyPairRelSpec] [anyPairKey] with
  | .error e => return s!"closure failed: {e}"
  | .ok env => return (← env.withInstanceLeaves).2.render

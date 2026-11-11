import Specimen
import Specimen.Basalt
import Specimen.Correctness.FloorOf

/-! A derived checker with a negated decidable premise, and a generator that checks it. -/

namespace Specimen.Correctness.CheckNegTest
open Basalt Specimen.Correctness

inductive Neq : Nat → Nat → Prop where
  | mk : ∀ a b, ¬ (a = b) → Neq a b

inductive Use : Nat → Nat → Bool → Prop where
  | mk : ∀ a b, Neq a b → Use a b true

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual generator (fun a b => ∃ t, Use a b t)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, _) in (← getEnv).constants.map₂.toList do
    let s := n.toString
    if !((s.splitOn "_block").length > 1) && ((s.splitOn "checkSound").length > 1 || ((s.splitOn ".sound").length > 1 && (s.splitOn "Use").length > 1)) then
      logInfo m!"{n}"
end Specimen.Correctness.CheckNegTest

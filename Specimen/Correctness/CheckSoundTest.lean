import Specimen
import Specimen.Basalt
import Specimen.Correctness.CheckSoundOf
import Specimen.Correctness.EnumSoundOf

/-! A derived generator whose rules check premises with derived checkers: the checkers' soundness
(`checkSound`), and the generator's soundness through it. -/

namespace Specimen.Correctness.CheckSoundTest
open Basalt Specimen.Correctness

inductive Ty where | a | b | c
deriving DecidableEq, Repr

deriving instance Basalt.ArbitrarySized for Ty

inductive NotC : Ty → Prop where
  | a : NotC .a
  | b : NotC .b

inductive Mrg : List Nat → List Nat → List Nat → Prop where
  | nil : Mrg [] [] []
  | left : ∀ x c₁ c₂ c, Mrg c₁ c₂ c → Mrg (x :: c₁) c₂ (x :: c)
  | right : ∀ x c₁ c₂ c, Mrg c₁ c₂ c → Mrg c₁ (x :: c₂) (x :: c)

/-- `s` and the lists are inputs: `NotC s` and `Mrg` are checked; `t` is produced. -/
inductive Pick : Ty → List Nat → List Nat → List Nat → Ty → Prop where
  | mk : ∀ s l₁ l₂ l t, NotC s → Mrg l₁ l₂ l → t ≠ .c → Pick s l₁ l₂ l t

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual generator (fun s l₁ l₂ l => ∃ t, Pick s l₁ l₂ l t)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, _) in (← getEnv).constants.map₂.toList do
    let s := n.toString
    if (s.splitOn "checkSound").length > 1 || ((s.splitOn ".sound").length > 1 && (s.splitOn "Pick").length > 1) then
      if !((s.splitOn "_block").length > 1) then logInfo m!"{n}"

end Specimen.Correctness.CheckSoundTest

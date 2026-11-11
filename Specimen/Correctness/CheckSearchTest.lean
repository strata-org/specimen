import Specimen
import Specimen.Basalt
import Specimen.Correctness.CheckSoundOf
import Specimen.Correctness.EnumSoundOf

/-! A derived checker that searches for a premise's witness with a derived enumerator: the
enumerator's search law, the checker's soundness through it, and a generator's through that. -/

namespace Specimen.Correctness.CheckSearchTest
open Basalt Specimen.Correctness

inductive Between : Nat → Nat → Nat → Prop where
  | here : ∀ lo hi, lo ≤ hi → Between lo hi lo
  | there : ∀ lo hi n, Between (lo + 1) hi n → Between lo hi n

/-- `n` is existential: the checker searches for it with `Between`'s enumerator. -/
inductive HasThree : Nat → Nat → Prop where
  | mk : ∀ lo hi n, Between lo hi n → n = 3 → HasThree lo hi

inductive Pick : Nat → Nat → Bool → Prop where
  | mk : ∀ lo hi, HasThree lo hi → Pick lo hi true

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual generator (fun lo hi => ∃ b, Pick lo hi b)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, _) in (← getEnv).constants.map₂.toList do
    let s := n.toString
    if !((s.splitOn "_block").length > 1) && ((s.splitOn "searchSound").length > 1 ||
        (s.splitOn "checkSound").length > 1 || ((s.splitOn ".sound").length > 1 && (s.splitOn "Pick").length > 1)) then
      logInfo m!"{n}"

end Specimen.Correctness.CheckSearchTest

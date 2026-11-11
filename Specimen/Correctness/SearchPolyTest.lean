import Specimen
import Specimen.Basalt
import Specimen.Correctness.CheckSoundOf
import Specimen.Correctness.EnumSoundOf

/-! A derived enumerator over a relation with type parameters: its search laws. -/

namespace Specimen.Correctness.SearchPolyTest
open Basalt Specimen.Correctness

inductive MC {α β : Type} : α → β → List (α × β) → Prop where
  | here : ∀ k v rest, MC k v ((k, v) :: rest)
  | there : ∀ k v p rest, MC k v rest → MC k v (p :: rest)

set_option specimen.emitBasalt true
set_option specimen.richOutput false
set_option specimen.emitSound true

derive_mutual enumerator (fun k l => ∃ v, MC k v l)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for (n, _) in (← getEnv).constants.map₂.toList do
    let s := n.toString
    if !((s.splitOn "_block").length > 1) && ((s.splitOn "searchSound").length > 1 || (s.splitOn "searchFinds").length > 1 || (s.splitOn ".sound").length > 1) then
      logInfo m!"{n}"

end Specimen.Correctness.SearchPolyTest

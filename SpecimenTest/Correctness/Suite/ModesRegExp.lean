import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ModesRegExp
inductive RegExp : Type where
  | EmptySet : RegExp
  | EmptyStr : RegExp
  | Char : Nat → RegExp
  | App : RegExp → RegExp → RegExp
  | Union : RegExp → RegExp → RegExp
  | Star : RegExp → RegExp
  deriving Repr
inductive ExpMatch : List Nat → RegExp → Prop where
| MEmpty : ExpMatch [] RegExp.EmptyStr
| MChar : ∀ x, ExpMatch [x] (RegExp.Char x)
| MApp : ∀ s1 re1 s2 re2, ExpMatch s1 re1 → ExpMatch s2 re2 → ExpMatch (s1 ++ s2) (RegExp.App re1 re2)
| MUnionL : ∀ s1 re1 re2, ExpMatch s1 re1 → ExpMatch s1 (RegExp.Union re1 re2)
| MUnionR : ∀ re1 s2 re2, ExpMatch s2 re2 → ExpMatch s2 (RegExp.Union re1 re2)
| MStar0 : ∀ re, ExpMatch [] (RegExp.Star re)
| MStarApp : ∀ s1 s2 re, ExpMatch s1 re → ExpMatch s2 (RegExp.Star re) → ExpMatch (s1 ++ s2) (RegExp.Star re)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual enumerator (fun r0 => ∃ (s : List Nat), ExpMatch s r0),
  checker (fun s r0 => ExpMatch s r0)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ModesRegExp

import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.Poly
inductive Contains {α : Type} : List α → α → Prop where
| head : Contains (x :: xs) x
| tail : Contains xs x → Contains (y :: xs) x
inductive IsWrapped {α : Type} : α → Option α → Prop where
| some : IsWrapped x (some x)
inductive SameType {α : Type} : α → α → Prop where
| refl : SameType (x : α) (x : α)
inductive FirstOf {α β : Type} : α × β → α → Prop where
| mk : FirstOf (x, y) x
inductive HasLen {α : Type} : List α → Nat → Prop where
| nil : HasLen [] 0
| cons : HasLen xs n → HasLen (x :: xs) (n + 1)
inductive Interleaves {α β : Type} : List α → List β → List (α ⊕ β) → Prop where
| nil_nil : Interleaves [] [] []
| left_cons : Interleaves xs ys zs → Interleaves (x :: xs) ys (Sum.inl x :: zs)
| right_cons : Interleaves xs ys zs → Interleaves xs (y :: ys) (Sum.inr y :: zs)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (fun α xs => ∃ x, @Contains α xs x),
  generator (fun α x => ∃ opt, @IsWrapped α x opt),
  generator (fun α x => ∃ y, @SameType α x y),
  generator (fun α β p => ∃ x, @FirstOf α β p x),
  generator (fun α xs => ∃ n, @HasLen α xs n),
  generator (fun α β xs ys => ∃ zs, @Interleaves α β xs ys zs),
  enumerator (fun α xs => ∃ x, @Contains α xs x),
  checker (fun α xs n => @HasLen α xs n)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.Poly

import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ModesSTLC
inductive type where
  | Nat : type
  | Fun : type → type → type
  deriving Repr, BEq, DecidableEq
inductive term where
  | Const : Nat → term
  | Add : term → term → term
  | Var : Nat → term
  | App : term → term → term
  | Abs : type → term → term
  deriving Repr
deriving instance Basalt.ArbitrarySized for type
instance : ArbitrarySizedComplete type := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch type := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits type := ⟨by arbitrary_hits_derived⟩
inductive lookup : List type -> Nat -> type -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ, lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ
inductive typing: List type → term → type → Prop where
| TConst : ∀ Γ n, typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2, typing Γ e1 .Nat → typing Γ e2 .Nat → typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ Γ e τ1 τ2, typing (τ1::Γ) e τ2 → typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ, lookup Γ x τ → typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2, typing Γ e2 τ1 → typing Γ e1 (.Fun τ1 τ2) → typing Γ (.App e1 e2) τ2

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual enumerator (fun Γ τ => ∃ (e : term), typing Γ e τ),
  enumerator (fun Γ τ => ∃ (x : Nat), lookup Γ x τ),
  enumerator (fun Γ x => ∃ (τ : type), lookup Γ x τ),
  enumerator (fun Γ e => ∃ (τ : type), typing Γ e τ),
  checker (fun Γ x τ => lookup Γ x τ),
  checker (fun Γ e τ => typing Γ e τ)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ModesSTLC

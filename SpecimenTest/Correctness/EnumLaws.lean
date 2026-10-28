
import Basalt
import Specimen.Enum
import Specimen.Enum.Laws
import BasaltExamples.ArbNat
import BasaltExamples.ArbList
import BasaltExamples.BST
import BasaltExamples.STLC.GenType

/-!
# The enumeration laws, walked

Ported with `Specimen.Enum` from Basalt's `enum-from-gen` branch, where it is the regression suite of
the laws; the generators are written there and here alike, over Basalt's `Gen`.

`walk fixpoint` proves `IsEnumerated`, `IsWeighed` and `IsCostEnumerated` construct by construct,
through `genRel_enumerates`, `genRel_weighs` and `genRel_costEnumerates`, and `EnumeratesSome`,
`CostEnumeratesSome` and `WeighsSome` for a generator that fails and backtracks, through
`genRel_enumeratesSome`, `genRel_costEnumeratesSome` and `genRel_weighsSome`.
-/


open Basalt Specimen ArbNat ArbList BST

namespace EnumLawTest

theorem nat_enumerated : IsEnumerated Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_enumerated : IsEnumerated (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_enumerated : IsEnumerated STLC.genType := ⟨by walk fixpoint⟩
theorem list_enumerated : IsEnumerated List.arbitrary := ⟨by walk fixpoint [nat_enumerated.enumerates]⟩

theorem nat_weighed : IsWeighed Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_weighed : IsWeighed (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_weighed : IsWeighed STLC.genType := ⟨by walk fixpoint⟩
theorem list_weighed : IsWeighed List.arbitrary := ⟨by walk fixpoint [nat_weighed.weighs]⟩

theorem nat_costEnumerated : IsCostEnumerated Nat.arbitrary := ⟨by walk fixpoint⟩
theorem bst_costEnumerated : IsCostEnumerated (Tree.genBST lo hi) := ⟨by walk fixpoint⟩
theorem genType_costEnumerated : IsCostEnumerated STLC.genType := ⟨by walk fixpoint⟩
theorem list_costEnumerated : IsCostEnumerated List.arbitrary :=
  ⟨by walk fixpoint [nat_costEnumerated.costEnumerates]⟩

/-- `genBST`'s enumeration, where defined, is exactly the valid BSTs: the walked law and the
generator's correctness proof, combined. -/
example (hd : (Tree.genBST (G := Specimen.Finite) lo hi) ≠ .undef) (t : BST.Tree Int) :
    (Tree.genBST (G := Specimen.Finite) lo hi).Mem t ↔ t.isBST lo hi :=
  bst_enumerated.mem_iff Tree.genBST.sound_complete hd t

/-! ## Failure and backtracking

Defined here, not imported, so `walk fixpoint` must realize their `eq_def` itself. -/

inductive Ty | nat | bool

inductive Expr | lit (n : Nat) | isPos (n : Nat) | add (l r : Expr)

def digit [Gen G] : G Nat := do return (← RandomChoice.choose 0 2 (by omega)).down.val

/-- A derived generator's shape: a rule per branch, `fail` where a rule does not apply, recursion
on a size. -/
def hasType [Gen G] [Fail G] [Backtrack G] (τ : Ty) : Nat → G Expr
  | 0 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail)]
  | size + 1 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail),
      (size + 1, fun _ => match τ with
        | .nat => Expr.add <$> hasType .nat size <*> hasType .nat size
        | _ => Fail.fail)]

theorem hasType_enumeratesSome (τ : Ty) (n : Nat) :
    EnumeratesSome (hasType (G := Specimen.Finite) τ n) (hasType (G := OptionT SPMF) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasType; walk
  | succ n ih => unfold hasType; walk [ih .nat]

/-- Unbounded recursion through `backtrack`, so a `partial_fixpoint`. -/
def digits [Gen G] [Fail G] [Backtrack G] [MonoBacktrack G] : G (List Nat) :=
  Backtrack.backtrack [(1, fun _ => pure []), (2, fun _ => do return (← digit) :: (← digits))]
partial_fixpoint

theorem digits_enumeratesSome :
    EnumeratesSome (digits (G := Specimen.Finite)) (digits (G := OptionT SPMF)) := by
  walk fixpoint

/-- Unbounded recursion through `pick`, the draw without retry. -/
def picked [Gen G] [Fail G] [Pick G] [MonoPick G] : G (List Nat) :=
  Pick.pick [(1, fun _ => pure []), (3, fun _ => do return (← digit) :: (← picked)), (0, fun _ => Fail.fail)]
partial_fixpoint

theorem picked_enumeratesSome :
    EnumeratesSome (picked (G := Specimen.Finite)) (picked (G := OptionT SPMF)) := by
  walk fixpoint

theorem hasType_costEnumeratesSome (τ : Ty) (n : Nat) :
    CostEnumeratesSome (hasType (G := CostGraded Specimen.Finite) τ n)
      (hasType (G := OptionT SPMF.Cost) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasType; walk
  | succ n ih => unfold hasType; walk [ih .nat]

theorem hasType_weighsSome (τ : Ty) (n : Nat) :
    WeighsSome (hasType (G := WFinite) τ n) (hasType (G := OptionT SPMF) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasType; walk
  | succ n ih => unfold hasType; walk [ih .nat]

theorem digits_costEnumeratesSome :
    CostEnumeratesSome (digits (G := CostGraded Specimen.Finite)) (digits (G := OptionT SPMF.Cost)) := by
  walk fixpoint

theorem picked_costEnumeratesSome :
    CostEnumeratesSome (picked (G := CostGraded Specimen.Finite)) (picked (G := OptionT SPMF.Cost)) := by
  walk fixpoint

theorem digits_weighsSome : WeighsSome (digits (G := WFinite)) (digits (G := OptionT SPMF)) := by
  walk fixpoint

theorem picked_weighsSome : WeighsSome (picked (G := WFinite)) (picked (G := OptionT SPMF)) := by
  walk fixpoint

/-- `hasType` truncated as derived code is: at size `0` the recursive rule fails with a label, so a
search looks elsewhere and a checker does not mistake it for a refutation. -/
def hasTypeT [Gen G] [Fail G] [FailWith Unit G] [Backtrack G] (τ : Ty) : Nat → G Expr
  | 0 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail),
      (1, fun _ => match τ with | .nat => FailWith.failWith () | _ => Fail.fail)]
  | size + 1 => Backtrack.backtrack [
      (1, fun _ => match τ with | .nat => do return .lit (← digit) | _ => Fail.fail),
      (1, fun _ => match τ with
        | .bool => do let n ← digit; if n ≠ 0 then pure (.isPos n) else Fail.fail
        | _ => Fail.fail),
      (size + 1, fun _ => match τ with
        | .nat => Expr.add <$> hasTypeT .nat size <*> hasTypeT .nat size
        | _ => Fail.fail)]

theorem hasTypeT_enumeratesWith (τ : Ty) (n : Nat) :
    EnumeratesWith (hasTypeT (G := ExceptT Unit Specimen.Finite) τ n)
      (hasTypeT (G := ExceptT Unit (OptionT SPMF)) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasTypeT; walk
  | succ n ih => unfold hasTypeT; walk [ih .nat]

theorem hasTypeT_costEnumeratesWith (τ : Ty) (n : Nat) :
    CostEnumeratesWith (hasTypeT (G := ExceptT Unit (CostGraded Specimen.Finite)) τ n)
      (hasTypeT (G := ExceptT Unit (OptionT SPMF.Cost)) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasTypeT; walk
  | succ n ih => unfold hasTypeT; walk [ih .nat]

theorem hasTypeT_weighsWith (τ : Ty) (n : Nat) :
    WeighsWith (hasTypeT (G := ExceptT Unit WFinite) τ n)
      (hasTypeT (G := ExceptT Unit (OptionT SPMF)) τ n) := by
  induction n generalizing τ with
  | zero => unfold hasTypeT; walk
  | succ n ih => unfold hasTypeT; walk [ih .nat]

/-- Unbounded recursion through `backtrack` and `pick`, a branch failing with a label. -/
def digitsT [Gen G] [Fail G] [FailWith Unit G] [Backtrack G] [MonoBacktrack G] : G (List Nat) :=
  Backtrack.backtrack [(1, fun _ => pure []), (2, fun _ => do return (← digit) :: (← digitsT)),
    (1, fun _ => FailWith.failWith ())]
partial_fixpoint

def pickedT [Gen G] [Fail G] [FailWith Unit G] [Pick G] [MonoPick G] : G (List Nat) :=
  Pick.pick [(1, fun _ => pure []), (3, fun _ => do return (← digit) :: (← pickedT)),
    (1, fun _ => FailWith.failWith ())]
partial_fixpoint

theorem digitsT_weighsWith :
    WeighsWith (digitsT (G := ExceptT Unit WFinite)) (digitsT (G := ExceptT Unit (OptionT SPMF))) := by
  walk fixpoint

theorem pickedT_weighsWith :
    WeighsWith (pickedT (G := ExceptT Unit WFinite)) (pickedT (G := ExceptT Unit (OptionT SPMF))) := by
  walk fixpoint

end EnumLawTest

import Specimen
import Specimen.Basalt
import Specimen.Correctness.SoundOf
import Specimen.Correctness.FloorOf

/-! Side mission: do derived floors make a balanced-BST generator succeed, with a good distribution? -/

namespace BalBSTTest
open Basalt

inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (r : Tree)
  deriving Repr, Inhabited

/-- A key in `[lo, hi)`. -/
inductive Between : Nat → Nat → Nat → Prop where
  | mk : ∀ lo hi k, lo ≤ k → k < hi → Between lo hi k

/-- Hand-written: uniform over `[lo, hi)`. -/
instance (lo hi : Nat) : BacktrackGenFor Nat (fun k => Between lo hi k) where
  gen _ _ := if h : lo < hi then chooseNat lo (hi - 1) (by omega) else Specimen.Fail.fail

open Specimen.Correctness in
@[specimen_sound] theorem between_gen (lo hi s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun k => Between lo hi k) (G := SGen) s l)
      (fun k => Between lo hi k) := by
  show succObs.spec (if h : lo < hi then chooseNat lo (hi - 1) (by omega) else Specimen.Fail.fail : SGen Nat) _
  split
  · walk
    exact Between.mk _ _ _ (by omega) (by omega)
  · walk

/-- `BalBST lo hi h t`: `t` is a perfectly balanced BST of height `h` with keys in `[lo, hi)`. -/
inductive BalBST : Nat → Nat → Nat → Tree → Prop where
  | leaf : ∀ lo hi, BalBST lo hi 0 .leaf
  | node : ∀ lo hi h k l r, Between lo hi k →
      BalBST lo k h l → BalBST (k + 1) hi h r → BalBST lo hi (h + 1) (.node l k r)

/-- AVL-balanced: child heights differ by at most one. -/
inductive AVL : Nat → Nat → Nat → Tree → Prop where
  | leaf : ∀ lo hi, AVL lo hi 0 .leaf
  | even : ∀ lo hi h k l r, Between lo hi k →
      AVL lo k h l → AVL (k + 1) hi h r → AVL lo hi (h + 1) (.node l k r)
  | leftHi : ∀ lo hi h k l r, Between lo hi k →
      AVL lo k (h + 1) l → AVL (k + 1) hi h r → AVL lo hi (h + 2) (.node l k r)
  | rightHi : ∀ lo hi h k l r, Between lo hi k →
      AVL lo k h l → AVL (k + 1) hi (h + 1) r → AVL lo hi (h + 2) (.node l k r)

/-- The size a perfect tree of height `h` needs: one per node. -/
def need (_lo _hi : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => 1 + 2 * need 0 0 h

/-- The AVL floor: the fewest nodes of an AVL tree of height `h`. -/
def needAVL (_lo _hi : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | h + 2 => 1 + needAVL 0 0 (h + 1) + needAVL 0 0 h

set_option specimen.emitBasalt true
set_option specimen.richOutput false

namespace Div
scoped derive_mutual generator (fun lo hi h => ∃ t, BalBST lo hi h t)
scoped derive_mutual generator (fun lo hi h => ∃ t, AVL lo hi h t)
end Div

namespace Uniform
set_option specimen.sizeSplit true in
scoped derive_mutual generator (fun lo hi h => ∃ t, BalBST lo hi h t)
set_option specimen.sizeSplit true in
scoped derive_mutual generator (fun lo hi h => ∃ t, AVL lo hi h t)
end Uniform

namespace Derived
set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
scoped derive_mutual generator (fun lo hi h => ∃ t, BalBST lo hi h t)
set_option specimen.sizeSplit true in
set_option specimen.deriveFloors true in
set_option specimen.emitSound true in
scoped derive_mutual generator (fun lo hi h => ∃ t, AVL lo hi h t)
end Derived

namespace Hand
set_option specimen.sizeSplit true in
set_option specimen.splitFloors "BalBSTTest.BalBST:BalBSTTest.need" in
scoped derive_mutual generator (fun lo hi h => ∃ t, BalBST lo hi h t)
set_option specimen.sizeSplit true in
set_option specimen.splitFloors "BalBSTTest.AVL:BalBSTTest.needAVL" in
scoped derive_mutual generator (fun lo hi h => ∃ t, AVL lo hi h t)
end Hand

end BalBSTTest

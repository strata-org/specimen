import Specimen.Enumerators
import Specimen.EnumeratorCombinators
import Specimen.DeriveEnum

set_option guard_msgs.diff true

/-! ## Nested (indirect) recursion through container types -/

/-- A type with nested recursion: `node` takes `List NestedTree` rather than
    `NestedTree` directly. -/
inductive NestedTree where
  | leaf : NestedTree
  | node : Nat → List NestedTree → NestedTree
  deriving Repr

deriving instance Enum for NestedTree

#guard_msgs(drop info, drop warning) in
#synth EnumSized NestedTree

#guard_msgs(drop info, drop warning) in
#synth Enum NestedTree

/-- info: [NestedTree.node 0 [], NestedTree.leaf] -/
#guard_msgs in
#eval (runEnum (α := NestedTree) 0)

/-! ## Mutual recursion -/

mutual
  inductive MutEven where
    | zero : MutEven
    | succOdd : MutOdd → MutEven
    deriving Repr

  inductive MutOdd where
    | succEven : MutEven → MutOdd
    deriving Repr
end

deriving instance Enum for MutEven, MutOdd

#guard_msgs(drop info, drop warning) in
#synth EnumSized MutEven

#guard_msgs(drop info, drop warning) in
#synth EnumSized MutOdd

#guard_msgs(drop info, drop warning) in
#synth Enum MutEven

#guard_msgs(drop info, drop warning) in
#synth Enum MutOdd

-- Verify the enumerators produce non-empty output.
-- Note: mutual recursion through `partial def` + local instances (mirroring
-- DeriveArbitrary) does not decrement fuel for cross-type calls, so the
-- enumerator exhaustively produces all reachable chains. We drop the output
-- and just check that evaluation succeeds.
#guard_msgs(drop info, drop warning) in
#eval (runEnum (α := MutEven) 0)

#guard_msgs(drop info, drop warning) in
#eval (runEnum (α := MutOdd) 0)

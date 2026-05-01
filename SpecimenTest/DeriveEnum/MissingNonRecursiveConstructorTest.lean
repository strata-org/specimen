import Specimen.DeriveEnum

/-- An inductive type with no non-recursive constructors.
    `derive_enum` should emit a clear error rather than panicking. -/
inductive InfiniteTree where
  | node : InfiniteTree → InfiniteTree → InfiniteTree

/-- error: derive Enum failed, InfiniteTree has no non-recursive constructors -/
#guard_msgs in
derive_enum InfiniteTree

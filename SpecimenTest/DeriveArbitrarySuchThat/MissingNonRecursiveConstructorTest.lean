import Specimen

/-- An inductive type with no non-recursive constructors. -/
inductive InfiniteTree' where
  | node : InfiniteTree' → InfiniteTree' → InfiniteTree'

/-- A relation over `InfiniteTree'` whose only constructor is recursive. -/
inductive AlwaysNode : InfiniteTree' → Prop where
  | mk : AlwaysNode l → AlwaysNode r → AlwaysNode (.node l r)

/-- error: Cannot derive constrained producer for 'AlwaysNode': all constructors are recursive (no finite base case) -/
#guard_msgs in
derive_generator (fun _ => ∃ t, AlwaysNode t)

/-- error: Cannot derive constrained producer for 'AlwaysNode': all constructors are recursive (no finite base case) -/
#guard_msgs in
derive_enumerator (fun _ => ∃ t, AlwaysNode t)

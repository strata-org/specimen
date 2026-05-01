set_option genSizeOfSpec false

structure LazyRoseTree (α : Type u) where
  val : α
  children : Thunk (List (LazyRoseTree α))

namespace LazyRoseTree

instance [Inhabited α] : Inhabited (LazyRoseTree α) where
  default := ⟨default, ⟨fun _ => []⟩⟩

partial def map [Inhabited β] (f : α → β) (tree : LazyRoseTree α) : LazyRoseTree β :=
  ⟨f tree.val, ⟨fun _ => tree.children.get.map (map f)⟩⟩

partial def reprTree [Repr α] (tree : LazyRoseTree α) (indent : String := "") : String :=
  let nodeStr := s!"{indent}{repr tree.val}\n"
  let childrenStr := tree.children.get.map (reprTree · (indent ++ "  ")) |> String.join
  nodeStr ++ childrenStr

instance [Repr α] : Repr (LazyRoseTree α) where
  reprPrec tree _ := reprTree tree

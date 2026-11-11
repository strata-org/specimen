import SpecimenTest.Correctness.Suite.Prelude

/-! The unconstrained generators Specimen's own tests derive (`DeriveArbitrary`, `DeriveEnum`), each
proved complete, its searches sound and complete. -/

open Basalt Specimen.Correctness

namespace Suite.Types

inductive BinOp where
  | land | lor | eq | ne | lt | le | gt | ge | add | sub | mul | div | mod | pow | floor
  | lshift | rshift | or | xor | and
deriving instance Basalt.ArbitrarySized for BinOp
instance : ArbitrarySizedComplete BinOp := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch BinOp := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits BinOp := ⟨by arbitrary_hits_derived⟩

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : String)
deriving instance Basalt.ArbitrarySized for Value
instance : ArbitrarySizedComplete Value := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch Value := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Value := ⟨by arbitrary_hits_derived⟩

inductive RegExp : Type where
  | EmptySet | EmptyStr | Char : Nat → RegExp | App : RegExp → RegExp → RegExp
  | Union : RegExp → RegExp → RegExp | Star : RegExp → RegExp
deriving instance Basalt.ArbitrarySized for RegExp
instance : ArbitrarySizedComplete RegExp := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch RegExp := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits RegExp := ⟨by arbitrary_hits_derived⟩

inductive type where
  | Nat : type
  | Fun : type → type → type
inductive term where
  | Const : Nat → term | Add : term → term → term | Var : Nat → term
  | App : term → term → term | Abs : type → term → term
deriving instance Basalt.ArbitrarySized for type
deriving instance Basalt.ArbitrarySized for term
instance : ArbitrarySizedComplete type := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch type := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits type := ⟨by arbitrary_hits_derived⟩
instance : ArbitrarySizedComplete term := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch term := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits term := ⟨by arbitrary_hits_derived⟩

inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
deriving instance Basalt.ArbitrarySized for Tree
instance : ArbitrarySizedComplete Tree := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch Tree := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Tree := ⟨by arbitrary_hits_derived⟩

structure Foo where
  stringField : String
  boolField : Bool
  natField : Nat
deriving instance Basalt.ArbitrarySized for Foo
instance : ArbitrarySizedComplete Foo := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedSearch Foo := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Foo := ⟨by arbitrary_hits_derived⟩

inductive MyList (α : Type) where
  | MyNil : MyList α
  | MyCons : α → MyList α → MyList α
deriving instance Basalt.ArbitrarySized for MyList
instance {α : Type} [ArbitrarySized α] [ArbitrarySizedComplete α] : ArbitrarySizedComplete (MyList α) :=
  ⟨by arbitrary_complete⟩
instance {α : Type} [ArbitrarySized α] [ArbitrarySizedSearch α] : ArbitrarySizedSearch (MyList α) :=
  ⟨by arbitrary_search_derived⟩
instance {α : Type} [ArbitrarySized α] [ArbitrarySizedHits α] : ArbitrarySizedHits (MyList α) :=
  ⟨by arbitrary_hits_derived⟩

end Suite.Types

#print axioms Suite.Types.instArbitrarySizedCompleteTerm
#print axioms Suite.Types.instArbitrarySizedHitsValue

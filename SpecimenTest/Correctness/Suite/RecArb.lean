import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

namespace Suite.RecArb

inductive type where
  | Nat : type
  | Fun : type → type → type
deriving instance Basalt.ArbitrarySized for type
instance : ArbitrarySizedComplete type := ⟨by arbitrary_complete⟩

inductive Color where | red | green | blue
deriving instance Basalt.ArbitrarySized for Color
instance : ArbitrarySizedComplete Color := ⟨by arbitrary_complete⟩

inductive Tree where
  | leaf : Tree
  | node : Color → Nat → Tree → Tree → Tree
deriving instance Basalt.ArbitrarySized for Tree
instance : ArbitrarySizedComplete Tree := ⟨by arbitrary_complete⟩

structure Pt where
  x : Nat
  y : Bool
deriving instance Basalt.ArbitrarySized for Pt
instance : ArbitrarySizedComplete Pt := ⟨by arbitrary_complete⟩

end Suite.RecArb
#print axioms Suite.RecArb.instArbitrarySizedCompleteType
#print axioms Suite.RecArb.instArbitrarySizedCompleteTree
#print axioms Suite.RecArb.instArbitrarySizedCompletePt

namespace Suite.RecArb
instance : ArbitrarySizedSearch type := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits type := ⟨by arbitrary_hits_derived⟩
instance : ArbitrarySizedSearch Color := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Color := ⟨by arbitrary_hits_derived⟩
instance : ArbitrarySizedSearch Tree := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Tree := ⟨by arbitrary_hits_derived⟩
instance : ArbitrarySizedSearch Pt := ⟨by arbitrary_search_derived⟩
instance : ArbitrarySizedHits Pt := ⟨by arbitrary_hits_derived⟩
end Suite.RecArb

import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Specimen.DeriveArbitrary
import Plausible.Attr

open Plausible
set_option guard_msgs.diff true

/-! Experiment: can `deriving Arbitrary` handle `LMonoTy`/`LTy`-shaped types?
    `LMonoTy` has a constructor with a `List LMonoTy` argument (nested recursion
    through `List`), plus a `Nat`-parameterized constructor. This mirrors Strata:
      inductive LMonoTy
        | ftvar (name : String)
        | tcons (name : String) (args : List LMonoTy)   -- nested through List
        | bitvec (size : Nat)
    and the poly type:
      inductive LTy | forAll (vars : List String) (ty : LMonoTy) -/

inductive LMonoTy' where
  | ftvar (name : String)
  | tcons (name : String) (args : List LMonoTy')
  | bitvec (size : Nat)
  deriving Repr

inductive LTy' where
  | forAll (vars : List String) (ty : LMonoTy')
  deriving Repr

deriving instance Arbitrary for LMonoTy'
deriving instance Arbitrary for LTy'

#synth Arbitrary LMonoTy'
#synth Arbitrary LTy'

#eval show IO Unit from do
  let mut i := 0
  while i < 5 do
    let t ← Gen.run (Arbitrary.arbitrary (α := LMonoTy')) 4
    IO.println (repr t)
    i := i + 1

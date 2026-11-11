import SpecimenTest.Correctness.Suite.Prelude

open Basalt Specimen.Correctness

set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option specimen.richOutput false

namespace Suite.ForwardRef
inductive InNat : Nat → List Nat → Prop where
  | here  : InNat x (x :: l)
  | there : InNat x l → InNat x (y :: l)
inductive NotInNat : Nat → List Nat → Prop where
  | nil  : NotInNat x []
  | cons : x ≠ y → NotInNat x l → NotInNat x (y :: l)
inductive Fresh : Nat → List Nat → Nat → Prop where
  | take     : NotInNat cur avoid → Fresh cur avoid cur
  | skipFree : NotInNat cur avoid → Fresh (cur.succ) avoid x → Fresh cur avoid x
  | skipUsed : InNat cur avoid → Fresh (cur.succ) avoid x → Fresh cur avoid x
abbrev Var := Nat × Nat
inductive Chain : List Nat → List Nat → List Var → Prop where
  | done {seen} : Chain seen [] []
  | prefixRef {s seen owed rest} (x r : Nat) :
      Fresh 0 ((s :: seen) ++ owed) x → InNat r (s :: seen) → Chain (x :: s :: seen) owed rest →
      Chain (s :: seen) owed ((x, r) :: rest)
  | forwardRef {seen owed rest} (x r : Nat) :
      Fresh 0 (seen ++ owed) x → Fresh 0 (x :: (seen ++ owed)) r → Chain (x :: seen) (r :: owed) rest →
      Chain seen owed ((x, r) :: rest)
  | fulfillBack {seen ow owed rest} (o r : Nat) :
      InNat o (ow :: owed) → InNat r seen → Chain (o :: seen) ((ow :: owed).erase o) rest →
      Chain seen (ow :: owed) ((o, r) :: rest)
  | fulfillFwd {seen ow owed rest} (o r : Nat) :
      InNat o (ow :: owed) → Fresh 0 (o :: (seen ++ (ow :: owed).erase o)) r →
      Chain (o :: seen) (r :: (ow :: owed).erase o) rest →
      Chain seen (ow :: owed) ((o, r) :: rest)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
derive_mutual generator (∃ (l : List Var), Chain [] [] l)

#specimen_blocks
set_option specimen.parallelProofs true
#specimen_prove_sound
#specimen_prove_all_but []
#specimen_audit ""

end Suite.ForwardRef

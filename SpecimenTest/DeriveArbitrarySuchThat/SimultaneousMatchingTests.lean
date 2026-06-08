import Plausible.Gen
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Specimen.DeriveChecker
import SpecimenTest.CommonDefinitions.ListRelations
import SpecimenTest.DeriveDecOpt.SimultaneousMatchingTests

/-! Tests for `derive_generator` on relations requiring simultaneous pattern matching on multiple inputs. -/

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true


#guard_msgs(drop info) in
derive_generator (fun x => ∃ (l : List Nat), InList x l)


#guard_msgs(drop info) in
derive_generator (fun a => ∃ (l: List Nat), MinOk l a)

#guard_msgs(drop info) in
derive_generator (fun n l' => ∃ (l : List Nat), MinEx n l l')

#guard_msgs(drop info) in
derive_generator (fun x l' => ∃ (l : List Nat), MinEx3 x l l')

#guard_msgs(drop info) in
derive_generator (fun x l => ∃ (l' : List Nat), MinEx2 x l l')

#guard_msgs(drop info) in
derive_generator (fun x l' => ∃ (l : List Nat), MinEx2 x l l')

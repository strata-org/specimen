import Plausible.Gen
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import Plausible.Arbitrary
import SpecimenTest.DeriveArbitrarySuchThat.MultiOutputTest

/-! Test: derive_mutual handles Eq with multi-output indices [1, 2].
    This regressed because Prod construction via mkAppM fails when output types
    live in Sort u (Eq : {α : Sort u} → α → α → Prop). -/

open Plausible

set_option guard_msgs.diff true

set_option specimen.multiOutput true in
set_option specimen.autoDeriveDeps true in
#guard_msgs(drop info) in
derive_mutual
  (∃ (a : Nat) (b : Nat), @Eq Nat a b)

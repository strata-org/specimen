import Plausible.Gen
import Specimen.DecOpt
import Specimen.ArbitrarySizedSuchThat
import Specimen.Enumerators
import Specimen.DeriveChecker
import Specimen.DeriveConstrainedProducer
import Specimen.EnumeratorCombinators
import SpecimenTest.CommonDefinitions.BinaryTree

/-! Test: `set_option specimen.silent true` suppresses all informational
    derivation output — the `Try this:` suggestions from the single-derive
    commands and the widget/text reports from `derive_mutual` — while still
    installing the typeclass instances.

    `#guard_msgs in` (strict, no expected messages) fails if the command emits
    *any* message, so it doubles as an assertion that silent mode is quiet.
    The `#check` lines afterwards confirm the instances were installed
    regardless. Note that silent mode suppresses only *informational* output;
    genuine warnings/errors are diagnostics and are intentionally left alone. -/

open Plausible DecOpt

set_option guard_msgs.diff true

/-! ## Old path — single-derive commands, silent

    Each of these would normally emit a `Try this <kind>: …` suggestion. Under
    `specimen.silent`, `#guard_msgs in` (which allows *no* messages) passes. -/

namespace SilentOld

/-- `Cube n` holds when `n` is a perfect cube. Self-contained (no dependency
    instances needed), so `derive_generator` succeeds standalone. -/
inductive Cube : Nat → Prop where
  | cube n : Cube (n * n * n)

set_option specimen.silent true

#guard_msgs in
derive_checker (fun lo x hi => Between lo x hi)

#guard_msgs in
derive_generator (∃ (m : _), Cube m)

#guard_msgs in
derive_enumerator (∃ (m : _), Cube m)

-- The checker instance was installed despite the silence.
#check (inferInstance : DecOpt (Between 0 1 2))
-- The generator instance was installed despite the silence.
#check (inferInstance : ArbitrarySizedSuchThat Nat (fun m => Cube m))

end SilentOld

/-! ## New path — `derive_mutual`, silent

    Normally emits an HTML widget (info) and/or a plain-text schedule report.
    Under `specimen.silent`, no messages are produced — even with
    `specimen.textOutput` cranked up, which would otherwise force text output. -/

namespace SilentMutual

set_option specimen.autoDeriveDeps true
set_option specimen.silent true
-- textOutput would normally force plain-text info output; silent must win.
set_option specimen.textOutput 3

#guard_msgs in
derive_mutual checker
  (fun lo hi t => BST lo hi t)

-- The checker instance was installed despite the silence.
#check (inferInstance : DecOpt (BST 0 10 .Leaf))

end SilentMutual

/-! ## Default behavior unchanged — suggestions still emitted

    With `silent` at its default (`false`), the single-derive commands still
    produce a `Try this checker:` suggestion. We assert its exact text for a
    trivial relation to confirm nothing is suppressed by default. -/

namespace LoudDefault

/-- `IsZero n` holds exactly when `n = 0`. A minimal relation whose derived
    checker is small enough to pin verbatim. -/
inductive IsZero : Nat → Prop where
  | mk : IsZero 0

/-- info: Try this checker:
      [apply] instance : DecOpt (@LoudDefault.IsZero n_1) where
        decOpt :=
          let rec aux_dec (fuel : Nat) (initSize : Nat) (size : Nat) (n_1 : Nat) : Except Plausible.GenError Bool :=
            (match fuel with
            | Nat.zero => MonadExcept.throw Gen.outOfFuelError
            | Nat.succ fuel' =>
              match size with
              | Nat.zero =>
                DecOpt.checkerBacktrack
                  [fun (_ : Unit) => @DecOpt.decOpt (@Eq (@Nat) n_1 (@OfNat.ofNat (@Nat) 0 (@instOfNatNat 0))) _ initSize]
              | Nat.succ size' =>
                DecOpt.checkerBacktrack
                  [fun (_ : Unit) => @DecOpt.decOpt (@Eq (@Nat) n_1 (@OfNat.ofNat (@Nat) 0 (@instOfNatNat 0))) _ initSize, ])
          fun size => aux_dec 10000 size size n_1
-/
#guard_msgs(whitespace := lax) in
derive_checker (fun n => IsZero n)

end LoudDefault

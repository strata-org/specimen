import Specimen.BasaltBridge

/-!
# Specimen's Basalt path

Import this in any file that derives generators with `set_option specimen.emitBasalt true`. Generators
derived under the flag are emitted against Basalt's `Gen`, `BacktrackGen` and `BacktrackGenFor`, so
those names must resolve in the deriving file; and this module supplies the bridge that lets them run
wherever an `ArbitrarySizedSuchThat` is expected.

It is not part of `import Specimen`: Basalt puts `Gen` at the root namespace, where it is ambiguous
with `Plausible.Gen` in any file with `open Plausible`, so loading it is left to the files that use
it.
-/

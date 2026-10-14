import Specimen.BasaltBridge
import Specimen.DeriveBasaltArbitrary

/-!
# Specimen's Basalt path

Import this in any file that derives generators with `set_option specimen.emitBasalt true`. It brings:

- Basalt's `Gen`, `BacktrackGen` and `BacktrackGenFor`, which generators derived under the flag are
  emitted against, so the names must resolve in the deriving file;
- the bridge that runs a `BacktrackGenFor` wherever an `ArbitrarySizedSuchThat` is expected
  (`Specimen.BasaltBridge`);
- `deriving instance Basalt.ArbitraryFueled for T` (`Specimen.DeriveBasaltArbitrary`), needed for
  every datatype a Basalt-derived generator draws unconstrained values of.

It is not part of `import Specimen`: Basalt puts `Gen` at the root namespace, where it is ambiguous
with `Plausible.Gen` in any file with `open Plausible`, so loading it is left to the files that use it.
-/

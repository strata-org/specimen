import Specimen.BasaltBridge
import Specimen.DeriveBasaltArbitrary

/-!
# Specimen's Basalt path

Import this in any file that derives generators or enumerators with
`set_option specimen.emitBasalt true`. It brings:

- Basalt's `Gen` and Specimen's `Fail`, `FailWith`, `Backtrack`, `Pick`, `BacktrackGenFor` and `EnumFor`, which
  producers derived under the flag are emitted against, so the names must resolve in the deriving file;
- the bridges that run a `BacktrackGenFor` wherever an `ArbitrarySizedSuchThat` is expected and an
  `EnumFor` wherever an `EnumSizedSuchThat` is (`Specimen.BasaltBridge`);
- `deriving instance Basalt.ArbitrarySized for T` (`Specimen.DeriveBasaltArbitrary`), needed for
  every datatype a derived generator or enumerator draws unconstrained values of.

It is not part of `import Specimen`: Basalt puts `Gen` at the root namespace, where it is ambiguous
with `Plausible.Gen` in any file with `open Plausible`, so loading it is left to the files that use it.
-/

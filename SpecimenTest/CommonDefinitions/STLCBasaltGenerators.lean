import Specimen.Basalt
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators

/-!
# Basalt unconstrained generators for the STLC datatypes

The `Plausible.Arbitrary` and `Enum` instances for these types are fixed at `Plausible.Gen` and
`Enumerator`, so a producer emitted against Basalt cannot use them. These are the generator-polymorphic
counterparts, which derived enumerators draw through as well.
A separate module so that `DeriveSTLCTermTypeGenerators`, a test of Plausible's own deriving handler,
stays free of Specimen.
-/

deriving instance Basalt.ArbitraryFueled for type
deriving instance Basalt.ArbitraryFueled for term

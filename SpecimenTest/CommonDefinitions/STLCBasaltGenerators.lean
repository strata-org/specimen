import Specimen.Basalt
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators

/-!
# Basalt unconstrained generators for the STLC datatypes

The `Plausible.Arbitrary` instances in `DeriveSTLCTermTypeGenerators` are fixed at `Plausible.Gen`, so a
generator emitted against Basalt cannot use them. These are the generator-polymorphic counterparts.
A separate module so that `DeriveSTLCTermTypeGenerators`, a test of Plausible's own deriving handler,
stays free of Specimen.
-/

deriving instance Basalt.ArbitraryFueled for type
deriving instance Basalt.ArbitraryFueled for term

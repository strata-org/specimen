-- The SPMF-based correctness development. A root of its own, built alongside `SpecimenTest` but
-- never joined with it: these modules import Mathlib (through Basalt's `SPMF`), and Mathlib's
-- root-level names (`Even`, `BinaryTree`, …) collide with the test suite's own at an import join.

-- The generator interpreter at `SPMF`, soundness and completeness, and the `Ev` generator proved
-- complete through it
import Specimen.Correctness.GenInterpSPMF
import Specimen.Correctness.LeafSPMF
import Specimen.Correctness.EvGenSPMF
-- The derived STLC producers proved sound and complete, directly against the emitted code
-- (each runs its own `derive_mutual`, namespaced so flag-on builds cannot collide)
import SpecimenTest.Correctness.StlcMeasures
import SpecimenTest.Correctness.StlcGeneratorSoundness
import SpecimenTest.Correctness.StlcCompleteness
-- …and the same results through the generic interpreter, bridged to the emitted definitions
import SpecimenTest.Correctness.DerivedGeneratorViaInterp
import SpecimenTest.Correctness.TypingBridge
-- …and the three-valued verdict discipline: an inconclusive premise never becomes a refutation
import SpecimenTest.Correctness.VerdictFidelity
-- The enumeration readings' laws, hosted in `Specimen.Enum`, walked for Basalt's generators, at each
-- reading's choice among branches, and for a derived generator
import Specimen.Enum.Laws
import SpecimenTest.Correctness.EnumLaws
import SpecimenTest.Correctness.EnumBacktrackingTest
import SpecimenTest.Correctness.DerivedEnumLaw
import SpecimenTest.Correctness.DerivedSearchLaw

-- Size as the measure, for two generators in the emitted shape; and the opt-in soundness leaf
import Specimen.Correctness.SizeMeasureExamples
import Specimen.Correctness.WalkSGenSelf
-- Proofs derive_mutual emits (`specimen.emitSound`, `specimen.emitComplete`): the commands' tests (the
-- suite of relations derived with every law proved, `SpecimenTest.Correctness.Suite`, is built
-- module by module, `lakefile.toml`)
import Specimen.Correctness.CheckNegTest
import Specimen.Correctness.CheckSearchTest
import Specimen.Correctness.CheckSoundTest
import Specimen.Correctness.CompleteOfTest
import Specimen.Correctness.CompleteOfTest2
import Specimen.Correctness.CompleteOfTest4
import Specimen.Correctness.EmitSoundTest
import Specimen.Correctness.SearchFindsTest
import Specimen.Correctness.SearchPolyTest
import Specimen.Correctness.SizeSplitTest
import Specimen.Correctness.SoundDecideTest
import Specimen.Correctness.SoundPolyTest

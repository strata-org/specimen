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

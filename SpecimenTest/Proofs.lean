-- The SPMF-based correctness development. A root of its own, built alongside `SpecimenTest` but
-- never joined with it: these modules import Mathlib (through Basalt's `SPMF`), and Mathlib's
-- root-level names (`Even`, `BinaryTree`, …) collide with the test suite's own at an import join.

-- The generator interpreter at `SPMF` — soundness AND completeness, no generator axioms — and the
-- `Ev` slice closed through it
import Specimen.Correctness.GenInterpSPMF
import Specimen.Correctness.EvGenSPMF
-- `Producer` is shared across kinds, and the kinds stay distinct
import SpecimenTest.Correctness.ProducerKindSharing

import Specimen.Correctness.Semantics
import Specimen.Correctness.Combinators
import Specimen.Correctness.Reflect
import Specimen.Correctness.CheckerInterp
import Specimen.Correctness.ProducerInterp
import Specimen.Correctness.GenAxioms
import Specimen.Correctness.GenInterp
import Specimen.Correctness.EvSlice

/-!
# `Specimen.Correctness`

Machine-checked soundness and completeness of specimen's derived generators, enumerators, and
checkers, following *Computing Correctly with Inductive Relations* (PLDI'22).

Modules:
* `Semantics`   — outcome-set semantics for the three producers + soundness/completeness targets.
* `Combinators` — relation-independent specs of the checker and enumerator combinators (paper §2).
* `Reflect` — a relation as data (`RelSpec`) with an inductive denotation (`Provable`), so that
  theorems can quantify over relations.
* `CheckerInterp` — checkers as the fuel-iteration of a one-level step: soundness, refutation
  soundness, and bounded refutation for structurally decreasing relations, proved once.
* `ProducerInterp` — the same for enumerators, over `List`: soundness and completeness.
* `GenInterp` — the same for generators at the real `Plausible.Gen`: soundness, with no axioms.
* `GenAxioms` — two QuickChick-style support laws for `Plausible.Gen`, postulated; see the file for why
  they are an idealization and which results use them.
* `EvSlice` — evenness end to end: checker, enumerator and generator proved sound and complete, and
  `Ev` reflected as a `RelSpec`.
* `GenInterpSPMF` / `EvGenSPMF` — the generator interpreter again, at Basalt's `SPMF`: soundness
  **and** completeness with no generator axioms (the support laws are theorems there), and the `Ev`
  slice closed through it. NOT imported here: `SPMF` sits on Mathlib, whose root-level names clash
  with this test suite's at an import join, so the SPMF development is built from the separate
  `SpecimenTest.Proofs` root instead.

Not imported by `Specimen`: the development is built by the test library.
-/

import Specimen.Correctness.Semantics
import Specimen.Correctness.Combinators
import Specimen.Correctness.Reflect
import Specimen.Correctness.CheckerInterp
import Specimen.Correctness.ProducerInterp
import Specimen.Correctness.GenSupport
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
* `GenSupport` — the support laws for `Plausible.Gen` in the soundness direction, proved. The reverse
  direction does not hold there, because `>>=` threads the seed rather than splitting it.
* `EvSlice` — evenness end to end: checker and enumerator sound and complete, generator sound, and
  `Ev` reflected as a `RelSpec`.
* `GenInterpSPMF` / `EvGenSPMF` — the generator interpreter again, at Basalt's `SPMF`: soundness
  **and** completeness (the support laws are theorems there), and the `Ev` generator proved complete
  through it. NOT imported here: `SPMF` sits on Mathlib, whose root-level names clash
  with this test suite's at an import join, so the SPMF development is built from the separate
  `SpecimenTest.Proofs` root instead.

Not imported by `Specimen`: the development is built by the test library.
-/

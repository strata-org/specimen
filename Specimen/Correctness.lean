import Specimen.Correctness.Semantics
import Specimen.Correctness.Combinators
import Specimen.Correctness.Reflect
import Specimen.Correctness.CheckerInterp
import Specimen.Correctness.ProducerInterp
import Specimen.Correctness.GenAxioms
import Specimen.Correctness.GenInterp

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

Not imported by `Specimen`: the development is built by the test library.
-/

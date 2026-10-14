import Specimen.Correctness.Semantics
import Specimen.Correctness.Combinators

/-!
# `Specimen.Correctness`

Machine-checked soundness and completeness of specimen's derived generators, enumerators, and
checkers, following *Computing Correctly with Inductive Relations* (PLDI'22).

Modules:
* `Semantics`   — outcome-set semantics for the three producers + soundness/completeness targets.
* `Combinators` — relation-independent specs of the checker and enumerator combinators (paper §2).

Not imported by `Specimen`: the development is built by the test library.
-/

import SpecimenTest.ArithCompiler.ArithCompiler
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Testable
import Plausible.DeriveShrinkable

/-! Property-based tests for the arithmetic expression compiler defined in `ArithCompiler.lean`. -/

open Plausible
open Plausible.Arbitrary

def store0 : Store := []

def compiler_correct (stmt : Stmt) : Prop :=
  let mstore' := execProg (compileStmt stmt) (optStateFromStore store0)
  let mstore'' := optStateFromStore (evalStmt store0 stmt)
  mstore' = mstore''

instance (stmt : Stmt) : Decidable (compiler_correct stmt) :=
  inferInstanceAs (Decidable (_ = _))

deriving instance Shrinkable for AExpr, BExpr, Stmt

instance : SampleableExt Stmt := inferInstance

#eval Testable.check (∀ stmt : Stmt, compiler_correct stmt)
  (cfg := {numInst := 100, maxSize := 5, quiet := true})
--  (cfg := {numInst := 100, maxSize := 5, quiet := false, traceSuccesses := true})

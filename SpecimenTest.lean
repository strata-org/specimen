/-
Copyright (c) 2024 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/

-- Common definitions for snapshot tests
import SpecimenTest.CommonDefinitions.BinaryTree
import SpecimenTest.CommonDefinitions.FunctionCallInConclusion
import SpecimenTest.CommonDefinitions.ListRelations
import SpecimenTest.CommonDefinitions.Permutation
import SpecimenTest.CommonDefinitions.STLCDefinitions

-- Tests for `derive_generator` (derives `ArbitrarySuchThat`)
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBSTGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator
import SpecimenTest.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator
import SpecimenTest.DeriveArbitrarySuchThat.SimultaneousMatchingTests
import SpecimenTest.DeriveArbitrarySuchThat.FunctionCallsTest
import SpecimenTest.DeriveArbitrarySuchThat.GetElemPremiseTest
import SpecimenTest.DeriveArbitrarySuchThat.DelegatedProducerTest
import SpecimenTest.DeriveArbitrarySuchThat.DelegatedProducerRepeatedVarTest
import SpecimenTest.DeriveArbitrarySuchThat.DerivePermutationGenerator
import SpecimenTest.DeriveArbitrarySuchThat.MutuallyRecursiveRelationsTest
import SpecimenTest.DeriveArbitrarySuchThat.WithUnfolds
import SpecimenTest.DeriveArbitrarySuchThat.Syntax
import SpecimenTest.DeriveArbitrarySuchThat.DependentArgs
import SpecimenTest.DeriveArbitrarySuchThat.DependentOutputTypeTest
import SpecimenTest.DeriveArbitrarySuchThat.InstanceParameterTest
import SpecimenTest.DeriveArbitrarySuchThat.NEqGenerator
import SpecimenTest.DeriveArbitrarySuchThat.MissingNonRecursiveConstructorTest
import SpecimenTest.DeriveArbitrarySuchThat.ForwardRefListGenerator

-- Tests for `deriving Arbitrary`
import SpecimenTest.DeriveArbitrary.DeriveTreeGenerator
import SpecimenTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import SpecimenTest.DeriveArbitrary.DeriveNKIValueGenerator
import SpecimenTest.DeriveArbitrary.DeriveNKIBinopGenerator
import SpecimenTest.DeriveArbitrary.DeriveRegExpGenerator
import SpecimenTest.DeriveArbitrary.StructureTest
import SpecimenTest.DeriveArbitrary.StructureParameterTest
import SpecimenTest.DeriveArbitrary.BitVecStructureTest
import SpecimenTest.DeriveArbitrary.MissingNonRecursiveConstructorTest
import SpecimenTest.DeriveArbitrary.ParameterizedTypeTest
import SpecimenTest.DeriveArbitrary.MutuallyRecursiveTypeTest
import SpecimenTest.DeriveArbitrarySuchThat.DeriveSTLCGenerator
import SpecimenTest.DeriveArbitrarySuchThat.NonLinearPatternsTest
import SpecimenTest.DeriveArbitrarySuchThat.MultiOutputTest
import SpecimenTest.DeriveArbitrarySuchThat.MultiOutputSTLCTest
import SpecimenTest.DeriveArbitrarySuchThat.EqMultiOutputTest
import SpecimenTest.DeriveArbitrarySuchThat.UserInstancePriorityTest
import SpecimenTest.DeriveArbitrarySuchThat.BoundedBuffer

-- Tests for instances of `Enum` for simple types and for correctness of enumerator combinators
import SpecimenTest.Enum.EnumInstancesTest
import SpecimenTest.Enum.EnumeratorSizeTest

-- Tests for `deriving Enum`
import SpecimenTest.DeriveEnum.DeriveTreeEnumerator
import SpecimenTest.DeriveEnum.DeriveSTLCTermTypeEnumerators
import SpecimenTest.DeriveEnum.DeriveNKIValueEnumerator
import SpecimenTest.DeriveEnum.DeriveNKIBinopEnumerator
import SpecimenTest.DeriveEnum.DeriveRegExpEnumerator
import SpecimenTest.DeriveEnum.StructureTest
import SpecimenTest.DeriveEnum.BitVecStructureTest
import SpecimenTest.DeriveEnum.MissingNonRecursiveConstructorTest
import SpecimenTest.DeriveEnum.NestedAndMutualRecursionTest
import SpecimenTest.DeriveEnum.StructureParameterTest

-- Tests for `derive_checker` (derives `DecOpt`)
import SpecimenTest.DeriveDecOpt.DeriveBSTChecker
import SpecimenTest.DeriveDecOpt.DeriveBalancedTreeChecker
import SpecimenTest.DeriveDecOpt.DeriveRegExpMatchChecker
import SpecimenTest.DeriveDecOpt.SimultaneousMatchingTests
import SpecimenTest.DeriveDecOpt.ExistentialVariablesTest
import SpecimenTest.DeriveDecOpt.FunctionCallsTest
import SpecimenTest.DeriveDecOpt.DeriveSTLCChecker
import SpecimenTest.DeriveDecOpt.NonLinearPatternsTest
import SpecimenTest.DeriveDecOpt.DerivePermutationChecker

-- Tests for `derive_enumerator` (derives `EnumSuchThat`)
import SpecimenTest.DeriveEnumSuchThat.DeriveBSTEnumerator
import SpecimenTest.DeriveEnumSuchThat.DeriveBalancedTreeEnumerator
import SpecimenTest.DeriveEnumSuchThat.DeriveRegExpMatchEnumerator
import SpecimenTest.DeriveEnumSuchThat.SimultaneousMatchingTests
import SpecimenTest.DeriveEnumSuchThat.DeriveSTLCEnumerator
import SpecimenTest.DeriveEnumSuchThat.NonLinearPatternsTest
import SpecimenTest.DeriveEnumSuchThat.DerivePermutationEnumerator

-- Key Value Store Example
import SpecimenTest.KeyValueStoreExample.KeyValueStore
import SpecimenTest.KeyValueStoreExample.TestKeyValueStoreCheckerGenerators
import SpecimenTest.KeyValueStoreExample.BackwardFailingTraces

-- Cedar Example
import SpecimenTest.CedarExample.Cedar
import SpecimenTest.CedarExample.CedarCheckerGenerators
import SpecimenTest.CedarExample.CedarWellTypedTermGenerator

-- Strata Lambda Example: well-typed `LExpr` generator via `HasTypeA`
import SpecimenTest.StrataLexprGen

-- Arithmetic Compiler Example
-- Note: ArithCompilerTest and FancyCompilerBuggyTest can't be imported together
-- because they define conflicting `Instr` types.
import SpecimenTest.ArithCompiler.FancyCompilerBuggyTest

-- Schedule quality regression tests
import SpecimenTest.ScheduleQualityRegressionTest

-- Weight function / modifier customization tests
import SpecimenTest.WeightCustomizationTest
import SpecimenTest.WeightPrecomputeTest

-- `specimen.silent` output-suppression option tests
import SpecimenTest.SilentOptionTest

-- Inconclusive errors are classified the same way on every producer path
import SpecimenTest.InconclusiveErrorTest
-- …and `andOpt` is K3 conjunction: a definite `false` decides it even beside an inconclusive operand
import SpecimenTest.AndOptTest
-- …and a derived generator skips constructors its inputs cannot match (`specimen.dispatchInputs`)
import SpecimenTest.DispatchInputsTest
-- …and seeded generator runs are reproducible
import SpecimenTest.SeededRunTest
-- `derive_mutual` on a relation with no inputs: the second weight-emission path
import SpecimenTest.InputFreeDeriveMutualTest
-- `n + k` indices are matched as `Nat.succ` patterns, not solved by enumeration
import SpecimenTest.ArithIndexTest
-- …and a type abbreviation used as a type argument is a type, not a function call
import SpecimenTest.TypeAbbrevArgTest
-- …and a match on a one-constructor structure emits no redundant failure arm
import SpecimenTest.IrrefutableMatchTest
-- Pattern coverage: the input-space trie and per-leaf scoring
import SpecimenTest.PatternCoverageTest
-- …and `scoped derive_mutual`: instances visible only where their namespace is open
import SpecimenTest.ScopedInstanceTest
-- …and a constructor a mode was derived without is reported under `trace.specimen.droppedCtors`
import SpecimenTest.DroppedCtorsTraceTest
-- …and a large mutual block of workers recurses structurally on `fuel`, not by well-founded recursion
import SpecimenTest.StructuralFuelTest

-- `specimen_test` command / `specimen` tactic
import SpecimenTest.TacticTest



-- Runtime schedule interpreter: derive a mode from data, reorder premises, profile the discards
import SpecimenTest.Interp.BSTInterpTest
-- …and read the relation-as-data straight off the declaration with `derive_relspec`
import SpecimenTest.Interp.ExtractTest
-- …and keep a variable repeated inside one conclusion argument linear, as the deriver does
import SpecimenTest.Interp.NonLinearConclusionTest
-- …and attribute a discard to the premise that emitted it in the schedule actually installed
import SpecimenTest.Interp.ProvenanceTest
-- …and derive the `Val` bridge, so the interpreter can be pointed at a real project's own types
import SpecimenTest.Interp.DerivingTest
-- …and learn a whole generator from where it discards, stopping at the irreducible
import SpecimenTest.Interp.LearnTest
-- …and interpret the other two producer sorts (checker, enumerator) end-to-end
import SpecimenTest.Interp.CheckEnumTest
-- …and never mistake interpreter misconfiguration for a discard: `backtrack` absorbing it hid a rule
-- that could never run
import SpecimenTest.Interp.InternalErrorTest
-- …and transfer a measured premise order back to the compile-time deriver, which only works if the two
-- lowerings agree step for step
import SpecimenTest.Interp.PinnedOrderTest
-- …and start learning from the deriver's own branch-and-bound choice, so what learning changes reads as
-- a diff against static
import SpecimenTest.Interp.FromCompiledTest
-- …and certify that the compiled start really runs what the deriver emitted, with a comparator that can
-- call two equivalent schedules different but never two different ones the same
import SpecimenTest.Interp.ScheduleEquivTest
-- …and keep the interpreter's hand-registered leaves in step with the instances Lean can synthesise,
-- since drifting either way makes a plan measurable here and unemittable there
import SpecimenTest.Interp.CorrespondenceTest
-- …and resolve leaves from the instances in scope, so the interpreter measures the compiled generator
import SpecimenTest.Interp.InstanceLeavesTest
-- …and follow blame from a measured rejection to the premises that could be reordered, including up into
-- the caller when the inputs are what decided it
import SpecimenTest.Interp.BlameTest
-- …and diagnose a constructor that rarely succeeds: localize its failing step, trace a blind choice to the
-- premise that made it, and try the anchor move and size floor the diagnosis names
import SpecimenTest.Interp.DiagnoseTest

-- Generators emitted against Basalt under `specimen.emitBasalt`: run with the flag set in-file, so the
-- default build covers the Basalt path too. Test files that derive generators import `Specimen.Basalt`
-- so the whole library can also be built with the flag on (see the comment in `lakefile.toml`).
import SpecimenTest.BasaltEmissionTest
import SpecimenTest.BasaltEnumeratorTest
import SpecimenTest.CheckerSearchTest
-- …and without `Specimen.Basalt`, Basalt stays unloaded and the flag asks for the import
import SpecimenTest.BasaltNotImportedTest
-- …and a dependency with only a hand-written Plausible generator is derived for Basalt, not missed
import SpecimenTest.BasaltDependencyLookupTest
-- Constraint propagation for polymorphic dependencies (issue #38)
import SpecimenTest.PolymorphicDepConstraints

-- Soundness and completeness proofs for derived producers (Computing Correctly with Inductive Relations)
import Specimen.Correctness
-- …and the checker `derive_checker` really emits, proved sound through the generic two-counter theory
import SpecimenTest.Correctness.DerivedCheckerSoundness
-- The SPMF-based correctness files are NOT imported here: they sit on Mathlib (through Basalt's
-- `SPMF`), whose root-level names (`Even`, `BinaryTree`, …) clash with this suite's at an import
-- join. They are built from the separate `SpecimenTest.Proofs` root instead.

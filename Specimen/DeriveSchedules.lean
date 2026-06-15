import Lean.Expr
import Lean.Elab.Term
import Specimen.Utils
import Specimen.Schedules
import Specimen.Scoring
import Specimen.UnificationMonad
import Specimen.MakeConstrainedProducerInstance
import Specimen.LazyList
import Specimen.SearchTree
import Specimen.Debug
import Lean.Util.SCC

namespace Schedules

open Lean Meta Elab Term
open Schedules

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- Extracts all the unique variable names that appear in a hypothesis of a constructor for an inductive relation
    (this looks underneath constructor applications).

    For example, given `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`,
    this function returns `[Γ, τ1, e, τ2]`.
 -/
partial def variablesInHypothesisTSyntax (term : TSyntax `term) : MetaM (List Name) :=
  match term with
  | `($id:ident) => return [id.getId.eraseMacroScopes]
  | `($_:ident $args:term*)
  | `(($_:ident $args*)) => do
    -- Note that we have to explicitly pattern match on parenthesized constructor applications,
    -- otherwise we won't be able to handle nested constructor applications, e.g. `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`
    let foo ← args.toList.flatMapM variablesInHypothesisTSyntax
    return (List.eraseDups foo)
  | _ => return []

/-- Extracts all variable names that appear in a `ConstructorExpr`
    (this looks underneath constructor applications).
    Note: names may appear more than once if a variable occurs in multiple positions. -/
def variablesInConstructorExpr (ctorExpr : ConstructorExpr) : List Name :=
  match ctorExpr with
  | .Unknown u => [u]
  | .Ctor _ args | .FuncApp _ args | .TyCtor _ args => args.flatMap variablesInConstructorExpr
  | .Lit _ => []
  | .CSort _ => []

/-- Given a hypothesis `hyp`, along with `binding` (a list of variables that we are binding with a call to a generator), plus `recCall` (a pair contianing the name of the inductive and a list of output argument indices),
    this function checks whether the generator we're using is recursive.

    For example, if we're trying to produce a call to the generator [(e, tau) ← typing gamma _ _], then
    we would have `binding = [e,tau]` and `hyp = typing gamma e tau`. -/
def isRecCall (binding : List Name) (typeVars : List Name) (hyp : HypothesisExpr) (recCall : Name × List Nat) : MetaM Bool := do
  let (ctorName, args) := hyp
  -- An output position is a position where all vars contained are unbound
  -- if they are unbound, we include them in the list of output indices (`outputPositions`)
  let outputPositions ← filterMapMWithIndex (fun i arg => do
    let vars := variablesInConstructorExpr arg
    if vars.isEmpty then pure none else
    let varsSubsetBinding := vars ⊆ binding
    let varsSubsetTypeVars := vars ⊆ typeVars
    if varsSubsetBinding && !varsSubsetTypeVars then
      pure (some i)
    else if !varsSubsetBinding && vars.any (· ∈ binding) then
      let v := List.find? (· ∈ binding) vars
      let vn := List.find? (· ∉ binding) vars
      throwError m!"error: {v} ∈ {binding} and {vn} ∉ {binding}\nArguments to hypothesis {hyp} contain both fixed and yet-to-be-bound variables (not allowed)"
    else pure none
  ) args

  let (inductiveName, recCallOutputIdxes) := recCall

  trace[plausible.deriving.arbitrary] m!"isRecCall: typeVars: {typeVars} binding {binding} hyp: {hyp} args: {args} outputsPos: {outputPositions} recCall: {recCall}"

  return (ctorName == inductiveName && (recCallOutputIdxes.mergeSort) == (outputPositions.mergeSort))

/-- Given a list of `hypotheses` of an inductive constructor, each containing a list of arguments,
    pairs each hypothesis with a list containing, for each argument, a list of the variables contained
    inside that argument. For instance:

    `(C a (K b (H c d)) (3 * e))` is paired with `[[a],[b,c,d],[e]]`
    It then sorts the list of hypotheses with variables by the total number of variables across all
    arguments.
    (This is a heuristic, since we would like to work w/ hypotheses that have fewer variables first (fewer generation options to deal with).) -/
def mkSortedHypothesesVariablesMap (hypotheses : List HypothesisExpr) : List (HypothesisExpr × List (List Name)) :=
  let hypVarMap := hypotheses.map (fun h@(_, ctorArgs) =>
    (h, ctorArgs.map variablesInConstructorExpr))
  List.mergeSort hypVarMap (le := fun (_, vars1) (_, vars2) => vars1.flatten.length <= vars2.flatten.length)

/-- Environment for the `ScheduleM` reader monad -/
structure ScheduleEnv where
  /-- List of variables which are universally-quantified in the constructor's type,
      along with the types of these variables -/
  vars : List TypedVar

  /-- Hypotheses about the variables in `vars` -/
  sortedHypotheses : List (HypothesisExpr × List (List Name))

  /-- Determines whether we're deriving a checker/enumerator/generator -/
  deriveSort : DeriveSort

  /-- The sort of auxiliary producer (generators / enumerators) invoked by
      the function being derived. Note that if `deriveSort = Checker`, then
      `prodSort = Enumerator`, since checkers have to invoke enumerators
      as discussed in the Computing Correctly paper. -/
  prodSort : ProducerSort

  /-- A pair contianing the name of the inductive relation and a list of indices for output arguments -/
  recCall : Name × List Nat

  /-- A list of fixed variables (i.e. inputs to the inductive relation) -/
  fixed : List Name

  /-- The (possibly freshened) name of the recursive helper function
      (e.g. `aux_dec`, `aux_arb`, `aux_enum`). -/
  recFnName : Name

  /-- When true, each hypothesis produces all available outputs at once -/
  multiOutput : Bool := false

  /-- Sibling specs in a mutual derivation block.
      Each entry is (inductiveName, outputIndices, auxFnName, siblingDeriveSort).
      When a hypothesis matches a sibling (exact same inductive + output positions + compatible sort),
      it emits Source.MutRec instead of Source.NonRec.
      Currently only same-sort mutual calls are supported (gen↔gen, checker↔enum). -/
  mutualSiblings : List (Name × List Nat × Name × DeriveSort) := []

  /-- Memoization for recursive dependency derivation.
      When set, the step scorer uses this to recursively derive deps and cache results.
      Keys that map to `inProgress` indicate a cycle (mutual recursion). -/
  depMemo : Option (IO.Ref (Std.HashMap SpecKey MemoEntry)) := none

/-- A monad for deriving generator schedules. Under the hood,
    `ScheduleM` is just a reader monad stacked on top of `MetaM`,
    with `ScheduleEnv` serving as the environment for the reader monad. -/
abbrev ScheduleM (α : Type) := ReaderT ScheduleEnv MetaM α

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far  -/
def collectCheckSteps (env : ScheduleEnv) (boundVars : List Name) (checkedHypotheses : List Nat) : List (Nat × Source) := do
  let (inductiveName, inputArgs) := env.recCall

  let toCheckSource hyp :=
    let (ctorName, ctorArgs) := hyp
    if env.deriveSort == DeriveSort.Checker && inputArgs.isEmpty && ctorName == inductiveName then
      Source.Rec env.recFnName ctorArgs
    else .NonRec hyp

  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (List.all · (· ∈ boundVars)) then
      some (i, toCheckSource hyp)
    else none) env.sortedHypotheses

  checkSteps

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far. This version returns raw
    hypothesisExprs without checking what their source (recursive/nonrecursive) should be.  -/
def collectCheckedHypotheses (env : ScheduleEnv) (boundVars : List Name) (checkedHypotheses : List Nat) : List (Nat × HypothesisExpr) := do
  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (List.all · (· ∈ boundVars)) then
      some (i, hyp)
    else none) env.sortedHypotheses

  checkSteps

/-- Determines whether inputs & outputs of a generator appear under the same constructor in a hypothesis `hyp`
    - Example: consider the `TApp` constructor for STLC (when we are generating `e` such that `typing Γ e τ` holds):
    ```
    | TApp: ∀ Γ e1 e2 τ1 τ2,
      typing Γ e2 τ1 →
      typing Γ e1 (.Fun τ1 τ2) →
      typing Γ (.App e1 e2) τ2
    ```
    The hypothesis `typing Γ e1 (.Fun τ1 τ2)` contains a term `.Fun τ1 τ2` where
    the existentially quantified variable `τ1` hasn't been generated yet,
    whereas `τ2` is an input to the generator (since it appears in the conclusion of `TApp`).
    Since `τ1, τ2` both appear under the same `.Fun` constructor,
    `outputInputNotUnderSameConstructor (.Fun τ1 τ2) [τ2]` returns `false`.  -/
def outputInputNotUnderSameConstructor (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool := do
  let (_, args) := hyp
  let result ← not <$> args.anyM (fun arg => do
    let vars := variablesInConstructorExpr arg
    return List.any vars (. ∈ outputVars) && List.any vars (. ∉ outputVars))
  return result

/-- Determines whether the variables in `outputVars` are constrained by a function application or type constructor in the hypothesis `hyp`.
    This function is necessary since we can't output something and then assert that it equals the output of a (non-constructor) function
    (since we don't have access to the function). -/
partial def outputsNotConstrainedByFunctionApplication (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool :=
  let (_, args) := hyp
  not <$> args.anyM (fun arg => check false arg)
    where
      check (b : Bool) (arg : ConstructorExpr) : ScheduleM Bool :=
        match arg with
        | .Unknown u => return (b && u ∈ outputVars)
        | .Ctor _ args => args.anyM (check b)
        | .TyCtor _ args
        | .FuncApp _ args => args.anyM (check true)
        | .Lit _ => return false
        | .CSort _ => return false

private inductive OptionallyTypedVar where
| TVar : TypedVar -> OptionallyTypedVar
| UVar : Name -> OptionallyTypedVar
  deriving Repr, BEq

/-- If we have a hypothesis that we're generating an argument for,
     and that argument is a constructor application where all of its args are outputs,
     then we just need to produce a backtracking check

     e.g. if we're trying to generate `TFun t1 t2 ← typing G e (TFun t1 t2)`,
     we have to do:
     ```
       v_t1t2 ← typing G e v_t1t2
       match v_t1t2 with
       | TFun t1 t2 => ...
       | _ => none
     ```
     assuming t1 and t2 are *unfixed* (not an input and not generated yet)

     The triple that is output consists of:
     - the list of pattern-matches that need to be produced
       (since TT can handle multiple outputs, each of which may need to be constrained by a pattern)
     - the updated thing we're generating for (e.g. `typing G e v_t1t2` in the example above), ie the RHS of the let-bind
     - the updated output list (e.g. `v_t1t2` in the example above), ie the LHS of the let-bind
     TODO: This function's purpose is to find all the matches that needs to be done for this output, but it tries to do it by looking
     which indicies need to be outputs by searching in them, but we have that info in preschedules, could just use that, filter
     to those indices, and perform the matches.

     -/
def handleConstrainedOutputs (hyp : HypothesisExpr) (outputVars : List TypedVar) : MetaM (List ScheduleStep × HypothesisExpr × List (OptionallyTypedVar)) := do
  let (ctorName, ctorArgs) := hyp

  let outputNamesTypes := outputVars.map (fun x => (x.var, x.type))

  let (patternMatches, args', newOutputs) ← splitThreeLists <$> ctorArgs.mapM (fun arg => do
    let vars := variablesInConstructorExpr arg

    match arg with
    | .Ctor _ _ =>
      match List.mapM (outputNamesTypes.lookup .) vars with
      | none => pure (none, arg, none)

      | some typedOutputs =>
      if !vars.isEmpty && !typedOutputs.all (fun x => x.isSort) then do
        let localCtx ← getLCtx
        let newName := localCtx.getUnusedName (Name.mkStr1 ("v" ++ String.intercalate "_" (Name.getString! <$> vars)))
        match patternOfConstructorExpr arg with
        | none => throwError m!"ConstructorExpr {arg} fails to be converted to pattern in handleConstrainedOutputs"
        | some pat =>
          let newMatch := ScheduleStep.Match .allExplicit newName pat
          pure (some newMatch, .Unknown newName, some (.UVar newName))
      else
        pure (none, arg, none)
    | .Unknown v =>
      match outputNamesTypes.lookup v with
      | some ty =>
        if ty.isSort then
          pure (none, arg, none)
        else
          pure (none, arg, some (.TVar ⟨v,ty⟩))
      | none  =>
        pure (none, arg, none)
    | .FuncApp _ _  | .TyCtor _ _ =>
      pure (none, arg, none)
    | .Lit _ =>
      pure (none, arg, none)
    | .CSort _ =>
      pure (none, arg, none)

      )

  return (patternMatches.filterMap id, (ctorName, args'), newOutputs.filterMap id)

/-Lazily enumerates pairs where the first elements is all subsets of
  the given list `as` and the second element is the complement-/
private def subsetsAndComplements {α} (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) ← subsetsAndComplements as'
    .lcons (a :: subset, comp) ⟨ fun _ => .lcons (subset, a :: comp) ⟨fun _ => .lnil⟩⟩

/- Unused utility function for future if we wish to prune selections of hypotheses by some predicate -/
private def subsetsAndComplementsSuchThat {α} (p : α -> Bool) (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) ← subsetsAndComplementsSuchThat p as'
    if p a then
    .lcons (subset,a :: comp) ⟨ fun _ => .lcons (a :: subset, comp) ⟨fun _ => .lnil⟩⟩
    else
    .lcons (subset,a::comp) ⟨ fun _ => .lnil ⟩

/-Select takes a list `as` and lazily enumerates pairs of all elements of the list with the unselected remainder of the list-/
def select {α} (as : List α) : LazyList (α × List α) :=
  match as with
  | [] => .lnil
  | a :: as' =>
    .lcons (a, as') ⟨fun _ => LazyList.mapLazyList (fun (x,as'') => (x, a::as'')) (select as')⟩

/-- A `PreScheduleStep α v` is a simplified representation of a `ScheduleStep`. It is parameterized by
  `α`, which represents a hypothesis, and `v`, which is the type of variables. The first parameter
  is useful if we want to construct a preschedule without carrying around a complex representation
  of a hypothesis, the second is useful because we can represent both type-annotated and unannotated
  preschedules. -/
private inductive PreScheduleStep α v where
| Checks (hyps : List α) /- Check a sequence of hypotheses. -/
| Produce (out : List v) (hyp : α) /- Produce a list of variables `out` such that they satisfy hypotheses `hyp`. -/
| InstVars (var : List v) /- Instantiate a list of variables according to their type, unconstrained(Arbitrary/Enum). -/
deriving Repr

instance [Repr α] [Repr v] : Repr (List (PreScheduleStep α v)) where
  reprPrec steps _ :=
    let lines := steps.map fun step =>
      match step with
      | .InstVars vars => s!"{repr vars} ← arbitrary"
      | .Produce out hyp => s!"{repr out} ← {repr hyp}"
      | .Checks hyps => s!"check {repr hyps}"
    "do\n  " ++ String.intercalate "\n  " lines

private def collectRepeatedNames (lists : List (List Name)) : List Name :=
  let allNames := lists.flatten
  let counts := allNames.foldl (fun (acc : NameMap Nat) name => acc.alter name (fun opt => some ((opt.getD 0) + 1))) {}
  counts.toList.filterMap (fun (name, count) =>
    if count > 1 then some name else none)

private partial def containsFunctionCall (ctrExpr : ConstructorExpr) : Bool :=
  match ctrExpr with
  | .Unknown _ => false
  | .Ctor _ args | .TyCtor _ args => List.any args (fun x => containsFunctionCall x)
  | .FuncApp _ _ => true
  | .Lit _ => false
  | .CSort _ => false

private partial def tyCtorConstrainsVariable (ctrExpr : ConstructorExpr) : Bool :=
  match ctrExpr with
  | .Unknown _ => false
  | .Ctor _ args | .FuncApp _ args => args.any tyCtorConstrainsVariable
  | .TyCtor _ _ => !(variablesInConstructorExpr ctrExpr).isEmpty
  | .Lit _ => false
  | .CSort _ => false

private def constructHypothesis (typeVars : List Name) (hyp : HypothesisExpr × List (List Name)) : HypothesisExpr × List (List Name) × List Name :=
  let repeatedNames := collectRepeatedNames hyp.snd
  let hypIndices := List.zip hyp.fst.snd hyp.snd
  let (mustBind, allSafe) := hypIndices.partition (fun (ctrExpr, vars) =>
    containsFunctionCall ctrExpr || tyCtorConstrainsVariable ctrExpr || (vars.any (fun v => v ∈ repeatedNames && v ∉ typeVars)))
  -- Any variables that appear multiple times in a hypothesis will end up in mustBind the same number of times, so we must deduplicate
  -- to avoid instantiating it multiple times.
  (hyp.fst, allSafe.map (fun x => x.snd), (List.eraseDups mustBind).flatMap (fun x => x.snd))

private def needs_checking {α v} [BEq v] (env : List v) (a_vars : α × List (List v) × List v) : Bool :=
  let (_, potentialIndices, alwaysBound) := a_vars
  alwaysBound.all (List.contains env) &&
  potentialIndices.all (fun idx => idx.all (List.contains env))

private def prune_empties {α v} (schd : List (PreScheduleStep α v)) : List (PreScheduleStep α v) :=
  schd.foldr aux []
  where
    aux pss l :=
      match pss with
      | .Checks [] => l
      | .InstVars [] => l
      | .Produce [] h => .Checks [h] :: l
      | _ => pss :: l

def computeSCC {v a} [DecidableEq v] (hypotheses : List (a × List v)) : List (List (a × List v)) :=
  let indices := List.range hypotheses.length
  let successors := fun i =>
    indices.filter fun j =>
      i ≠ j &&
      match hypotheses[i]?, hypotheses[j]? with
      | some (_, vars), some (_, vars') => vars.any (· ∈ vars')
      | _, _ => false
  let sccIndices := Lean.SCC.scc indices successors
  sccIndices.map fun component =>
    component.filterMap (fun i => hypotheses[i]?)

-- Two connected components {H} and {I,J}, as the latter share the variable 5
/--info: [[("H", [1, 2, 3]), ("J", [5, 1]), ("I", [4, 5])]]-/
#guard_msgs(all) in
#eval computeSCC [("H", [1,2,3]), ("I", [4,5]), ("J",[5,1])]

-- Example: Two connected components H1{a,b,c} & H2{a} vs H3{d} & H4{d,e}; the first two share a, the latter two share d
/--info: [[("H1", ["a", "b", "c"]), ("H2", ["a"])], [("H3", ["d"]), ("H4", ["d", "e"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a", "b", "c"]), ("H2", ["a"]), ("H3", ["d"]), ("H4", ["d", "e"])]

-- Example: Transitive dependencies make one big connected component.
/--info: [[("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]), ("H4", ["c"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]), ("H4", ["c"])]

-- Example: No overlap so all hypotheses are singleton components.
/--info: [[("H1", ["a"])], [("H2", ["b"])], [("H3", ["c"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a"]), ("H2", ["b"]), ("H3", ["c"])]


/- For each permutation, for each of its hypotheses, select which of its
unbound variables should be instantiated to satisfy it.
Not all unbound variables are able to be instantiated by a hypothesis,
so we must filter out those unbound mentioned in the hypothesis which
are arguments to a function (1) and those which are under a constructor
that contains a bound or invalid unbound variable (2) and those that
appear nonlinearly (as they would require an unlikely equality check)(3).
Here is an encompassing example:
`H (C a (f b)) c (C₃ c) d (C₃ (C₂ e) C₄)`
We can't instantiate `b` because it is under a function (1),
  `a` because it is under a constructor with an invalid variable `b` (2),
  `c` because it appears nonlinearly
We *can* instantiate `d` and `e` because they satisfy all three conditions
Note that despite e being stored under several constructors, there are no
bound or invalid variables mixed in, so we can generate H's 5th argument
and pattern match the result against `(C₃ (C₂ x) C₄)` and if it matches,
`e` to the value `x`.

The remainder of its unbound variables should be instantiated according
to their type unconstrained by a hypothesis. These unconstrained instantiations
should happen before the constrained instantiation. For each `2^|unbound ∩ valid|`
choice, we prepend the unconstrained instantiations behind the constrained one
and lazily cons that version of the schedule to our list.

Finally, we fold through the list, tracking the set of variables bound, as soon
as a constraint has had all its variables bound, a check for it
should be inserted at that point in the schedule. Finally, return
the schedules. -/

/-
  Depth-first enumeration of all possible schedules.

  The list of possible schedules boils down to taking a permutation of list of hypotheses -- what this function
  does is it comes up with the list of possible permutations of hypotheses.

  For `TyApp` in the STLC example, here are the possible permutations (output is e, the unbound vars are {e1, e2, t1}):

  (a.) `[typing Γ e1 (TFun 𝜏1 𝜏2), typing Γ e2 𝜏1]`
  (b.) `[typing Γ e2 𝜏1, typing Γ e1 (TFun 𝜏1 𝜏2)]`

  We first discuss permutation (a).

  For permutation (a), `t1` and `e1` are unbound, so we're generate the max no. of variables possible
    * `e1` is in an outputtable position (since its not under a constructor)
    * `t1` is *not* in an ouputtable position (since `t1` is under the `TFun` constructor, `type` is an input mode, and `t2` is also an input mode)
    * This means `t1` has to be generated first arbitrarily

  We have elaborated this step to:
  ```lean
    t1 ← type                      -- (this uses the `Arbitrary` instance for [type])
    e1 ← typing Γ ? (TFun t1 t2)    -- (this desugars to `arbitraryST (fun e1 => typing Γ e1 (TFun t1 t2))` )
  ```

  Now that we have generated `t1` and `e1`, the next hypothesis is `typing Γ e2 𝜏1`
  * `e2` is the only variable that's unbound
  * Thus, our only option is to do:
  ```lean
    e2 ← typing Γ ? t1
  ```

  + For permutation (b), the first thing we do is check what are the unbound (not generated & not fixed by inputs)
    variables that are constrained by the first hypothesis `typing Γ e2 𝜏1`
    * `e2` is unbound & can be output (since its in the output mode & not generated yet)
    * `t1` can also be output since its not been generated yet & not under a constructor
      * `Γ` is fixed already (bound) b/c its a top-level argument (input) to `aux_arb`
    * Here we have 3 possible choices:
      1. Arbitrary [t1], ArbitrarySuchThat [e2]
      2. Arbitrary [e2], ArbitrarySuchThat [t1]
      3. ArbitrarySuchThat [e2, t1]

    * For each choice, we can then elaborate the next `ScheduleStep` in our hypothesis permutation (i.e. `typing Γ e1 (TFun 𝜏1 𝜏2)`)
    + Rest of the logic for dealing with permutation (b) is similar to as the 1st permutation
-/

/- Variables in third elt of hyp should be disjoint from flatten of snd elt
   Assume that any hyp in hyps should have at least one thing it could generate
   Any hypothesis which lacks an index it can generate from should be checked
   in a prior step. The second element of hyps should contain only lists of unbound
   variables.

   The snd and third elements combined should equal the set vars(hyp.fst)
-/

private partial def enumSchedules {α v} [BEq v] (vars : List v) (hyps : List (α × List (List v) × List v)) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hyps with
  | [] => pure (prune_empties [.InstVars <| vars.removeAll env])
  | _ => do
    let ⟨ (hyp, potential_output_indices, always_bound_variables),hyps' ⟩ ← select hyps
    let (some_bound_output_indices, all_unbound_output_indices) := List.partition (List.any . (List.contains env)) potential_output_indices
    let (out,bound) ← subsetsAndComplements all_unbound_output_indices
    if out.length > 1 then .lnil else
    let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
    let env' := bound_vars ++ env
    let (prechecks,to_be_satisfied) := List.partition (needs_checking env') hyps'
    let out_vars := out.flatten
    let env'' := out_vars ++ env'
    let (postchecks,to_be_satisfied') := List.partition (needs_checking env'') to_be_satisfied
    LazyList.mapLazyList (fun l => prune_empties [.InstVars (List.eraseDups bound_vars)
                              , .Checks (Prod.fst <$> prechecks)
                              , .Produce out_vars hyp
                              , .Checks (Prod.fst <$> postchecks)
                              ]
                              ++ l) (enumSchedules vars to_be_satisfied' env'')

#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4] [("A",[[1,2,3],[4]],[]), ("B",[[4]],[])] []).take 15

-- Simple test with 2 hypotheses
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] []).take 3

-- Test with overlapping variables
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5] [("H1",[[1],[2],[3]],[]), ("H2",[[3],[4]],[]), ("H3",[[4],[5]],[])] []).take 5

-- Test with some variables already bound
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] [1])

-- Larger example to test scalability
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4] [("P",[[1],[2]],[]), ("Q",[[2],[3]],[]), ("R",[[3],[4]],[]), ("S",[[1],[4]],[])] []).take 10

-- Lots of variables (10 variables in one hypothesis)
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5,6,7,8,9,10] [("BigHyp",[[1],[2],[3],[4],[5],[6],[7],[8],[9],[10]],[])] []).take 5

-- Lots of hypotheses (10 hypotheses with few variables each)
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5,6,7,8,9,10] [("H1",[[1]],[]), ("H2",[[2]],[]), ("H3",[[3]],[]), ("H4",[[4]],[]), ("H5",[[5]],[]),
                       ("H6",[[6]],[]), ("H7",[[7]],[]), ("H8",[[8]],[]), ("H9",[[9]],[]), ("H10",[[10]],[])] []).take 3

-- Both: many hypotheses with many variables each
#guard_msgs(error, drop info) in
#eval (enumSchedules (List.range 14) [("A",[[1],[2],[3],[4],[5]],[]), ("B",[[3],[4],[5],[6],[7]],[]), ("C",[[5],[6],[7],[8],[9]],[]),
                       ("D",[[7],[8],[9],[10],[11],[3],[1],[2]],[]), ("E",[[9],[10],[11],[12],[13]],[])] []).take 100

#guard_msgs(error, drop info) in
#eval (@enumSchedules String Nat _ [] [] [])

-- Example for BetweenN constructor:
-- BetweenN : ∀ n m, n <= m -> Between n (.succ n) (.succ (.succ m))
-- Variables: n, m (inputs), output: Between n (.succ n) (.succ (.succ m))
-- Hypothesis: n <= m
-- The hypothesis "n <= m" has variables [n, m] which are both inputs (always bound)
#guard_msgs(error, drop info) in
#eval (enumSchedules [`n, `m] [(`n_le_m, [], [`n, `m])] [`n,`m]).take 5

/--
`enumSchedules'` is a variant of `enumSchedules` where instead of taking a list of hypotheses to permute,
it takes a list of simply connected components of hypotheses based on reachability in the graph
where an edge between hypotheses exists iff their variable sets overlap. It then permutes
only hypotheses within components but not between components. The different components are kept
in a canonical order always, thus dramatically reducing the size of the enumeration. This is okay
because hypotheses in different components cannot possibly depend on each other, so their ordering
does not make a difference.
-/
private partial def enumSchedules' {α v} [BEq v] (vars : List v) (matchableVars : List v) (hypComps : List (List (α × List (List v) × List v))) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hypComps with
  | [] => pure (prune_empties [.InstVars <| vars.removeAll env])
  | [] :: hypComps' => enumSchedules' vars matchableVars hypComps' env
  | hyps :: hypComps' => do
    let ⟨ (hyp, potential_output_indices, always_bound_variables),hyps' ⟩ ← select hyps
    let (some_bound_output_indices, all_unbound_output_indices) := potential_output_indices.partition /- Partition the output arguments based on -/
      (fun l => /- Whether each output index's list of contained variables, `l`-/
        l.any (fun v => env.contains v && !matchableVars.contains v) /- contains a variable that is fixed already in the environment and is not matchable on (e.g. not a type variable) -/
        || l.all (matchableVars.contains)) /- or if all the variables are matchable on (it is constant), or empty. -/
    let (out,bound) ← subsetsAndComplements all_unbound_output_indices
    if out.length > 1 || (out.isEmpty && !bound.isEmpty) then .lnil else
    let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
    let env' := bound_vars ++ env
    let (prechecks,to_be_satisfied) := List.partition (needs_checking env') hyps'
    let out_vars := out.flatten
    let env'' := out_vars ++ env'
    let (postchecks,to_be_satisfied') := List.partition (needs_checking env'') to_be_satisfied
    LazyList.mapLazyList (fun l => prune_empties [.InstVars (List.eraseDups bound_vars)
                              , .Checks (Prod.fst <$> prechecks)
                              , .Produce out_vars hyp
                              , .Checks (Prod.fst <$> postchecks)
                              ]
                              ++ l) (enumSchedules' vars matchableVars (to_be_satisfied' :: hypComps') env'')

#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3,4] [] [[("A",[[1,2,3],[4]],[])], [("B",[[4]],[])]] []).take 15

-- Two separate SCCs: {H1,H2} share 'a', {H3,H4} share 'd'
#guard_msgs(error, drop info) in
#eval (enumSchedules' ["a","b","c","d","e"] [] [[("H1",[["a"],["b"],["c"]],[]), ("H2",[["a"]],[])], [("H3",[["d"]],[]), ("H4",[["d"],["e"]],[])]] []).take 100

-- Three SCCs: connected chain, isolated, pair
#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3,4,5,6] [] [[("A",[[1],[2]],[]), ("B",[[2],[3]],[]), ("C",[[3]],[])], [("D",[[4]],[])], [("E",[[5]],[]), ("F",[[5],[6]],[])]] []).take 100

-- Multiple single-node SCCs
#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3] [] [[("X",[[1]],[])], [("Y",[[2]],[])], [("Z",[[3]],[])]] []).take 2

-- Comparison: enumSchedules vs enumSchedules' - total schedule counts
-- Example 1: Two separate SCCs should reduce schedules significantly
#guard_msgs(error, drop info) in
#eval (enumSchedules ["a","b","c","d"] [("H1",[["a"],["b"]],[]), ("H2",[["a"]],[]), ("H3",[["c"],["d"]],[]), ("H4",[["c"]],[])] []).length

#guard_msgs(error, drop info) in
#eval (enumSchedules' ["a","b","c","d"] [] [[("H1",[["a"],["b"]],[]), ("H2",[["a"]],[])], [("H3",[["c"],["d"]],[]), ("H4",[["c"]],[])]] []).length

-- Example 2: Single SCC should have same count
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] []).length

#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3] [] [[("A",[[1],[2]],[]), ("B",[[2],[3]],[])]] []).length


-- Compare binary choice approach vs full permutations
-- Generates all possible permutations of a list (factorial growth)
private partial def enumAllPermutations {α} [BEq α] (hyps : List α) : LazyList (List α) :=
  match hyps with
  | [] => pure []
  | _ => do
    let ⟨h, rest⟩ ← select hyps
    let restPerms ← enumAllPermutations rest
    pure (h :: restPerms)

-- Build dependency graph: for each hypothesis, find all other hypotheses that share variables
private def getNeighbors {α v} [BEq α] [BEq v] (hyps : List (α × List v)) : List (α × List α) :=
  hyps.map (fun (hyp, vars) =>
    let neighbors := hyps.filter (fun (otherHyp, otherVars) =>
      hyp != otherHyp && vars.any (otherVars.contains ·))
    (hyp, neighbors.map Prod.fst))

/--
`enumSchedules'` is a variant of `enumSchedules` where instead of taking a list of hypotheses to permute,
it takes a list of simply connected components of hypotheses based on reachability in the graph
where an edge between hypotheses exists iff their variable sets overlap. It then permutes
only hypotheses within components but not between components. The different components are kept
in a canonical order always, thus dramatically reducing the size of the enumeration. This is okay
because hypotheses in different components cannot possibly depend on each other, so their ordering
does not make a difference.
-/
private def enumSchedulesChunked {α v} [BEq v] [Hashable v] (vars : List v) (matchableVars : List v) (hypComps : List (LazyList (List (α × List (List v) × List v)))) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  -- Use HashSet for O(1) lookups instead of O(n) List.contains
  let envSet := Std.HashSet.ofList env
  let matchableSet := Std.HashSet.ofList matchableVars

  match hypComps with
  | [] => pure (prune_empties [.InstVars <| vars.filter (!envSet.contains ·)])
  | componentPerms :: hypComps' => do
    let mut perm ← componentPerms
    let mut sched := []
    let mut envSet := envSet
    let mut env := env

    repeat
      match perm with
      | [] => break
      | (hyp, potential_output_indices, always_bound_variables) :: rest =>
      perm := rest

      let (some_bound_output_indices, all_unbound_output_indices) := potential_output_indices.partition
        (fun l =>
          l.any (fun v => envSet.contains v && !matchableSet.contains v)
          || l.all matchableSet.contains)

      let (out,bound) ← subsetsAndComplements all_unbound_output_indices
      if out.length > 1 || (out.isEmpty && !bound.isEmpty) then .lnil else

      let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (!envSet.contains ·)

      -- Update both list and set for efficiency
      for v in bound_vars do
        envSet := envSet.insert v
      env := bound_vars ++ env

      let (prechecks,to_be_satisfied) := List.partition (needs_checking env) perm
      let out_vars := out.flatten

      for v in out_vars do
        envSet := envSet.insert v
      env := out_vars ++ env

      let (postchecks,to_be_satisfied') := List.partition (needs_checking env) to_be_satisfied
      sched := sched ++ prune_empties [.InstVars (List.eraseDups bound_vars)
                                , .Checks (Prod.fst <$> prechecks)
                                , .Produce out_vars hyp
                                , .Checks (Prod.fst <$> postchecks)
                                ];
      perm := to_be_satisfied'

    LazyList.mapLazyList (sched ++ ·) <| enumSchedulesChunked vars matchableVars hypComps' env

private def filterWorse [LE σ] [DecidableRel (fun (a b : σ) => a <= b)] (l : LazyList α) (rank : α → σ) : LazyList (α × Nat) :=
  let seen := 1
  let rec go score l seen : LazyList (α × Nat) :=
    match l with
    | .lnil => .lnil
    | .lcons a rest =>
      let score' := rank a
      if score' >= score then
        go score rest.get (seen + 1)
      else
        .lcons (a, seen) <| go score' rest.get (seen + 1)
  match l with
  | .lnil => .lnil
  | .lcons a rest => .lcons (a, seen) <| go (rank a) rest.get (seen + 1)

structure PreScheduleScore where
  checks : Nat
  length : Nat
  unconstrained : Nat
  deriving Ord, Repr, BEq

def preScheduleStepsScore (schedule : List (PreScheduleStep α β)) : PreScheduleScore :=
  let steps := schedule
  Id.run do
    let mut checks := 0
    let mut length := 0
    let mut unconstrained := 0
    for step in steps do
      length := length + 1
      match step with
      | .Checks cs => checks := checks + cs.length
      | .InstVars vs => unconstrained := unconstrained + vs.length
      | _ => ()
    ⟨checks, length, unconstrained⟩

instance : LE PreScheduleScore := leOfOrd
instance : LT PreScheduleScore := ltOfOrd

def preScheduleLT (a b : List (PreScheduleStep α β)) := preScheduleStepsScore a ≤ preScheduleStepsScore b

def sequentialFlatMap {α β s : Type} (l : LazyList α) (initialState : s) (f : α → s → LazyList (β × s)) : LazyList (β × s) :=
  let rec go (remaining : LazyList α) (currentState : s) : LazyList (β × s) :=
    match remaining with
    | LazyList.lnil => LazyList.lnil
    | LazyList.lcons a rest =>
      let results := f a currentState
      match results with
      | LazyList.lnil => go rest.get currentState
      | LazyList.lcons (b, newState) subRest =>
        LazyList.lcons (b, newState) ⟨fun _ =>
          let rec drainResults (remaining : LazyList (β × s)) (state : s) : LazyList (β × s) :=
            match remaining with
            | LazyList.lnil => go rest.get state
            | LazyList.lcons (b', state') rest' =>
              LazyList.lcons (b', state') ⟨fun _ => drainResults rest'.get state'⟩
          drainResults subRest.get newState⟩
  go l initialState

-- Initialize worst possible score for branch and bound
def initWorstScore (numHyps : Nat) : PreScheduleScore :=
  ⟨numHyps + 1, 0, 0⟩

-- Estimate lower bound for remaining schedule (conservative estimate)
def estimateLowerBound (partialScore : PreScheduleScore) (remainingHyps : Nat) : PreScheduleScore :=
  ⟨partialScore.checks, partialScore.length + remainingHyps, partialScore.unconstrained⟩

-- Generate all permutations of a list
def List.permutations {α : Type u} : List α → List (List α)
  | [] => [[]]
  | x :: xs => ((List.permutations xs).flatMap fun perm =>
    (List.range (perm.length + 1)).map fun i => perm.take i ++ [x] ++ perm.drop i)

/-- Evaluates one scheduling choice for a hypothesis: `out` are the output variable groups
    produced by satisfying the hypothesis, `bound` are variables bound arbitrarily beforehand.
    Extends the environment with bound vars, partitions remaining hypotheses into pre/post-checks
    around the produce step. Returns `none` if invalid (multiple outputs in single-output mode,
    or no outputs with non-empty bound). -/
private def processChoice {α v} [BEq v] [Hashable v] (multiOutput : Bool) (hyp : α)
        (out bound : List (List v)) (some_bound_output_indices : List (List v))
        (always_bound_variables : List v) (rest : List (α × List (List v) × List v))
        (currentEnv : List v) (currentEnvSet : Std.HashSet v)
        : Option (List (PreScheduleStep α v) × List (α × List (List v) × List v) × List v × Std.HashSet v) :=
  if (!multiOutput && out.length > 1) || (out.isEmpty && !bound.isEmpty) then none else
  let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (!currentEnvSet.contains ·)
  let newEnvSet := bound_vars.foldl (fun s v => s.insert v) currentEnvSet
  let newEnv := bound_vars ++ currentEnv
  let (prechecks, to_be_satisfied) := List.partition (needs_checking newEnv) rest
  let out_vars := out.flatten
  let finalEnvSet := out_vars.foldl (fun s v => s.insert v) newEnvSet
  let finalEnv := out_vars ++ newEnv
  let (postchecks, to_be_satisfied') := List.partition (needs_checking finalEnv) to_be_satisfied
  let newSched := prune_empties [.InstVars (List.eraseDups bound_vars)
                                , .Checks (Prod.fst <$> prechecks)
                                , .Produce out_vars hyp
                                , .Checks (Prod.fst <$> postchecks)]
  some (newSched, to_be_satisfied', finalEnv, finalEnvSet)

private def findMins [Ord β] (l : List α) (score : α → β) : List α :=
  let rec aux (l : List α) (best : List α) (minScore : β) :=
    match l with
    | [] => best
    | a :: as =>
      let ascore := score a
      match compare ascore minScore with
      | .lt => aux as [a] ascore
      | .eq => aux as (a :: best) minScore
      | .gt => aux as best minScore
  match l with
  | [] => []
  | a :: as => aux as [a] (score a)

/-- Lazily enumerates generator schedules using branch-and-bound pruning.
    Explores permutations of hypothesis orderings chunked by connected components,
    pruning branches whose lower-bound score exceeds the best found so far.
    Returns a lazy list of valid schedules sorted by quality (best first). -/
private partial def enumSchedulesChunkedWithPruning {α v} [Ord v] [BEq v] [Repr α] [Repr v] [Hashable v] (vars : List v) (matchableVars : List v) (hypComps : List (LazyList (List (α × List (List v) × List v)))) (env : List v) (numHyps : Nat) (multiOutput : Bool := false)
  : LazyList (List (PreScheduleStep α v)) :=
  let matchableSet := Std.HashSet.ofList matchableVars

  /-
  go takes:
  hypComps, a list where each element is an enumeration of all permutations of a strongly connected component of hypotheses that are distinct according variable dependencies
  env, an environment of variables that have been bound already in the schedule prefix under consideration
  sched, the schedule prefix already constructed that we are enumerating how to extend to a full schedule
  numHypsRemaining, a count of the remaining hypotheses to be checked/produced with across all components
  bestScore, the best (smallest) scoring complete schedule seen so far. If the current schedule's score lower bound exceeds this, this enumeraiton is pruned.
    When a new schedule is found with an improved score, its score replaces bestScore.
  go returns an enumeration of schedules constructed alongside their score that beat all prior schedules considered, so the enumeration is monotonically decreasing in score.
  -/
  let rec go [BEq v] (hypComps : List (LazyList (List (α × List (List v) × List v)))) (env : List v) (sched : List (PreScheduleStep α v)) (numHypsRemaining : Nat) (bestScore : PreScheduleScore)
    : LazyList (List (PreScheduleStep α v) × PreScheduleScore) :=
    match hypComps with
    | [] => do /- If there are no more strongly connected components of hypotheses to satisfy, we can finish our schedule by instantiating the remaining uninstantiated variables in an unconstrained manner
      and then return the schedule. -/
      let finalSched := sched ++ prune_empties [.InstVars <| vars.filter (!(Std.HashSet.ofList env).contains ·)]
      let finalScore := preScheduleStepsScore finalSched
      if finalScore < bestScore then /- Only include this schedule in the enumeration if it improves on the bestScore to get monotonicity property, also update the new best score. -/
        pure (finalSched, finalScore)
      else
        .lnil /- If it isn't better than the best so far, prune it. -/
    | componentPerms :: hypComps' => /- Consider the next component of hypotheses. -/
      let componentBest := initWorstScore (componentPerms.head?.getD [] |>.length)
      let envMemo : Std.HashMap (List v) PreScheduleScore := {}
      let rec processPerm [BEq v] (currentPerm : List _) (currentSched : List (PreScheduleStep α v)) (currentEnv : List v) (currentEnvSet : Std.HashSet v)
                          (st : PreScheduleScore × Std.HashMap (List v) PreScheduleScore)
        : LazyList ((List (PreScheduleStep α v) × List v) × (PreScheduleScore × Std.HashMap (List v) PreScheduleScore)) :=
        let (runningComponentBest, envMemo) := st
        let currentScore := preScheduleStepsScore currentSched
        let remainingHyps := currentPerm.length
        let lowerBound := estimateLowerBound currentScore remainingHyps
        let envKey := ((List.eraseDups currentEnv) |>.mergeSort (fun a b => compare a b |>.isLE))
        let dominatingScore := envMemo[envKey]?.getD componentBest
        let _ := schedTrace "processPerm: remainingHyps={remainingHyps}, currentScore={repr currentScore}, lowerBound={repr lowerBound}, runningBest={repr runningComponentBest}, dominatingScore={repr dominatingScore}"
        if lowerBound > runningComponentBest then
          let _ := schedTrace "PRUNED: lowerBound > runningComponentBest ({repr lowerBound} >= {repr runningComponentBest}) \n"
          .lnil
        else if dominatingScore < currentScore then
          let _ := schedTrace "PRUNED: dominatingScore < currentScore ({repr dominatingScore} < {repr currentScore}) \n"
          .lnil
        else
        match currentPerm with
        | [] =>
          let _ := schedTrace "BASE CASE: returning final schedule with score {repr currentScore}"
          pure ((sched ++ currentSched, currentEnv), (currentScore, envMemo))
        | (hyp, potential_output_indices, always_bound_variables) :: rest =>
          let _ := schedTrace "PROCESSING hyp: {repr hyp}, potential_outputs: {repr potential_output_indices.length}, always_bound: {repr always_bound_variables.length}"
          let envMemo := if currentScore < dominatingScore then envMemo.insert envKey currentScore else envMemo
          let (some_bound_output_indices, all_unbound_output_indices) := potential_output_indices.partition
            (fun l =>
              l.any (fun v => currentEnvSet.contains v && !matchableSet.contains v)
              || l.all matchableSet.contains)
          let choices := if multiOutput then
              [(all_unbound_output_indices, [])]
            else
              ([],all_unbound_output_indices) :: (select all_unbound_output_indices |>.toList.map (fun (a,b) => ([a],b)))
          let validChoices := choices.filterMap (fun (out,bound) => processChoice multiOutput hyp out bound some_bound_output_indices always_bound_variables rest currentEnv currentEnvSet)
          let _ := schedTrace "CHOICES: total={choices.length}, valid={validChoices.length}"
          let sortedChoices := validChoices.mergeSort (fun (a,_,_,_) (b,_,_,_) => preScheduleStepsScore a ≤ preScheduleStepsScore b)

          sequentialFlatMap (LazyList.fromList sortedChoices) (runningComponentBest,envMemo) fun (newSteps, to_be_satisfied', finalEnv, finalEnvSet) (runningComponentBest, envMemo) =>
            processPerm to_be_satisfied' (currentSched ++ newSteps) finalEnv finalEnvSet (runningComponentBest, envMemo)

      let componentResults := sequentialFlatMap componentPerms (componentBest, envMemo) (fun perm (runningComponentBest, envMemo) =>
        processPerm perm [] env (Std.HashSet.ofList env) (runningComponentBest, envMemo)) |>.mapLazyList (fun (a,_) => a)

      sequentialFlatMap componentResults bestScore (fun (newSched, newEnv) globalBest =>
        let score := preScheduleStepsScore newSched
        let remainingHyps := numHypsRemaining - (componentPerms.head?.getD []).length
        let lowerBound := estimateLowerBound score remainingHyps
        if lowerBound > globalBest then .lnil else
        go hypComps' newEnv newSched (numHypsRemaining - (componentPerms.head?.getD []).length) globalBest)

  let initialScore := initWorstScore numHyps
  go hypComps env [] numHyps initialScore |>.mapLazyList (fun (schd, _score) => schd)

#guard_msgs(drop info) in
#eval do
  -- Test 1: Deep dependency chain - all connected by shared variables, forms one SCC
  let deepChainScc := [("H1", [["a"]], []), ("H2", [["a"], ["b"]], []), ("H3", [["b"], ["c"]], []),
                       ("H4", [["c"], ["d"]], []), ("H5", [["d"], ["e"]], []), ("H6", [["e"], ["f"]], [])]
  let deepChainComps := [LazyList.fromList (List.permutations deepChainScc)]
  let deepVars := ["a", "b", "c", "d", "e", "f"]

  let deepOriginal := enumSchedulesChunked deepVars [] deepChainComps [] |>.toList.length
  let deepPruned := enumSchedulesChunkedWithPruning deepVars [] deepChainComps [] 6 |>.toList.length

  -- Test 2: True multi-SCC example with disconnected variable groups
  -- SCC1: variables {p, q} - H1 and H2 share variable p
  let scc1 := [("H1", [["p"]], []), ("H2", [["p"], ["q"]], [])]
  -- SCC2: variables {r, s} - H3 and H4 share variable r
  let scc2 := [("H3", [["r"]], []), ("H4", [["r"], ["s"]], [])]
  -- SCC3: variables {t, u} - H5 and H6 share variable t
  let scc3 := [("H5", [["t"]], []), ("H6", [["t"], ["u"]], [])]
  let branchComps := [LazyList.fromList (List.permutations scc1), LazyList.fromList (List.permutations scc2), LazyList.fromList (List.permutations scc3)]
  let branchVars := ["p", "q", "r", "s", "t", "u"]

  let branchOriginal := enumSchedulesChunked branchVars [] branchComps [] |>.toList.length
  let branchPruned := enumSchedulesChunkedWithPruning branchVars [] branchComps [] 6 |>.toList.length

  -- Test 3: Complex with matchable variables split into SCCs
  let complexScc1 := [("H1", [["a"], ["b"]], ["m1"])]
  let complexScc2 := [("H2", [["b", "m1"], ["c"]], ["m2"])]
  let complexScc3 := [("H3", [["c"], ["d", "m2"]], []), ("H4", [["d"], ["e"]], ["m3"])]
  let complexScc4 := [("H5", [["e", "m3"]], []), ("H6", [["a", "e"]], [])]
  let complexComps := [LazyList.fromList (List.permutations complexScc1), LazyList.fromList (List.permutations complexScc2),
                       LazyList.fromList (List.permutations complexScc3), LazyList.fromList (List.permutations complexScc4)]
  let complexVars := ["a", "b", "c", "d", "e", "m1", "m2", "m3"]
  let complexMatchable := ["m1", "m2", "m3"]

  let complexOriginal := enumSchedulesChunked complexVars complexMatchable complexComps [] |>.toList.length
  let complexPruned := enumSchedulesChunkedWithPruning complexVars complexMatchable complexComps [] 6 |>.toList.length

  -- Test 4: Worst case scenario split into SCCs
  let worstScc1 := [("H1", [["a"]], []), ("H2", [["b"]], [])]
  let worstScc2 := [("H3", [["a", "b"], ["c"]], [])]
  let worstScc3 := [("H4", [["a", "c"], ["d"]], []), ("H5", [["b", "c"], ["e"]], [])]
  let worstScc4 := [("H6", [["d", "e"], ["f"]], [])]
  let worstScc5 := [("H7", [["a", "f"]], []), ("H8", [["b", "f"]], []), ("H9", [["c", "f"]], [])]
  let worstComps := [LazyList.fromList (List.permutations worstScc1), LazyList.fromList (List.permutations worstScc2), LazyList.fromList (List.permutations worstScc3),
                     LazyList.fromList (List.permutations worstScc4), LazyList.fromList (List.permutations worstScc5)]
  let worstVars := ["a", "b", "c", "d", "e", "f"]

  let worstOriginal := enumSchedulesChunked worstVars [] worstComps [] |>.toList.length
  let worstPruned := enumSchedulesChunkedWithPruning worstVars [] worstComps [] 9 |>.toList.length

  IO.println "=== Branch and Bound Optimization Results ==="
  IO.println s!"Deep Chain - Original: {deepOriginal}, Pruned: {deepPruned}, Reduction: {((deepOriginal - deepPruned) * 100) / deepOriginal}%"
  IO.println s!"Multi Branch - Original: {branchOriginal}, Pruned: {branchPruned}, Reduction: {((branchOriginal - branchPruned) * 100) / branchOriginal}%"
  IO.println s!"Complex Constraints - Original: {complexOriginal}, Pruned: {complexPruned}, Reduction: {((complexOriginal - complexPruned) * 100) / complexOriginal}%"
  IO.println s!"Worst Case - Original: {worstOriginal}, Pruned: {worstPruned}, Reduction: {((worstOriginal - worstPruned) * 100) / worstOriginal}%"

  let totalReduction := ((deepOriginal + branchOriginal + complexOriginal + worstOriginal) -
                        (deepPruned + branchPruned + complexPruned + worstPruned)) * 100 /
                       (deepOriginal + branchOriginal + complexOriginal + worstOriginal)
  IO.println s!"Total Reduction: {totalReduction}%"
  pure ()

-- Property test: preScheduleStepsScore components (checks, length, unconstrained) are
-- all monotonically non-decreasing as hypotheses are iteratively processed.
-- Uses random generation of hypothesis sets and tests all permutations for small sets,
-- random permutations for larger ones.

private structure SimpleRng where
  state : UInt64

private def SimpleRng.next (rng : SimpleRng) : SimpleRng × UInt64 :=
  -- xorshift64
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

private def SimpleRng.natBelow (rng : SimpleRng) (n : Nat) : SimpleRng × Nat :=
  if n == 0 then (rng, 0)
  else let (rng', v) := rng.next; (rng', v.toNat % n)

private def shuffle (rng : SimpleRng) (l : List α) : SimpleRng × List α := Id.run do
  let mut rng := rng
  let mut arr := l.toArray
  let mut i := arr.size
  while i > 1 do
    i := i - 1
    let (rng', j) := rng.natBelow (i + 1)
    rng := rng'
    match arr[i]?, arr[j]? with
    | some vi, some vj =>
      arr := arr.set! i vj |>.set! j vi
    | _, _ => pure ()
  return (rng, arr.toList)

-- Simulate processChoice: process one hypothesis given env and remaining hyps
private def simProcessHyp (hyp : String) (outputGroups : List (List String))
    (alwaysBound : List String)
    (rest : List (String × List (List String) × List String))
    (envSet : Std.HashSet String)
    : (List (PreScheduleStep String String) × Std.HashSet String × List (String × List (List String) × List String)) :=
  let (someBound, allUnbound) := outputGroups.partition (fun l => l.any envSet.contains)
  let boundVars := (if allUnbound.isEmpty then [] else allUnbound.drop 1 |>.flatten) ++
                   (alwaysBound ++ someBound.flatten).filter (!envSet.contains ·)
  let envAfterBind := boundVars.foldl (fun s v => s.insert v) envSet
  let (prechecks, rest1) := rest.partition fun (_, potIdx, ab) =>
    ab.all envAfterBind.contains && potIdx.all (fun idx => idx.all envAfterBind.contains)
  let outVars := if allUnbound.isEmpty then [] else allUnbound.head!
  let envAfterProduce := outVars.foldl (fun s v => s.insert v) envAfterBind
  let (postchecks, rest2) := rest1.partition fun (_, potIdx, ab) =>
    ab.all envAfterProduce.contains && potIdx.all (fun idx => idx.all envAfterProduce.contains)
  let steps := prune_empties [
    .InstVars boundVars,
    .Checks (prechecks.map (·.1)),
    .Produce outVars hyp,
    .Checks (postchecks.map (·.1))
  ]
  (steps, envAfterProduce, rest2)

-- Run one permutation and check monotonicity
private def checkOrdering (perm : List (String × List (List String) × List String))
    : Option (PreScheduleScore × PreScheduleScore) := Id.run do
  let mut env : Std.HashSet String := {}
  let mut remaining := perm
  let mut prevScore : PreScheduleScore := ⟨0, 0, 0⟩
  let mut cumSched : List (PreScheduleStep String String) := []
  while !remaining.isEmpty do
    match remaining with
    | [] => return none
    | (hyp, outputs, bound) :: rest =>
      let (newSteps, newEnv, newRest) := simProcessHyp hyp outputs bound rest env
      cumSched := cumSched ++ newSteps
      let newScore := preScheduleStepsScore cumSched
      if newScore.checks < prevScore.checks ||
         newScore.length < prevScore.length ||
         newScore.unconstrained < prevScore.unconstrained then
        return some (prevScore, newScore)
      prevScore := newScore
      env := newEnv
      remaining := newRest
  return none

-- Generate a random hypothesis set
private def genHypSet (rng : SimpleRng) : SimpleRng × List (String × List (List String) × List String) := Id.run do
  let (rng, numHyps) := rng.natBelow 5  -- 2..6 hypotheses
  let numHyps := numHyps + 2
  let (rng, numVars) := rng.natBelow 4  -- 3..6 variables
  let numVars := numVars + 3
  let vars := (List.range numVars).map fun i => s!"v{i}"
  let mut rng := rng
  let mut hyps : List (String × List (List String) × List String) := []
  let mut hi := 0
  while hi < numHyps do
    let hypName := s!"H{hi}"
    let (rng', numGroups) := rng.natBelow 3
    rng := rng'
    let numGroups := numGroups + 1
    let mut groups : List (List String) := []
    let mut gi := 0
    while gi < numGroups do
      let (rng', groupSize) := rng.natBelow 2
      rng := rng'
      let groupSize := groupSize + 1
      let mut group : List String := []
      let mut vi := 0
      while vi < groupSize do
        let (rng', idx) := rng.natBelow numVars
        rng := rng'
        group := group ++ [vars[idx]!]
        vi := vi + 1
      groups := groups ++ [group.eraseDups]
      gi := gi + 1
    let mut alwaysBound : List String := []
    let (rng', hasAB) := rng.natBelow 5
    rng := rng'
    if hasAB == 0 then
      let (rng', abi) := rng.natBelow numVars
      rng := rng'
      alwaysBound := [vars[abi]!]
    hyps := hyps ++ [(hypName, groups, alwaysBound)]
    hi := hi + 1
  return (rng, hyps)

private def testScoreMonotonicity : IO String := do
  let numTrials := 10000
  let mut rng : SimpleRng := { state := 12345 }
  let mut violations := 0
  let mut tests := 0
  let mut firstViolation : Option String := none
  let mut trial := 0
  while trial < numTrials do
    let (rng', hyps) := genHypSet rng
    rng := rng'
    if hyps.length ≤ 4 then
      let perms := hyps.permutations
      for perm in perms do
        tests := tests + 1
        match checkOrdering perm with
        | some (prev, cur) =>
          violations := violations + 1
          if firstViolation.isNone then
            firstViolation := some s!"prev={repr prev} cur={repr cur} hyps={hyps.length}"
        | none => pure ()
    else
      let mut si := 0
      while si < 10 do
        let (rng', perm) := shuffle rng hyps
        rng := rng'
        tests := tests + 1
        match checkOrdering perm with
        | some (prev, cur) =>
          violations := violations + 1
          if firstViolation.isNone then
            firstViolation := some s!"prev={repr prev} cur={repr cur} hyps={hyps.length}"
        | none => pure ()
        si := si + 1
    trial := trial + 1
  if violations > 0 then
    return s!"FAILED: {violations}/{tests} orderings had non-monotonic score. First: {firstViolation.getD ""}"
  else
    return s!"PASSED: {tests} orderings across {numTrials} random hypothesis sets — score monotonically non-decreasing"

#eval do IO.println (← testScoreMonotonicity)

-- Determine the right name for the recursive function in the producer
-- The default name for the recursive function, used when no freshened name is provided.
def defaultRecFnName (deriveSort : DeriveSort) : Name :=
  match deriveSort with
  | DeriveSort.Generator => `aux_arb
  | .Enumerator => `aux_enum
  | .Checker | .Theorem => `aux_dec

private def preScheduleStepToScheduleStep (ctorName : Name) (preStep : PreScheduleStep HypothesisExpr TypedVar) : ScheduleM (List ScheduleStep) := do
  let env ← read
  match preStep with
  | .Checks hyps => return (hyps.map (fun hyp =>
    -- Unwrap nested negation: peel `Not` layers, flipping polarity each time
    let (innerHyp, polarity) := Id.run do
      let mut h := hyp
      let mut pol := true
      for _ in List.range 10 do  -- bounded iteration
        if h.fst == ``Not then
          match h.snd with
          | [.Ctor name args] => h := (name, args); pol := !pol
          | [.TyCtor name args] => h := (name, args); pol := !pol
          | [.FuncApp name args] => h := (name, args); pol := !pol
          | _ => break
        else break
      return (h, pol)
    let src := if env.deriveSort == DeriveSort.Checker && env.recCall.fst == innerHyp.fst then
      Source.Rec env.recFnName innerHyp.snd
    else
      Source.NonRec innerHyp;
    ScheduleStep.Check src polarity))
  | .Produce outs hyp =>
    let (newMatches, hyp', newOutputs) ← handleConstrainedOutputs hyp outs
    let typedOutputs ← newOutputs.mapM
      (fun v =>
        match v with
        | .TVar v => do
          let typ ← exprToConstructorExpr v.type
          pure (v.var, some typ)
        | .UVar n =>
          pure (n, none)
          )
    let typedVars := env.vars.filterMap fun ⟨v, t⟩ => if t.isSort then some v else none
    let (_, hypArgs) := hyp'
    let constrainingRelation ←
      if ← isRecCall (outs.map (fun x => x.var)) typedVars hyp env.recCall then
        let inputArgs := filterWithIndex (fun i _ => i ∉ (Prod.snd env.recCall)) hypArgs
        pure (Source.Rec env.recFnName inputArgs)
      else
        pure (Source.NonRec hyp')
    return (ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort :: newMatches)
  | .InstVars vars =>
    vars.mapM (fun ⟨v,ty⟩ => do
    let (cName, cArgs) := ty.getAppFnArgs
    let src ←
      if cName == Prod.fst env.recCall
        then Source.Rec env.recFnName <$> cArgs.toList.mapM (fun e => exprToConstructorExpr e)
      else
        let hypothesisExpr ← exprToHypothesisExpr ctorName ty
        pure (Source.NonRec hypothesisExpr)
    return ScheduleStep.Unconstrained v src env.prodSort
    )

/-- Takes a `deriveSort` and returns the corresponding `ProducerSort`:
    - If we're deriving a `Checker` or a `Enumerator`, the corresponding `ProducerSort` is an `Enumerator`,
      since its more efficient to enumerate values when checking
    - If we're deriving a `Generator` or a function which generates inputs to a `Theorem`,
      the corresponding `ProducerSort` is a `Generator`, since we want to generate random inputs -/
def convertDeriveSortToProducerSort (deriveSort : DeriveSort) : ProducerSort :=
  match deriveSort with
  | .Checker | .Enumerator => ProducerSort.Enumerator
  | .Generator | .Theorem => ProducerSort.Generator

private def typePreScheduleStep {α} (tyMap : NameMap Expr) (step : PreScheduleStep α Name) : (PreScheduleStep α TypedVar) :=
  match step with
  | .Checks hyps => .Checks hyps
  | .Produce out hyp =>
    let typedOut := out.map (fun name =>
      let ty := tyMap.get! name
      ⟨name, ty⟩)
    .Produce typedOut hyp
  | .InstVars vars =>
    let typedVars := vars.map (fun name =>
      let ty := tyMap.get! name
      ⟨name, ty⟩)
    .InstVars typedVars

instance [ToString α] [ToString v] : ToString (List (List (PreScheduleStep α v))) where
  toString schedules :=
    schedules.map (fun steps =>
      let lines := steps.map fun step =>
        match step with
        | .InstVars vars => s!"{vars} ← arbitrary"
        | .Produce out hyp => s!"{out} ← {hyp}"
        | .Checks hyps => s!"check {hyps}"
      "do\n  " ++ String.intercalate "\n  " lines
    ) |> String.intercalate "\n\n"


/-- Converts a HypothesisExpr to a list of VarExpr, checking each argument for function applications -/
private def hypothesisToVarExpr (hyp : HypothesisExpr) : List (SearchTree.VarExpr Name) :=
  let (_, args) := hyp
  args.map fun arg =>
    let vars := variablesInConstructorExpr arg
    if containsFunctionCall arg || tyCtorConstrainsVariable arg then
      SearchTree.VarExpr.Func vars
    else if vars.length > 1 then
      SearchTree.VarExpr.Ctor vars
    else
      match vars with
      | [v] => SearchTree.VarExpr.Var v
      | _ => SearchTree.VarExpr.Ctor vars

private def possiblePreSchedulesWithAdvancedPruning (vars : List TypedVar) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) (recFnName : Name := defaultRecFnName deriveSort) (multiOutput : Bool := false) : LazyList ((List (PreScheduleStep HypothesisExpr TypedVar))) × ScheduleEnv :=
  let typeVars := vars.filterMap fun ⟨v,t⟩ => if t.isSort then some v else none
  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses
  let varNames := vars.map (fun x => x.var)
  let prodSort := convertDeriveSortToProducerSort deriveSort
  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, prodSort, recCall, fixedVars, recFnName, multiOutput, [], none ⟩
  let remainingVars := List.filter (fun v => not <| fixedVars.contains v) varNames
  let (newCheckedIdxs, newCheckedHyps) := List.unzip <| (collectCheckedHypotheses scheduleEnv fixedVars [])
  let remainingSortedHypotheses := filterWithIndex (fun i _ => i ∉ newCheckedIdxs) sortedHypotheses
  let rawHypotheses := remainingSortedHypotheses.map (fun (h,vars) => ((h,vars), List.flatten vars))
  let sccGroups := computeSCC rawHypotheses
  let connectedHypotheses := sccGroups
                             |>.map (fun scc =>
                                let hypVarMap := scc
                                SearchTree.enumDependencySatisfyingOrderingsWithAdvancedPruning hypVarMap (fun (h,_) => hypothesisToVarExpr h)
                                  |>.mapLazyList (List.map <| constructHypothesis typeVars))
  let firstChecks := PreScheduleStep.Checks newCheckedHyps.reverse
  let lazyPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr Name)) := enumSchedulesChunkedWithPruning remainingVars typeVars connectedHypotheses fixedVars sortedHypotheses.length multiOutput
  let nameTypeMap := List.foldl (fun m ⟨name,ty⟩ => NameMap.insert m name ty) ∅ vars
  let typedPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr TypedVar)) := lazyPreSchedules.mapLazyList ((firstChecks :: ·) ∘ List.map (typePreScheduleStep nameTypeMap))
  (typedPreSchedules, scheduleEnv)

/-- Computes all possible schedules for a constructor
    (each candidate schedule is represented as a `List ScheduleStep`).

    Arguments:
    - `ctorName`: The name of the constructor we are deriving a schedule for
    - `vars`: A list of universally-quantified variables and their types
    - `hypotheses`: A list of hypotheses about the variables in `vars`
    - `deriveSort` The sort (checker/enumerator/generator) of deriver we are generating
    - `recCall`: A pair contianing the name of the inductive relation and a list of indices for output arguments
    - `fixedVars`: A list of fixed variables (i.e. inputs to the inductive relation) -/
def possibleSchedules (ctorName : Name) (vars : List TypedVar) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) (recFnName : Name := defaultRecFnName deriveSort) (multiOutput : Bool := false) : LazyList (MetaM (List ScheduleStep × Nat)) := do
  let (typedPreSchedules, scheduleEnv) := possiblePreSchedulesWithAdvancedPruning vars hypotheses deriveSort recCall fixedVars recFnName multiOutput
  let prunedImprovingTypedPreSchedules := filterWorse typedPreSchedules preScheduleStepsScore
  let lazySchedules := prunedImprovingTypedPreSchedules.mapLazyList
    ((ReaderT.run . scheduleEnv) ∘ (fun (s,c) => return (← s.flatMapM <| preScheduleStepToScheduleStep ctorName, c)))
  lazySchedules

/-- Bundle-aware schedule search using monadic SearchTree pruning.
    Faithfully replicates the enumeration logic of `possiblePreSchedulesWithAdvancedPruning`
    and `enumSchedulesChunkedWithPruning`, but uses the scoring bundle for all quality
    decisions and `minTreePruningM` for branch-and-bound over hypothesis orderings
    within each SCC component.

    The `deriveDep` callback is invoked when scoring encounters a dependency not yet
    in the memo. The caller can wire this to `deriveBestInductiveSchedule` to trigger
    on-demand recursive derivation (avoids circular imports).

    Returns `none` if no valid schedule exists. -/
partial def searchBestScheduleM (ctorName : Name) (vars : List TypedVar)
    (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
    (recCall : Name × List Nat) (fixedVars : List Name)
    (recFnName : Name := defaultRecFnName deriveSort) (multiOutput : Bool := false)
    (bundle : Scoring.ScorerBundle) (memo : IO.Ref (Std.HashMap SpecKey MemoEntry))
    (key : SpecKey) (limit : Nat := 200000)
    (deriveDep : SpecKey → MetaM Unit := fun _ => pure ()) : MetaM (Option (List ScheduleStep × Score × Nat)) := do
  -- 1. Set up ScheduleEnv (same as possiblePreSchedulesWithAdvancedPruning)
  let typeVars := vars.filterMap fun ⟨v,t⟩ => if t.isSort then some v else none
  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses
  let varNames := vars.map (fun x => x.var)
  let prodSort := convertDeriveSortToProducerSort deriveSort
  let scheduleEnv : ScheduleEnv := ⟨vars, sortedHypotheses, deriveSort, prodSort, recCall,
    fixedVars, recFnName, multiOutput, [], some memo⟩

  -- 2. Collect initially-checked hypotheses (same as existing)
  let (newCheckedIdxs, newCheckedHyps) := List.unzip <| (collectCheckedHypotheses scheduleEnv fixedVars [])

  -- 3. Compute SCC groups and build per-component SearchTrees
  let remainingSortedHypotheses := filterWithIndex (fun i _ => i ∉ newCheckedIdxs) sortedHypotheses
  let rawHypotheses := remainingSortedHypotheses.map (fun hv => (hv, List.flatten hv.snd))
  let sccGroups := computeSCC rawHypotheses
  -- Each component gets its own SearchTree (faithful to pure pipeline)
  let componentTrees := sccGroups.map fun scc =>
    (scc, SearchTree.enumDependencySatisfyingOrderingsTree scc)

  let matchableSet := Std.HashSet.ofList typeVars
  let nameTypeMap := List.foldl (fun m ⟨name,ty⟩ => NameMap.insert m name ty) ∅ vars
  let remainingVarNames := List.filter (fun v => not <| fixedVars.contains v) varNames

  -- Mutable state for global tracking
  let done ← IO.mkRef false
  let countRef ← IO.mkRef (0 : Nat)
  let bestRef ← IO.mkRef (none : Option (List ScheduleStep × Score))

  -- Helper: score a single pre-schedule step using the bundle
  let scorePreStep := fun (memoState : Std.HashMap SpecKey MemoEntry)
      (step : PreScheduleStep HypothesisExpr Name) (_env : Std.HashSet Name) => do
    let typedStep := typePreScheduleStep nameTypeMap step
    let schedSteps ← (preScheduleStepToScheduleStep ctorName typedStep).run scheduleEnv
    let stepScores := schedSteps.map fun s => bundle.stepScorer key memoState s
    return stepScores

  -- Helper: process mode choices for one hypothesis (replicates processChoice logic)
  -- Returns (newPreSteps, remainingHyps, newEnv, newEnvSet)
  let processModeChoices := fun (hyp : HypothesisExpr) (potential_output_indices : List (List Name))
      (always_bound_variables : List Name) (rest : List (HypothesisExpr × List (List Name) × List Name))
      (currentEnv : List Name) (currentEnvSet : Std.HashSet Name) => do
    let (some_bound_output_indices, all_unbound_output_indices) := potential_output_indices.partition
      (fun l =>
        l.any (fun v => currentEnvSet.contains v && !matchableSet.contains v)
        || l.all matchableSet.contains)
    -- Enumerate mode choices (same logic as enumSchedulesChunkedWithPruning)
    let choices : List (List (List Name) × List (List Name)) := if multiOutput then
        [(all_unbound_output_indices, [])]
      else
        ([], all_unbound_output_indices) :: (select all_unbound_output_indices).toList.map (fun (a, b) => ([a], b))
    -- Filter through processChoice to get valid choices
    let validChoices := choices.filterMap (fun (out, bound) =>
      processChoice multiOutput hyp out bound some_bound_output_indices
        always_bound_variables rest currentEnv currentEnvSet)
    match validChoices with
    | [] =>
      -- No valid choice (shouldn't happen in well-formed input, but handle gracefully)
      pure (([] : List (PreScheduleStep HypothesisExpr Name)), rest, currentEnv, currentEnvSet)
    | [single] => pure single
    | multiple =>
      -- Score each valid choice and pick the best
      let memoState ← memo.get
      let scored ← multiple.mapM fun choice => do
        let (newSteps, _, _, _) := choice
        let stepScores ← newSteps.flatMapM (scorePreStep memoState · currentEnvSet)
        let score := bundle.scheduleScorer stepScores
        return (choice, score)
      let best := scored.foldl (fun acc (choice, score) =>
        match acc with
        | none => some (choice, score)
        | some (_, bestScore) =>
          if bundle.isBetter score bestScore then some (choice, score) else acc) none
      match best with
      | none => pure ([], rest, currentEnv, currentEnvSet)
      | some (choice, _) => pure choice

  -- Helper: given a hypothesis ordering for one component, process it through
  -- mode choices and return the resulting pre-schedule steps + final env
  let processOrdering := fun (ordering : List (HypothesisExpr × List (List Name)))
      (env : List Name) (envSet : Std.HashSet Name) => do
    let constructedHyps := ordering.map (constructHypothesis typeVars)
    let mut currentEnv := env
    let mut currentEnvSet := envSet
    let mut sched : List (PreScheduleStep HypothesisExpr Name) := []
    let mut remaining := constructedHyps
    while !remaining.isEmpty do
      match remaining with
      | [] => break
      | (hyp, potential_output_indices, always_bound_variables) :: rest =>
        let (newSteps, to_be_satisfied', finalEnv, finalEnvSet) ←
          processModeChoices hyp potential_output_indices always_bound_variables rest currentEnv currentEnvSet
        sched := sched ++ newSteps
        currentEnv := finalEnv
        currentEnvSet := finalEnvSet
        remaining := to_be_satisfied'
    return (sched, currentEnv, currentEnvSet)

  -- Dominance pruning: tracks best score for each env state (sorted bound var set)
  let envDominanceRef ← IO.mkRef ({} : Std.HashMap (List Name) Score)

  -- Helper: score an ordering via processChoice → ScheduleSteps → bundle.
  -- Dominance: if this env state was reached before with a better score, return penaltyScore.
  -- On-demand: derives unknown deps before scoring.
  let scoreComponentOrdering := fun (env : List Name) (envSet : Std.HashSet Name)
      (ordering : List (HypothesisExpr × List (List Name))) => do
    let (compSched, compEnv, _) ← processOrdering ordering env envSet
    let typedSteps := compSched.map (typePreScheduleStep nameTypeMap)
    let schedSteps ← (typedSteps.flatMapM (preScheduleStepToScheduleStep ctorName)).run scheduleEnv
    -- On-demand dep derivation
    let deps := collectNonRecDeps schedSteps
    for dep in deps do
      if dep.kind == DepKind.relation || dep.kind == DepKind.checker then
        let depKey : SpecKey := { inductiveName := dep.inductiveName,
                                  outputIndices := dep.outputIndices,
                                  deriveSort := dep.deriveSort }
        if depKey != key then
          let m ← memo.get
          unless m.contains depKey do deriveDep depKey
    -- Score
    let memoState ← memo.get
    let score := bundle.scheduleScorer (schedSteps.map fun step => bundle.stepScorer key memoState step)
    -- Dominance check (same structure as original: if dominated, signal pruning)
    let envKey := compEnv.eraseDups |>.mergeSort (fun a b => compare a b |>.isLE)
    let envDom ← envDominanceRef.get
    match envDom[envKey]? with
    | some prevBest =>
      if bundle.isBetter prevBest score then return bundle.penaltyScore
    | none => pure ()
    envDominanceRef.modify fun m =>
      match m[envKey]? with
      | some prev => if bundle.isBetter score prev then m.insert envKey score else m
      | none => m.insert envKey score
    return score

  -- 4. Process SCC components sequentially using minTreePruningM per component
  let mut accSched : List (PreScheduleStep HypothesisExpr Name) := []
  let mut accEnv : List Name := fixedVars
  let mut accEnvSet : Std.HashSet Name := Std.HashSet.ofList fixedVars

  for (_, tree) in componentTrees do
    if ← done.get then break
    -- Use minTreePruningM to find the best ordering for this component
    let componentDone ← IO.mkRef false
    -- Tree yields List α where α = HypothesisExpr × List (List Name)
    -- (the List Name from rawHypotheses is consumed as v for SCC edges)
    let componentBestRef ← IO.mkRef (none : Option (List (PreScheduleStep HypothesisExpr Name) × List Name × Std.HashSet Name × Score))
    let componentWorst := bundle.penaltyScore
    let envSnapshot := accEnv
    let envSetSnapshot := accEnvSet

    let _ ← SearchTree.minTreePruningM tree (scoreComponentOrdering envSnapshot envSetSnapshot)
      bundle.isBetter componentWorst componentDone
      fun (ordering, score) currentBest => do
        let c ← countRef.get
        countRef.set (c + 1)
        if c + 1 > limit then
          done.set true
          componentDone.set true
          return currentBest
        -- Process this ordering through mode choices
        let (compSched, compEnv, compEnvSet) ← processOrdering ordering envSnapshot envSetSnapshot
        -- Track best for this component
        match ← componentBestRef.get with
        | none =>
          componentBestRef.set (some (compSched, compEnv, compEnvSet, score))
        | some (_, _, _, prevScore) =>
          if bundle.isBetter score prevScore then
            componentBestRef.set (some (compSched, compEnv, compEnvSet, score))
        -- Return the score for pruning decisions
        return if bundle.isBetter score currentBest then score else currentBest

    -- Use the best ordering found for this component
    match ← componentBestRef.get with
    | none => pure ()
    | some (compSched, compEnv, compEnvSet, _) =>
      accSched := accSched ++ compSched
      accEnv := compEnv
      accEnvSet := compEnvSet

  -- 5. Build final schedule: firstChecks + component schedules + remaining vars
  let remainingUninstantiated := remainingVarNames.filter (!accEnvSet.contains ·)
  let finalPreSteps := (PreScheduleStep.Checks newCheckedHyps.reverse :: accSched ++
    prune_empties [.InstVars remainingUninstantiated]).map (typePreScheduleStep nameTypeMap)

  -- Convert to ScheduleSteps
  let scheduleSteps ← (finalPreSteps.flatMapM (preScheduleStepToScheduleStep ctorName)).run scheduleEnv

  -- 6. Trigger on-demand dep derivation for unknown deps
  let deps := collectNonRecDeps scheduleSteps
  for dep in deps do
    if dep.kind == .relation || dep.kind == .checker then
      let depKey : SpecKey := { inductiveName := dep.inductiveName,
                                outputIndices := dep.outputIndices,
                                deriveSort := dep.deriveSort }
      if depKey != key then
        let memoState ← memo.get
        unless memoState.contains depKey do
          deriveDep depKey

  -- 7. Score using the bundle with up-to-date memo
  let memoState ← memo.get
  let fullScore := bundle.scheduleScorer
    (scheduleSteps.map fun step => bundle.stepScorer key memoState step)
  bestRef.set (some (scheduleSteps, fullScore))

  let count ← countRef.get
  match ← bestRef.get with
  | none => return none
  | some (steps, score) => return some (steps, score, count)

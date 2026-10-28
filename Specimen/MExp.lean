import Specimen.Debug
import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.Enumerators
import Specimen.DecOpt
import Specimen.TSyntaxCombinators
import Batteries.Lean.Expr
import Specimen.Schedules
import Specimen.UnificationMonad
import Specimen.Idents
import Specimen.Utils

namespace MExp

open Plausible
open Idents Schedules
open Lean Parser Elab Term Command ToExpr TSyntax

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- The sort of monad we are compiling to, i.e. one of the following:
    - An unconstrained / constrained generator (`Gen`)
    - An unconstrained / constrained enumerator (`Enumerator` / `Except GenError Enumerator`)
    - A Checker (`Except GenError Bool` monad) -/
inductive MonadSort
  | Gen
  | Enumerator
  | OptionTEnumerator
  | Checker
  deriving Repr, BEq

/-- Determines whether a `MonadSort` corresponds to a monad
    for an enumerator (i.e. `Enumerator` or `OptionT Enumerator`) -/
def MonadSort.isEnumerator : MonadSort → Bool
  | .Enumerator | .OptionTEnumerator => true
  | _ => false

/-- An intermediate representation of monadic expressions that are
    used in generators/enumerators/checkers.
    - Schedules are compiled to `MExp`s, which are then compiled to Lean code
    - Note: `MExp`s make it easy to optimize generator code down the line
      (e.g. combine pattern-matches when we have disjoint patterns
    - The cool thing about `MExp` is that we can interpret it differently
      based on the `MonadSort` -/
inductive MExp : Type where
  /-- `MRet e` represents `return e` in some monad -/
  | MRet (e : MExp)

  /-- `MBind monadSort m1 vars m2` represents `m1 >>= fun vars => m2` in a particular monad,
       as determined by `monadSort` -/
  | MBind (monadSort : MonadSort) (m1 : MExp) (vars : List (Name × Option Expr)) (m2 : MExp)

  /-- N-ary function application -/
  | MApp (explicit : Explicit) (f : MExp) (args : List MExp)

  /-- N-ary constructor application -/
  | MCtr (explicit : Explicit) (c : Name) (args : List MExp)

  /-- Some constant name (e.g. refers to functions) -/
  | MConst (name : Name)

  /-- `MMatch scrutinee [(p1, e1), …, (pn, en)]` represents
       ```lean
       match scrutinee with
       | p1 => e1
       ...
       | pn => en
       ```
  -/
  | MMatch (explicit : Explicit) (scrutinee : MExp) (cases : List (Pattern × MExp))

  /-- Refers to a variable identifier -/
  | MId (name : Name)

  /-- A function abstraction, where `args` is a list of variable names,
      and `body` is an `MExp` representing the function body -/
  | MFun (args : List (Name × Option Expr)) (body : MExp)

  /-- A natural number or string literal. -/
  | MLit (l : Literal)

  /-- Signifies failure (corresponds to the term `OptionT.fail`) -/
  | MFail

  /-- Signifies running out of fuel -/
  | MOutOfFuel

  | MHole
  | MSort (lvl : Level)

  deriving Repr, Inhabited, BEq


/-- Converts a `ProducerSort` to a `MonadSort`
    representing an unconstrained producer (i.e. `Gen` or `Enumerator`) -/
def prodSortToMonadSort (prodSort : ProducerSort) : MonadSort :=
  match prodSort with
  | .Enumerator => MonadSort.Enumerator
  | .Generator => MonadSort.Gen

/-- Converts a `ProducerSort` to a `MonadSort`
    representing a *constrained* producer
    (i.e. `OptionT Gen` or `OptionT Enumerator`) -/
def prodSortToOptionTMonadSort (prodSort : ProducerSort) : MonadSort :=
  match prodSort with
  | .Enumerator => MonadSort.OptionTEnumerator
  | .Generator => MonadSort.Gen

/-- `MExp` representation of `EnumSizedSuchThat.enumSizedST`,
    where `prop` is the `Prop` constraining the value being enumerated
    and `fuel` is an `MExp` representing the fuel argument to the enumerator -/
def enumSizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``EnumSizedSuchThat.enumSizedST) [.MHole, prop, .MHole, fuel]

/-- `MExp` representation of `ArbitrarySizedSuchThat.arbitrarySizedST`,
    where `prop` is the `Prop` constraining the value being generated
    and `fuel` is an `MExp` representing the fuel argument to the generator -/
def arbitrarySizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``ArbitrarySizedSuchThat.arbitrarySizedST) [.MHole, prop, .MHole, fuel]

/-- `MExp` representation of `BacktrackGenFor.gen`, the Basalt-general counterpart of
    `arbitrarySizedST`.

    Five more holes than `arbitrarySizedST` because the field is
    `{α} → (P) → [inst] → {G} → [Gen G] → [Fail G] → [FailWith _ G] → [Backtrack G] → Nat → G α`:
    under `@` every binder must be supplied, so `G` gets a hole solved by unification against the
    expected type, and its instances get holes solved by instance synthesis.

    The name is unqualified so it resolves in the *emitted* code's scope rather than requiring
    Specimen's own modules to import Basalt. -/
def backtrackGenForCall (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst (Name.mkStr2 "BacktrackGenFor" "gen"))
    [.MHole, prop, .MHole, .MHole, .MHole, .MHole, .MHole, .MHole, fuel]

/-- `ok x` is an `MExp` representing `Except.ok x`. -/
def ok (x : MExp) : MExp :=
  .MApp .allowImplicit (.MConst ``Except.ok) [x]

/-- `okTrue` is an `MExp` representing `ok true`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def okTrue : MExp :=
  ok (.MConst ``true)

/-- `okFalse` is an `MExp` representing `ok false`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def okFalse : MExp :=
  ok (.MConst ``false)


/-- Converts a `List α` to a right-nested "tuple", where the function `pair`
    is used to create tuples. Produces `(a, (b, c))` for `[a, b, c]`. -/
def tupleOfList [Inhabited α] (pair : α → α → α) (l : List α) (default : Option α) : α :=
  match l with
  | [] => default.get!
  | [x] => x
  | x :: xs => pair x (tupleOfList pair xs default)


/-- Converts a list of `Pattern`s to a one single `Pattern` expressed
    as a tuple -/
def patternTupleOfList (xs : List Pattern) : Pattern :=
  tupleOfList (fun x y => Pattern.CtorPattern ``Prod.mk [x, y]) xs none

/-- Compiles a `Pattern` to a `TSyntax term` -/
partial def compilePattern (explicit : Explicit) (p : Pattern) : MetaM (TSyntax `term) :=
  match p with
  | .UnknownPattern u => `($(mkIdent u):ident)
  | .CtorPattern ctorName args => do
    let compiledArgs ← args.toArray.mapM <| compilePattern explicit
    match explicit with
    | .allExplicit =>
    `(@$(mkIdent ctorName):ident $compiledArgs*)
    | .allowImplicit =>
    `($(mkIdent ctorName):ident $compiledArgs*)
  | .LitPattern l => mkLiteral l


/-- Names a pattern binds. -/
partial def patternVars : Pattern → List Name
  | .UnknownPattern u => [u]
  | .CtorPattern _ args => args.flatMap patternVars
  | .LitPattern _ => []

/-- Whether `c` is the only constructor of its type. -/
private def soleCtor (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo ci) =>
    match env.find? ci.induct with
    | some (.inductInfo ii) => ii.ctors.length == 1
    | _ => false
  | _ => false

/-- Matches every value once variables are erased — so testing it would filter nothing, and Lean would
    reject the `| _ => false` arm after it as redundant. A name that is a constructor (`Pattern` spells
    nullary constructors as `UnknownPattern` too) is irrefutable only if it is its type's sole constructor. -/
partial def irrefutableErased (env : Environment) : Pattern → Bool
  | .UnknownPattern u => !env.isConstructor u || soleCtor env u
  | .CtorPattern c args => soleCtor env c && args.all (irrefutableErased env)
  | .LitPattern _ => false

/-- `p` as a pattern term with every variable replaced by a `_` **hole**. (`mkIdent `_` would be a
    variable *named* `_`, and two of them in one pattern clash.) Constructor names are kept. -/
partial def compileErasedPattern (env : Environment) (explicit : Explicit) : Pattern → MetaM (TSyntax `term)
  | .UnknownPattern u => if env.isConstructor u then `($(mkIdent u):ident) else `(_)
  | .CtorPattern ctorName args => do
    let compiledArgs ← args.toArray.mapM (compileErasedPattern env explicit)
    match explicit with
    | .allExplicit => `(@$(mkIdent ctorName):ident $compiledArgs*)
    | .allowImplicit => `($(mkIdent ctorName):ident $compiledArgs*)
  | .LitPattern l => mkLiteral l

/-- The input test a branch's schedule starts with, as a `Bool` term — or `none` if it starts with none.

    Walks the **leading** `.Match` steps. A step whose scrutinee is not bound by an earlier leading pattern
    must be an input (nothing else is bound yet), and contributes
    `match x with | ⟨pattern, variables erased⟩ => true | _ => false`; a step on a variable an earlier
    pattern bound is skipped (it would need a nested match), as is one whose erased pattern is irrefutable.
    Skipping only weakens the guard. The result is implied by the branch's own leading matches succeeding,
    so filtering on it is sound. -/
def inputGuard? (steps : List ScheduleStep) : MetaM (Option (TSyntax `term)) := do
  let env ← getEnv
  let mut bound : List Name := []
  let mut tests : Array (TSyntax `term) := #[]
  for step in steps do
    match step with
    | .Match explicit scrutinee pattern =>
      if !bound.contains scrutinee && !irrefutableErased env pattern then
        let lhs ← compileErasedPattern env explicit pattern
        tests := tests.push (← `(match $(mkIdent scrutinee):ident with | $lhs => true | _ => false))
      bound := bound ++ patternVars pattern
    | _ => break
  if tests.isEmpty then return none
  let mut acc := tests[0]!
  for t in tests[1:] do
    acc ← `($acc && $t)
  return some acc

/-- `MExp` representation of a `DecOpt` instance (a checker).
    Specifically, `decOptChecker prop fuel` represents the term
    `DecOpt.decOpt $prop $fuel`. -/
def decOptChecker (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``DecOpt.decOpt) [prop, .MHole, fuel]

/-- Converts a `ConstructorExpr` to an `MExp` -/
partial def constructorExprToMExp (exp : Explicit) (expr : ConstructorExpr) : MExp :=
  match expr with
  | .Unknown u => .MId u
  | .Hole => .MHole
  | .Ctor c args | .TyCtor c args => .MCtr exp c (constructorExprToMExp exp <$> args)
  | .FuncApp f args => .MApp exp (.MId f) (constructorExprToMExp exp <$> args)
  | .Lit l => .MLit l
  | .CSort lvl => .MSort lvl

partial def mexpToConstructorExpr (m : MExp) : Option ConstructorExpr :=
  match m with
  | .MId u => return .Unknown u
  | .MCtr _explicit c args => do
    let convertedArgs ← args.mapM mexpToConstructorExpr
    return .Ctor c convertedArgs
  | .MApp _explicit (.MId f) args => do
    let convertedArgs ← args.mapM mexpToConstructorExpr
    return .FuncApp f convertedArgs
  | .MLit l => return .Lit l
  | .MSort lvl => return .CSort lvl
  | .MHole => return .Hole
  | _ => none

/-- `MExp` representation of a recursive function call,
    where `f` is the function name, `fuelPrimeName` is the name for `fuel'`,
    `sizeExpr` is the size budget expression passed to the recursive call (an `MExp` rather
    than a bare `Name` because it may be `size' / N` when the constructor has N size-consuming
    calls — see `countSizeConsumingCalls`), and `args` are the input arguments -/
def recCall (f : Name) (fuelPrimeName : Name) (sizeExpr : MExp) (args : List ConstructorExpr) : MExp :=
  .MApp .allowImplicit (.MId f) $
    [.MId fuelPrimeName, .MId `initSize, sizeExpr] ++ (constructorExprToMExp .allExplicit <$> args)

/-- Converts a `HypothesisExpr` to an `MExp` -/
def hypothesisExprToMExp (hypExpr : HypothesisExpr) : MExp :=
  let (ctorName, ctorArgs) := hypExpr
  .MCtr .allExplicit ctorName (constructorExprToMExp .allExplicit <$> ctorArgs)

def hypothesisMExpToExpr (m : MExp) : Option Expr := do
  let .MCtr .allExplicit ctorName args := m | none
  let cargs ← args.mapM mexpToConstructorExpr
  return constructorExprToExpr ((.Ctor ctorName cargs))

/-- `Pattern` that represents a wildcard (i.e. `_` on the LHS of a pattern-match) -/
def wildCardPattern : Pattern :=
  .UnknownPattern `_

/-- `MExp` representing a pattern-match on a `scrutinee` of type `Except _ Bool`.
     Specifically, `matchOptionBool scrutinee trueBranch falseBranch` represents
     ```lean
     match scrutinee with
     | .ok true => $trueBranch
     | .ok false => $falseBranch
     | .error _ => $MExp.MOutOfFuel
     ```
-/
def matchExceptBool (scrutinee : MExp) (trueBranch : MExp) (falseBranch : MExp) : MExp :=
  .MMatch .allowImplicit scrutinee
    [
      (.CtorPattern ``Except.ok [.UnknownPattern ``true], trueBranch),
      (.CtorPattern ``Except.ok [.UnknownPattern ``false], falseBranch),
      (.CtorPattern ``Except.error [wildCardPattern], .MOutOfFuel)
    ]

/-- `CompileScheduleM` is a monad for compiling `Schedule`s to `TSyntax term`s.
    Under the hood, this is just a `State` monad stacked on top of `TermElabM`,
    where the state is an `Array` of `TSyntax term`s, representing any auxiliary typeclass
    instances that need to derived beforehand.  -/
abbrev CompileScheduleM (α : Type) := StateT (TSyntaxArray `term) TermElabM α

/-- `MExp` representation of an unconstrained producer,
    parameterized by a `producerSort` and the type `ty` (represented as a `TSyntax term`)
    of the value being generated -/
def unconstrainedProducer (prodSort : ProducerSort) (ty : TSyntax `term)
    (fuel : MExp := .MId `initSize) : CompileScheduleM MExp := do
  -- Under Basalt an unconstrained sub-producer must be polymorphic in the generator monad, so
  -- Plausible's `Arbitrary` (fixed at `Plausible.Gen`) cannot be used — it type-errors inside a
  -- Basalt-targeted body.
  --
  -- `Basalt.ArbitraryFueled` rather than `Basalt.Arbitrary`, for two reasons. Basalt's `Gen` has no
  -- ambient size parameter and hence no `sized`, so there is no `ArbitraryFueled → Arbitrary`
  -- instance to fall back on and a derived datatype only ever has the fueled form. And an
  -- unconstrained generator for a *recursive* datatype ought to be bounded anyway: `initSize` is the
  -- right budget, being the allocation meant for independent dependencies.
  let useBasalt := (Lean.Option.get (← getOptions) specimen.emitBasalt)
    && prodSort matches .Generator
  let typeClassName :=
    if useBasalt then Name.mkStr2 "Basalt" "ArbitraryFueled"
    else match prodSort with
    | .Enumerator => ``Enum
    | .Generator => ``Arbitrary
  let typeClassInstance ← `( $(Lean.mkIdent typeClassName) $ty:term )

  -- Add the `typeClassInstance` for the unconstrained producer to the state,
  -- then obtain the `MExp` representing the unconstrained producer
  StateT.modifyGet $ fun instances =>
    let producerMExp :=
      if useBasalt then
        .MApp .allowImplicit (.MConst (Name.mkStr3 "Basalt" "ArbitraryFueled" "arbitraryFueled")) [fuel]
      else match prodSort with
      | .Enumerator => .MConst ``Enum.enum
      | .Generator => .MConst ``Arbitrary.arbitrary
    (producerMExp, instances.push typeClassInstance)

mutual

  partial def delabMexpAsExpr (mexp : MExp) : CompileScheduleM (TSyntax `term) := do
    let a ← (pure <$> hypothesisMExpToExpr mexp).getD (throwError "hypothesis mexp fails to turn to expr")
    let lctx ← getLCtx
    delabExprInLocalContext lctx a

  /-- Compiles a `MExp` to a Lean `doElem`, according to the `DeriveSort` provided -/
  partial def mexpToTSyntax (mexp : MExp) (deriveSort : DeriveSort) : CompileScheduleM (TSyntax `term) :=
    match mexp with
    | .MSort _ => `(Sort _)
    | .MHole => `(_)
    | .MId v | .MConst v => `($(mkIdent v))
    | .MApp explicit func args => do
      let f ← mexpToTSyntax func deriveSort
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      match explicit with
      | .allowImplicit => `($f $compiledArgs*)
      | .allExplicit => `(@$f $compiledArgs*)
    | .MCtr explicit ctorName args => do
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      match explicit with
      | .allowImplicit => `($(mkIdent ctorName) $compiledArgs*)
      | .allExplicit => `(@$(mkIdent ctorName) $compiledArgs*)
    | .MFun vars body => do
      let compiledBody ← mexpToTSyntax body deriveSort
      match vars with
      | [] => throwError "empty list of function arguments supplied to MFun"
        -- When we have multiple args, create a tuple containing all of them
        -- in the argument of the lambda
      | _ =>  do
        let args ← mkTuple vars
        `((fun $args:term => $compiledBody))
    | .MFail | .MOutOfFuel =>
      -- Outside the Basalt path these two compile to the same term, and the distinction survives only
      -- because `Gen.outOfFuelError` carries a message that `GenError.isInconclusive` recognises.
      -- Under Basalt one is a refutation (`Fail`) and the other a labelled failure (`FailWith`).
      do
      let useBasalt := (Lean.Option.get (← getOptions) specimen.emitBasalt)
        && deriveSort matches .Generator
      if useBasalt then
        match mexp with
        | .MOutOfFuel => `($backtrackGenExhaustFn)
        | _ => `($backtrackGenRefuteFn)
      else
      match deriveSort with
      | .Generator | .Enumerator => `($failFn $genericFailure)
      | .Theorem => `(return ($(mkIdent ``Except.error) $genericFailure))
      | .Checker => `($(mkIdent ``Except.ok) $(mkIdent ``false))
    | .MRet e => do
      let e' ← mexpToTSyntax e deriveSort
      `(return $e')
    | .MBind monadSort m vars k => do
      -- Compile the monadic expression `m` and the continuation `k` to `TSyntax term`s
      let m1 ← mexpToTSyntax m deriveSort
      let k1 ← mexpToTSyntax k deriveSort
      match deriveSort, monadSort with
      | .Generator, .Gen
      | .Theorem, .Gen
      | .Enumerator, .Enumerator
      | .Enumerator, .OptionTEnumerator =>
        -- If there are multiple variables that are bound to the result
        -- of the monadic expression `m`, convert them to a tuple
        let compiledArgs ←
          if vars.isEmpty then
            throwError m!"empty list of vars supplied to MBind, deriveSort = {repr deriveSort}, monadSort = {repr monadSort}, m1 = {m1}, k1 = {k1}"
          else
            mkTuple vars
        -- If we have a producer, we can just produce a monadic bind
        `(do let $compiledArgs:term ← $m1:term ; $k1:term)
      | .Generator, .Checker
      | .Enumerator, .Checker => do
        -- If a producer invokes a checker, we have to invoke the checker
        -- provided by the `DecOpt` instance for the proposition, then pattern
        -- match on its result
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``Except.ok) $(mkIdent ``true) => $k1)
        let useBasalt := (Lean.Option.get (← getOptions) specimen.emitBasalt)
          && deriveSort matches .Generator
        -- `DecOpt` is three-valued, and the two failures mean different things: `ok false` is a
        -- definite "this constructor does not apply", `error` only says the checker ran out of budget.
        --
        -- Under `Plausible.Gen` there is nowhere to put that difference — failure is a single thrown
        -- error — so both collapse. Under Basalt they must not: a refutation is `Fail.fail` and an
        -- undecided premise `FailWith`, so an inconclusive premise stays inconclusive. Collapsing
        -- `error` into a refutation would let a *derived* checker that merely ran out of fuel be
        -- reported as a definite refutation of the whole branch, and `backtrack` would then be
        -- entitled to report a refutation for a relation that is in fact inhabited. This is the same
        -- distinction the `size = 0` case preserves with `Specimen.truncated`.
        let cases ←
          if useBasalt then do
            let falseCase ← `(Term.matchAltExpr|
              | $(mkIdent ``Except.ok) $(mkIdent ``false) => $backtrackGenRefuteFn)
            let errCase ← `(Term.matchAltExpr| | _ => $basaltInconclusiveFn)
            pure #[trueCase, falseCase, errCase]
          else do
            let wildCardCase ← `(Term.matchAltExpr| | _ => $failFn $genericFailure)
            pure #[trueCase, wildCardCase]
        `(match $m1:term with $cases:matchAlt*)
      | .Theorem, .Checker => do
        -- For theorem mode: return the error as a value rather than throwing,
        -- so the RNG state is not reset on discard
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``Except.ok) $(mkIdent ``true) => $k1)
        let wildCardCase ← `(Term.matchAltExpr| | _ => return ($(mkIdent ``Except.error) $genericFailure))
        let cases := #[trueCase, wildCardCase]
        `(match $m1:term with $cases:matchAlt*)
      | .Checker, .Checker =>
        -- If the continuation of the bind is just returning `some True`,
        -- we can just inline the checker call `m1` to avoid the extra indirection
        -- of calling checker combinator functions
        if k == okTrue then
          `($m1:term)
        else
          -- For checkers, we can just invoke `DecOpt.andOptList`
          `($andOptListFn [$m1:term, $k1:term])
      | .Checker, .Enumerator
      | .Checker, .OptionTEnumerator => do
          -- If there are multiple variables that are bound to the result
          -- of the enumerator `m`, convert them to a tuple
          let args ←
            if vars.isEmpty then
              throwError m!"empty list of vars supplied to MBind, deriveSort = {repr deriveSort}, monadSort = {repr monadSort}, m1 = {m1}, k1 = {k1}"
            else
              mkTuple vars
          let fuelForEnumerator ← `($initSizeIdent:term)
          match monadSort with
          | .Enumerator =>
            -- If a checker invokes an unconstrained enumerator,
            -- we call `EnumeratorCombinators.enumerating` a la QuickChick
            `($enumeratingFn $m1:term (fun $args:term => $k1:term) $fuelForEnumerator:term)
          | .OptionTEnumerator =>
            -- If a checker invokes a contrained enumerator,
            -- we call `EnumeratorCombinators.enumeratingOpt` a la QuickChick
            `($enumeratingOptFn $m1:term (fun $args:term => $k1:term) $fuelForEnumerator:term)
          | .(_) => throwError "Unreachable pattern match: Checkers can only invoke enumerators in this branch"
      | _, _ => throwError m!"Invalid monadic bind for deriveSort {repr deriveSort}"
    | .MMatch explicit scrutinee cases => do
      -- Compile the scrutinee, the LHS & RHS of each case separately
      let compiledScrutinee ← mexpToTSyntax scrutinee deriveSort
      let compiledCases ← cases.toArray.mapM (fun (pattern, rhs) => do
        let lhs ← compilePattern explicit pattern
        let compiledRHS ← mexpToTSyntax rhs deriveSort
        `(Term.matchAltExpr| | $lhs:term => $compiledRHS))
      `(match $compiledScrutinee:term with $compiledCases:matchAlt*)
    | .MLit l => mkLiteral l

  /-- `MExp` representation of a constrained producer,
      parameterized by a `producerSort`, a list of variable names & their types `varsTys`,
      and a `Prop` (`prop`) constraining the values being produced

      - Note: this function corresponds to `such_that_producer`
        in the QuickChick code -/
  partial def constrainedProducer (prodSort : ProducerSort) (varsTys : List (Name × Option ConstructorExpr)) (prop : MExp) (fuel : MExp) : CompileScheduleM MExp :=
    if varsTys.isEmpty then
      panic! "Received empty list of variables for constrainedProducer"
    else do
      -- Determine whether the typeclass instance for the constrained generator already exists
      -- i.e. check if an instance for `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` with the
      -- specified `argTys` and `prop` already exists
      let (args, argTys) := List.unzip varsTys
      let argTyExprs := argTys.map (Option.map ToExpr.toExpr)
      let typedArgs := List.zip args argTyExprs
      let argsTuple ← mkTuple typedArgs
      let propBody ← delabMexpAsExpr prop
      -- Under Basalt a constrained sub-producer is looked up through `BacktrackGenFor` rather than
      -- `ArbitrarySizedSuchThat`, both for the recorded instance constraint and for the call.
      let useBasalt := (Lean.Option.get (← getOptions) specimen.emitBasalt)
        && prodSort matches .Generator
      let typeClassName :=
        if useBasalt then Name.mkStr1 "BacktrackGenFor"
        else match prodSort with
        | .Enumerator => ``EnumSizedSuchThat
        | .Generator => ``ArbitrarySizedSuchThat
      let typeClassInstance ← `($(mkIdent typeClassName) `_ (fun $argsTuple:term => $propBody))

      -- Add the `typeClassInstance` for the constrained producer to the state,
      -- then obtain the `MExp` representing the constrained producer
      StateT.modifyGet $ fun instances =>
        let producerWithArgs := MExp.MFun typedArgs prop
        let producerMExp :=
          if useBasalt then backtrackGenForCall producerWithArgs fuel
          else match prodSort with
          | .Enumerator => enumSizedST producerWithArgs fuel
          | .Generator => arbitrarySizedST producerWithArgs fuel
        (producerMExp, instances.push typeClassInstance)

end

private def nameAndConstructorExprToTypedVar (v : Name × Option ConstructorExpr) : Name × Option Expr :=
  Prod.map id (ToExpr.toExpr <$> ·) v

/-- Compiles a `ScheduleStep` to an `MExp`.
     Note that `MExp` that is returned by this function is represented
     as a function `MExp → MExp`, akin to difference lists in Haskell
     (see https://www.seas.upenn.edu/~cis5520/22fa/lectures/stub/03-trees/DList.html)

    The arguments to this function are:
    - The current step of the schedule (`step`)
    - The function parameter `k` represents the remainder of the `mexp`
      (the rest of the monadic `do`-block)
    - `mfuel` and `defFuel` are `MExp`s representing the current size and the initial size
      supplied to the generator/enumerator/checker we're deriving
-/

def scheduleStepToMExp (step : ScheduleStep) (defFuel : MExp) (k : MExp) (outputType : Expr) (fuelPrimeName : Name) (sizeExpr : MExp) (targetInductive : Name) : CompileScheduleM MExp :=
  match step with
  | .Unconstrained v src prodSort => do
    let monadSort := prodSortToMonadSort prodSort
    match src with
    | Source.NonRec hyp => do
      let ty ← hypothesisExprToTSyntaxTerm hyp
      let tyExpr := ToExpr.toExpr hyp
      let producer ← unconstrainedProducer prodSort ty defFuel
      pure $ .MBind monadSort producer [⟨v,tyExpr⟩] k
    | Source.Rec f args | Source.MutRec f args =>
      pure $ .MBind monadSort (recCall f fuelPrimeName sizeExpr args) [⟨v, outputType⟩] k

  | .SuchThat varsTys prod ps => do
    let monadSort := prodSortToOptionTMonadSort ps
    let typedVars := List.map (nameAndConstructorExprToTypedVar) varsTys
    match prod with
    | Source.NonRec hypExpr => do
      -- Same-inductive deps share the split budget: since fuel (not size) guarantees
      -- termination, we can split size flexibly, and calls that construct the target
      -- output (even non-recursively, e.g. a different mode of the same relation)
      -- should share the budget rather than getting the full allocation meant for
      -- independent dependencies.
      let fuel := if hypExpr.1 == targetInductive then sizeExpr else defFuel
      let producer ← constrainedProducer ps varsTys (hypothesisExprToMExp hypExpr) fuel
      pure $ .MBind monadSort producer typedVars k
    | Source.Rec f args | Source.MutRec f args =>
      pure $ .MBind monadSort (recCall f fuelPrimeName sizeExpr args) typedVars k
  | .Check src polarity =>

    let checker :=
      match src with
      | Source.NonRec hypExpr =>
        -- Same-inductive deps share the split budget: since fuel (not size) guarantees
      -- termination, we can split size flexibly, and calls that construct the target
      -- output (even non-recursively, e.g. a different mode of the same relation)
      -- should share the budget rather than getting the full allocation meant for
      -- independent dependencies.
        let fuel := if hypExpr.1 == targetInductive then sizeExpr else defFuel
        decOptChecker (hypothesisExprToMExp hypExpr) fuel
      | Source.Rec f args | Source.MutRec f args =>
        recCall f fuelPrimeName sizeExpr args

    let checker :=
      if polarity then checker
      else .MApp .allowImplicit (.MConst ``DecOpt.negOpt) [checker]

    pure $ .MBind .Checker checker [] k
  | .Match explicit scrutinee pattern =>
    pure $ .MMatch explicit (.MId scrutinee) [(pattern, k), (wildCardPattern, .MFail)]

/-- The steps of a recursive constructor's schedule that decide whether its conclusion applies to the
    inputs: its leading input matches, and the checks on inputs alone that follow them (a non-linear
    conclusion's equalities among them). -/
def conclusionSteps (steps : List ScheduleStep) : List ScheduleStep :=
  steps.takeWhile fun
    | .Match .. => true
    | .Check (.NonRec _) _ => true
    | _ => false

/-- The `size = 0` stand-in for a recursive constructor: its conclusion is matched against the inputs
    (`conclusionSteps`), and where it matches the constructor is cut off with `Specimen.truncated`
    rather than refuted, since it would apply at a larger size. Where it does not match, the match
    fails and refutes, so a disjunction none of whose recursive constructors could apply is still
    refuted. Nothing after the conclusion is run, so no size is spent. -/
def truncationToMExp (steps : List ScheduleStep) (defFuel : MExp) (recType : Expr)
    (fuelPrimeName : Name := `fuel') (targetInductive : Name := `_unknown) : CompileScheduleM MExp :=
  List.foldrM (fun step acc => scheduleStepToMExp step defFuel acc recType fuelPrimeName
      (.MLit (.natVal 0)) targetInductive)
    (.MConst (Name.mkStr2 "Specimen" "truncated")) (conclusionSteps steps)

/-- Converts a `Schedule` (a list of `ScheduleStep`s along with a `ScheduleSort`,
    which acts as the conclusion of the schedule) to an `MExp`.
    - `mfuel` and `defFuel` are auxiliary `MExp`s representing the fuel
      for the function we are deriving (these correspond to `size` and `initSize`
      in the QuickChick code for the derived functions)
    - `targetInductive` is the inductive we're generating for (used to detect same-type deps) -/
def scheduleToMExp (schedule : Schedule) (mfuel : MExp) (defFuel : MExp) (recType : Expr) (fuelPrimeName : Name := `fuel') (sizePrimeName : Name := `size') (targetInductive : Name := `_unknown) : CompileScheduleM MExp :=
  let (scheduleSteps, scheduleSort) := schedule
  -- Compute the size expression: split budget across all size-consuming calls
  -- (self-recursive, mutual, and non-recursive calls to the same inductive)
  let numSizeCalls := Schedules.countSizeConsumingCalls targetInductive scheduleSteps
  let sizeExpr : MExp :=
    if numSizeCalls ≤ 1 then .MId sizePrimeName
    else .MApp .allExplicit (.MConst ``Nat.div) [.MId sizePrimeName, .MLit (.natVal numSizeCalls)]
  -- Determine the *epilogue* of the schedule (i.e. what happens after we
  -- have finished executing all the `scheduleStep`s)
  let epilogue :=
    match scheduleSort with
    | .ProducerSchedule _ conclusionOutputs =>
      -- Convert all the outputs in the conclusion to `mexp`s
      let conclusionMExps := constructorExprToMExp .allowImplicit <$> conclusionOutputs
      -- If there are multiple outputs, wrap them in a tuple
      match conclusionMExps with
      | [] => panic! "No outputs being returned in producer schedule"
      | [output] => MExp.MRet output
      | outputs => MExp.MRet (tupleOfList (fun e1 e2 => .MApp .allowImplicit (.MConst ``Prod.mk) [e1, e2]) outputs outputs[0]?)
    | .CheckerSchedule => okTrue
    | .TheoremSchedule conclusion typeClassUsed =>
      -- Create a pattern-match on the result of the checker
      -- on the conclusion, returning `.ok true` or `.ok false` accordingly.
      -- Use MRet to wrap in the Gen monad (since the theorem body is monadic).
      let conclusionMExp := hypothesisExprToMExp conclusion
      let scrutinee :=
        if typeClassUsed then decOptChecker conclusionMExp mfuel
        else conclusionMExp
      matchExceptBool scrutinee (.MRet okTrue) (.MRet okFalse)
  -- Fold over the `scheduleSteps` and convert each of them to a functional `MExp`
  -- Note that the fold composes the `MExp`, and we use `foldr` since
  -- we want the `epilogue` to be the base-case of the fold
  List.foldrM (fun step acc => scheduleStepToMExp step defFuel acc recType fuelPrimeName sizeExpr targetInductive)
    epilogue scheduleSteps

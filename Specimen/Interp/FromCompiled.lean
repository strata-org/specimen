import Specimen
import Specimen.Interp

/-!
# Starting the interpreter from the deriver's own choice

The runtime interpreter used to begin learning from its own default — `deriveModeIn`'s first resolvable
plan, fewest checks — and that default is not what `derive_mutual` ships. On Cedar's `HasType[0,3,4]` the
two disagreed on 31 of 76 constructors, so a learned book mixed two kinds of difference that cannot be
told apart afterwards: places where measurement beat branch and bound, and places where the interpreter
merely started somewhere else. Only the first kind is worth pinning.

So learning starts here instead: run the deriver's search unpinned, read back the premise order it settled
on for every `(mode, constructor)` it derived (`Schedules.chosenOrdersRef`), and turn that into a
`PlanBook` (`PlanBook.ofOrders`). A learned book's `PlanBook.diff` against this one is then exactly the
set of constructors where dynamic measurement overruled the static estimate.

It is only a faithful start if the interpreter lowers each recorded order to the schedule the deriver
emitted. That is now **certified**, by `DeriverChoice.agreement` (`Interp.FromCompiledAgreement`), whose
comparator is sound: it may call two equivalent schedules different, never two different ones the same.
On Cedar's `HasType[0,4]` closure, with dispatch off, **907 of 907** generator constructors agree — every
one the interpreter samples, including the 46 at instantiated polymorphic modes — and re-ordering one root
constructor's premises is caught (906 agree, 1 differs). That needed four fixes first: the interpreter's
non-linear-pattern and instance-argument handling, the deriver's classification of type abbreviations
(`Attr`), and publishing derived checkers under their function names.

What follows is the history, kept because it explains the numbers elsewhere. An earlier comparator that
did not pin inputs, compare outputs, or erase type arguments by position reported 1756 of 1870 recorded
orders agreeing, and, of the closure, the figures below. In the
closure the interpreter actually samples, every one of the 907 generator constructors is planned from
the book; 861 sit at monomorphic modes with a compiled schedule under the same key, and 820 of those
agree (compared up to alpha-renaming, type arguments erased, commuting check/match runs canonicalised;
the rest differ in where a check or match lands). The other 46 sit at *instantiated* modes of
polymorphic relations (`MapContains[2]@(0:Attr, 1:QualifiedType)`), which the deriver derives once,
uninstantiated; they reach the book through `PlanBook.find?`'s fallback to the uninstantiated key, and
match their compiled schedule up to the type arguments' spelling, which that comparison does not
normalise. On `BST` it holds for all of them (`SpecimenTest.Interp.FromCompiledTest`).

Faithful is not the same as good. On that Cedar closure the compiled start reaches 126 distinct 3-paths
where the interpreter's own default reaches 198 (dispatch on; 115 against 175 off) — see
`CedarGen/Relational/SpecimenFromCompiledProbe.lean` in the Cedar tree, which also runs the first
learning pass from here. (Before the `find?` fallback those 46 polymorphic constructors silently ran the
interpreter's default, and the compiled start measured 129 and 116.)

Kept out of `Specimen.Interp` for the same reason as `Interp.Correspondence`: `Interp` does not depend
on the compile-time deriver, and that independence is worth keeping. `ofOrders` takes plain tuples for
exactly that reason; this module is the one place that connects the two.
-/

open Lean Schedules Specimen Specimen.Interp

namespace Specimen.Interp

/-- What the deriver settled on for one root and everything its search pulled in. -/
structure DeriverChoice where
  /-- The settled premise order per `(mode, constructor)`, in the interpreter's basis — the contents of
      `chosenOrdersRef` after the derivation, and nothing from any earlier one. -/
  orders : PinnedOrders
  /-- The deriver's memo, holding the schedules those orders lowered to: the comparison target for
      anyone checking that the interpreter reproduces them. -/
  memo : Std.HashMap SpecKey MemoEntry
  /-- Per `(mode, constructor)`, the badness the emitted weight receives: `scaleBadness` of the active
      scorer bundle's `scoreBadness` on the constructor's score, exactly as `compileWeightedProducer`
      computes it. Keyed without type arguments, as the deriver keys everything. -/
  badness : List (SpecKey × Name × Nat) := []
  /-- The weight the emitted code computes: the active weight function, passed through the active
      weight modifier when one is set. -/
  weightFn : CtorWeightFn := balancedCtorWeight

namespace DeriverChoice

/-- Every order the deriver settled on — generator, checker and enumerator modes alike. This is the
    faithful start.

    A checker's *verdict* does not depend on its premise order, but its *cost* does, and by orders of
    magnitude. On Cedar, `ValidEntityType` refuting a type that is not in the schema took **66 s** under
    the interpreter's default orders and **5 ms** under the deriver's: the default `isAction` branch
    enumerates `MapContainsPairKey`'s `eid` blind and then checks `b ≠ b'`, where the deriver takes it from
    the recursive call. That one checker put a 65-second tail on about one sample in fifteen at size 5,
    which made the interpreter unusable at the sizes Cedar actually tests (`propertyTest` runs at 12).
    Under this book, 50 samples at size 12 take 0.4–2.7 s. -/
def book (c : DeriverChoice) : PlanBook := PlanBook.ofOrders c.orders

/-- The orders at **generator** modes only, with checker and enumerator modes left to the interpreter's
    default. Kept for comparison; prefer `book`.

    This used to be the start, on the grounds that non-generator orders sampled identically at size 4 and
    that the full book needed a `List String` enumerator leaf nobody had registered. Both reasons are
    gone: instance leaves (`withInstanceLeaves`) supply the enumerator, and at realistic sizes the default
    checker orders are what make sampling slow (see `book`). -/
def generatorBook (c : DeriverChoice) : PlanBook :=
  PlanBook.ofOrders (c.orders.filter (fun (k, _, _) => k.deriveSort == .Generator))

/-- The schedule the deriver emitted for one constructor of one mode, if it derived that mode.

    `none` also for a mode the deriver found an existing instance for (`alreadyExists`): it derived no
    schedule there, and the interpreter has to supply that mode from a leaf. -/
def schedule? (c : DeriverChoice) (key : SpecKey) (ctorName : Name) : Option Schedule :=
  match c.memo[key]? with
  | some (.done ind) =>
    ((ind.baseSchedules ++ ind.recSchedules).find? (fun p => p.1 == ctorName)).map (·.2)
  | _ => none

/-- A closure made to sample with the **compiled** constructor weights: the deriver's per-constructor
    badness on every mode it derived, and its weight function and modifier.

    Faithful schedules are not a faithful generator. A derived interpreter mode has no badness of its own
    and samples with the default weight function, while compiled code weights each constructor by its
    scorer's badness and any modifier — so the two draw constructors with different frequencies, and an
    order that helps one need not help the other. On Cedar the order learning found for
    `HasType.hasAttrEntity` took the interpreter from 115 to 168 distinct 3-paths and did nothing for the
    compiled generator (159 unpinned, 155 pinned, 800 samples each). Learning must measure the generator
    that will actually ship. -/
def withCompiledWeights (c : DeriverChoice) (env : InterpEnv) : InterpEnv :=
  let relations := env.relations.fold (fun acc key rel =>
    let bare : SpecKey := { key with typeArgs := [] }
    let bad := c.badness.filterMap (fun (k, n, b) => if k == bare then some (n, b) else none)
    acc.insert key (if bad.isEmpty then rel else { rel with badness := bad })) env.relations
  { env with relations := relations, weightFn := c.weightFn }

end DeriverChoice

/-- Runs the deriver's search for `root`, **unpinned**, and returns the orders it settled on.

    Three things make the answer the deriver's own, rather than an artefact of how it was called:

    * `specimen.multiOutput` is set, as `derive_mutual` sets it. Without it the deprecated single-output
      path runs, under which a premise order does not determine the schedule, and the recorded orders
      would not lower to anything the pipeline emits.
    * `pinnedOrdersRef` is set to `pins` for the duration — empty by default. A pin a file installed for
      its own `derive_mutual` would be recorded as "settled on" (pinned orders are recorded too), and the
      book would reproduce the pin instead of branch and bound. Passing `pins` deliberately gives what
      the compiled generator would get *with* them — including the badness, which is a function of the
      schedule, so a pinned constructor's weight changes with its order.
    * The memo is fresh and `chosenOrdersRef` is reset first, so the orders are this derivation's and
      nothing else's — including no leftovers from a `derive_mutual` earlier in the file.

    Both refs are restored afterwards, even on failure, so calling this does not disturb pins a file
    installed for its own `derive_mutual`.

    Throws when the deriver did not actually search the root. The deriver skips any mode Lean already
    has an instance for (`instanceExistsFor`), so after a `derive_mutual` for the same root earlier in
    the file — or with a hand-written instance in scope — it records **no** orders, and the book comes
    back empty. Learning would then start from the interpreter's own default while reporting it as the
    compiled start, which is the confusion this module exists to remove. -/
def deriveChoice (root : SpecKey) (pins : PinnedOrders := []) : Elab.Command.CommandElabM DeriverChoice := do
  let savedPins ← pinnedOrdersRef.get
  let savedChosen ← chosenOrdersRef.get
  pinnedOrdersRef.set pins
  chosenOrdersRef.set []
  let memo ← IO.mkRef (∅ : Std.HashMap SpecKey MemoEntry)
  try
    Elab.Command.withScope (fun sc => { sc with opts := sc.opts.set `specimen.multiOutput true }) do
      let _ ← Elab.Command.liftTermElabM (deriveBestInductiveSchedule root memo)
    match (← memo.get)[root]? with
    | some (.done ind) =>
      if ind.alreadyExists then
        throwError "deriveChoice: {renderSpecKey root} already has an instance in scope, so the deriver \
          skipped it and settled no order for it; the book would silently be the interpreter's default. \
          Call this where no `derive_mutual` or instance for that mode is visible."
    | some (.failed msg) => throwError "deriveChoice: the deriver failed on {renderSpecKey root}: {msg}"
    | _ => throwError "deriveChoice: the deriver left no schedule for {renderSpecKey root}"
    -- The weights, under the same options the search just ran with: the scorer, weight function and
    -- modifier are all options, so a caller reproducing a real derivation sets them around this call
    -- with `set_option … in`, exactly as it would around `derive_mutual`.
    let bundle ← Elab.Command.liftTermElabM Scoring.getActiveScorerBundle
    let wf ← Elab.Command.liftCoreM Scoring.getActiveWeightFn
    let wm ← Elab.Command.liftCoreM Scoring.getActiveWeightModifier
    let memoNow ← memo.get
    let badness := memoNow.toList.flatMap (fun (k, e) =>
      match e with
      | .done ind => ind.ctorStats.map (fun (n, _, _, sc) =>
          (k, n, Scoring.scaleBadness (bundle.scoreBadness sc)))
      | _ => [])
    let weightFn : CtorWeightFn := match wm with
      | some m => fun c o srt b r z nb nr nrc => m.fn (wf.fn c o srt b r z nb nr nrc) c o srt b r z nb nr nrc
      | none => wf.fn
    return { orders := ← chosenOrdersRef.get, memo := memoNow, badness := badness, weightFn := weightFn }
  finally
    pinnedOrdersRef.set savedPins
    chosenOrdersRef.set savedChosen

/-- The deriver's generator choices for `root` as a `PlanBook`: the book generator learning should start
    from (see `DeriverChoice.generatorBook` for why checker and enumerator orders are left out). -/
def compiledBook (root : SpecKey) : Elab.Command.CommandElabM PlanBook :=
  return (← deriveChoice root).book

end Specimen.Interp

# Towards Automating Thorough Input Generation

A property-based tester wants to test its target *thoroughly*. When the target's
inputs are *sparse* — most are invalid or rejected, and the interesting behaviors
are reached by only a few valid inputs — thoroughness is hard to come by. This
note lays out two routes to it, and what each one needs to work:

1. **One generator that does it all** — derive a single constrained generator and
   *tune* it (reweight and restructure its choices) until its output distribution
   exercises the target thoroughly. This is the subject of most of the note.
2. **Two-part scenario generation** — first synthesize the *scenarios* worth
   testing, then generate a concrete input realizing each. This is genuinely
   different: you are not running one generator over and over, but planning a
   suite. The generation half is a (roughly backwards) constrained generator; the
   scenario-synthesis half is a separate problem, developed in the companion
   scenario-generation design and sketched in the last section here.

## Problem: Thorough input generation by automated tuning

A typical goal of a property-based tester is to _throughly_ test a target. We want to generate inputs that put the code through all of its paces, exposing failiures due to unforeseen interactions and missed corner cases.

This is challenging when the inputs to that target are _sparse_, meaning that most are either _invalid_ － the behavior is undefined on them － or _erroneous_ － the behavior is to reject the input as non-sensical, and thus not explore much of the target's interesting functionality.

Tools like Specimen aim to address the sparse input problem by automatically deriving constrained generators, for which we can be sure inputs satisfy a (sparse) predicate that defines what it means to be valid/non-erroneous. The Basalt library defines correctness conditions for generators, enabling GenAI can write the generators and prove their are correct (sound & complete with respect to a constraining predicate).

Unfortunately, just because Specimen or GenAI produce a generator that _may_ produce an input, the chances of doing so may not be sufficiently _likely_. This is a problem when some program behaviors are exercised by very few inputs. To thoroughly test those behaviors, we need to generate those inputs. 

The process of altering a generator to produce a better _distribution_ of inputs, i.e., those that test a target more thoroughly, quickly, and reliably, is called _tuning_ the generator. Our goal is to automate generator tuning.

### Examples

Here we define three examples to frame the discussion. For the first two, the validity predicate is _state based_, as many interesting examples are such (even ones that don't necessarily appear to be).

1. **Amazon Verified Permissions**. We want to synthesize a sequence of API calls to AVP that (mostly) do not fail. Then we can ensure that AVP behaves properly using model-based testing, and also that it satisfies properties like idempotence of certain operations.

    AVP is obviously state-based: We create a repository, add a policy to it, remove a policy from it, list the current policies, carry out an authorization request. Each of these is an API call and their validity is predicated on the current state of the repository. A generator for such API calls would track an abstraction of the state (e.g., what repositories are created, what policies are in them, etc.) to know what API calls could be generated next.

2. **Cedar**. We want to synthesize Cedar programs that are (mostly) well-typed. Then we can test theorems like type soundness, and we can do differential testing against Cedar implementations.

    Some sub-expressions are only valid when paired with others, which establish a precondition. Example
    ```
    principal has manager && principal.manager.level > 8
    ```
    The second sub-expression, `principal.manager...` is only legal if `principal` has `manager` as an attribute, and that fact is established by the first sub-expression. In the type system, the fact that `has` on an attribute has surely occurred is carried in the _capability_, which is essentially a state; the judgment form is `ɑ ; Γ ⊢ e : τ ; ε`, where `ɑ` is the input capability (collecting the attributes in `has` checks that have succeeded to this point), and `ε` is the output capability, which are checked attributes (still) conditionally valid, going forward. The type rule for `has C` will add `C` to `ε`. The type rule for `x.C` will confirm that `C` is in `ɑ`. 

    In short, the `ɑ` / `ε` are basically the _state_ abstracted by the type system. They allow a decision made by the generator early － to produce a `has` check on `C` － to inform a later decision － what `C` to use on the expression `x.C`.

3. **Strata**. We want to synthesize Strata Core programs that are (mostly) well typed. Then we can test theorems of the Strata codebase, similarly to Cedar. Strata is built around a core polymorhic lambda calculus parameterized by a set of types and operators, and extends out to support stateful operations (commands), functions, and procedures.

### Unlikely inputs

In principle, a generator produced by Specimen or proved correct in Basalt can cover all inputs. But in practice it fail to produce many interesting ones. Here are some examples why.

1. Consider Cedar. A generator cannot produce a well-typed expression `x.C` on its own; that expression needs to be generated within a _context_ `x has C && []` where the `x.C` plugs into the hole `[]`. The context can be more general than this, of course, e.g., it could be `x has C && x has D && []` or `(if true then x has C else false) && []` and so on. In essence, we are saying the context is one which induces `C ∈ ɑ` when typing `x has C`. Overall, it is relatively unlikely that you will generate such a context by chance and then, by chance, generate `x has C`. You need to decide to generate `&&` and then to generate `x has C` for the left sub-term and then generate `x.C` for the right. If we assume there is a uniformly random chance for each constructor -- `has`, `&&`, and `.` -- then it's much more likely we'll generate something else.

2. As another example, consider Strata terms under well typing, i.e., given a type `T`, generate a term with that type. Based on the App typing rule, to produce an expression of type `T` a generator would generate a type `T1`, a value `x` of type `T1`, and a function `f` of type `T1 -> T` and return `f x`. Functions include operators `op`, chosen from a dictionary which maps operators to their type `T1 -> T2 -> ... Tn`. Suppose `+` has type `Nat -> Nat -> Nat` and we want to generate a term of type `Nat` that uses `+`. Then the generator would have (a) decide to generate a function application, and then choose T1 to be `Nat` and generate a function of type `Nat -> Nat`; (b) choose to generate the `Nat -> Nat` by deciding to generate a function application again, in this case `T1` would again be `Nat` and the function type would be `Nat -> Nat -> Nat`; (c) choose to generate the `Nat -> Nat -> Nat` value by looking up an operator and getting `+`. This call then returns `+ x`, and then the outer call returns `(+ x) y` where `x` and `y` are the `Nat` values generated with the applications. In sum: A bunch of lucky choices have to be made here. And this is just for a two-argument function. For 4 or more aruguments it would be very unlikely to succeed.

## Tuning: Making unlikely inputs more likely (and vice versa)

General assumption: We will get run-time feedback that will feed into doing these things. But we could also imagine driving them with static analysis, e.g., per the [Boltzman tuning idea, marrying probabilistic programming and PBT](https://dl.acm.org/doi/full/10.1145/3763082), or even just having an LLM look at the code. Deferring this question to the end.

### Generator refinement: Changing weights

Generators often randomly choosing amongst a set of alternatives: For a Cedar expression of type `bool` you could generate a conjuction `X && Y`, a conditional `if e then X else Y`, a literal `true` or `false`, etc. (where `X` and `Y` are expressions that have type `bool`, generated recursively). These alternatives might have equal probability by default. During the tuning process we might decide to increase the weight for conjunctions and `has-`checks, which could increase the chances of `x has C && x.C` for example.

While weighting is surely part of the solution, it's not the whole solution. There are some downsides of only changing the weights of individual terms:

1. This might result in more failures overall, due to backtracking. We just increase the chances of ending up in an unlikely scenario. So we get a "better" distribution but fewer useful inputs.
2. This might result in a few more intersting terms while skewing the distribution toward "almost interesting" terms, e.g., `x has C && true` or `x has C`. These terms don't test what we really want to test, which is `x.C` when `C` is optional.

### Generator restructuring: Compound rules

When changing weights doesn't make a situation likely enough, or has the downsides mentioned above, we can adjust the _structure_ of the generator to make the situation more likely.

For example, suppose we decide that we are not generating enough `op` applications for Strata. It's not clear how we can address the problems mentioned above just by changing weights (which will also have negative downstream consequences). To make an `op` plus its arguments much more likely, we might just elect to generate them all together with a kind of compund rule: select an `op`, generate expressions with the types of its arguments as normal, and then call it － we are not relying on several "generate a function and apply" rules to land in our favor later. The generate-`op`-then-its-arguments approach was recommended by Palka. It is basically a _derived_ typing rule that adds no additional type-checking power, but directs generation more effectively. 

We might apply this pattern more generally. For example, suppose we decide to generate a record deref `x.C`, then to succeed we know we need to precede it in a conjunction with an expression `e` such that `C ∈ ɑ`. We could hardcode `e` to just be `x has C && ...` but this is a little unsatisfying. What if there is a bug that arises only in the expression `if true then x has C else false && x.C` but not in `x has C && x.C`? We are unlikely to find it. So we want to generate a _compatible context_ for a term, and then the term itself. A key question is how to get this general context reliably (more below).

### Application to Specimen, using runtime feedback

My sense is that to apply these two ideas two Specimen, we can take the following steps:

1. For frequency weights, we can configure the generator so that the weights can be specified from the outside. That allows an LLM agent to make observations and tune the weights. I have a feeling that this is possible now, but I'm not sure.

2. For structural composition, we can ask an LLM to synthesize new rules that should be admissable by the existing ones, but which improve the quality of generation. For example, in addition to rules for application and op-lookup, we synthesize an admissable rule like Palka's. Then we ask the LLM to prove that the admissable rule is indeed admissable, and act as normal.

A key question is what sort of signal does an agent need to leverage these tuning approaches. Let's assume that we will gather run-time information from test runs, based on instrumentation -- this is one reason, BTW, for Specimen to target Basalt generators, since they can be parameterized to include instrumentation and Plausible cannot. One potentially useful sort of generation is failures: When a checker fails which causes backtracking, log the construct the failure was in and the variable it was on. If we also instrument the constructor in which a variable was first generated, we can see that the creation site failed to produce a value that satisfied the checking site. That might be an opportunity for composition.

> As an aside: You could also imagine a special kind of backtracking in which a failed check backtracks directly to the generation site along with the failed constraint, which the generator can attempt to satisfy. I think this is difficult though because there may be other implicit constraints that were satisfied by checks in between that we don't necessarily know about. You'd need to gather per-variable successful checks along with the failed ones in order to re-generate properly. Then you also probably need some way to "replay" the same choices you made before, to get back to the failed check. Seems hard.

### The feedback loop

Both interventions — reweighting and rule-addition — are moves in a loop that
observes generation, decides what to change, and re-runs. It's worth naming the
loop's parts, because each has open design questions.

- **Observation.** What do we log from a run? Candidates, from cheap to rich:
  (a) *coverage* — which constructors of the target relation fired, and how often
  (a histogram); (b) *outcome shape* — of the inputs produced, how many were
  trivial vs. interesting (e.g. the "non-empty ⟹ contains-Redeem" invariant we
  already track in `Results.md`); (c) *backtracking events* — the
  `(constructor, variable, failed-check)` records described above, which point at
  *where* a path got stuck. Coverage tells you *what* is under-explored;
  backtracking tells you *why*. Only Basalt generators can carry this
  instrumentation, which is one reason to target them.

- **Inference.** Given observations, what do we change and how? The observation
  →action map is the hard part, and there are several plausible drivers:
  *statistical* (hill-climb weights to flatten a coverage histogram — cheap,
  local, and blind to structure); *heuristic* (a fixed rule like "a constructor
  with 0 coverage and repeated backtracking on variable `v` is a candidate for
  inlining/compound-rule around `v`"); or *LLM-driven* (hand the agent the
  coverage histogram, the backtracking log, and the relation source, and ask for
  a diagnosis plus a proposed intervention). These are not exclusive — statistics
  can pick weights while an LLM proposes rules.

- **Action.** The two levers differ in cost and reversibility. Reweighting is a
  cheap, continuous, fully-reversible edit to a config vector (see
  `Generator-config.md`). Rule-addition is a discrete, structural change that
  carries a proof obligation (the new rule must be admissible — see below) and
  cannot be undone by nudging a number. A loop should probably exhaust the cheap
  lever before reaching for the expensive one, but see the note below on why
  that's a cost ordering, not a strict hierarchy.

- **Reward / stopping.** When is the generator "tuned enough"? We need a target
  the loop optimizes toward. Flat constructor coverage is one proxy; distance
  from a Boltzmann-style target distribution over term *shapes* is another (see
  the aside on Boltzmann tuning below); "every scenario in a synthesized suite is
  realized at least once" is the criterion the scenario approach gives for free.
  Without a stopping condition the loop has no notion of done.

Two clarifications on how the levers relate. First, they **compose** cleanly —
you can reweight a generator that has had compound rules added, and adding a rule
introduces new choice points that themselves want weights. Second, it is *not*
clear that one **dominates** the other, so this is a cost ordering (try the cheap
lever first), not a strict hierarchy: reweighting cannot make a 0-coverage
constructor fire when the path to it is un-invertible (that's the whole point of
the inlining experiments), and rule-addition is overkill when a path is reachable
but merely under-sampled. They address different failure modes — "unreachable"
vs. "under-explored" — and a real tuner needs both.

> Aside — Boltzmann tuning. The [probabilistic-programming-meets-PBT line of
> work](https://dl.acm.org/doi/full/10.1145/3763082) gives a principled way to
> hit a *target distribution over term shapes* by solving for branch weights,
> rather than hand-tuning them. It is the right theory for the reweighting lever
> — but it tunes a distribution over shapes a generator can *already* produce; it
> says nothing about shapes the generator reaches with probability zero. So
> Boltzmann tuning is the mature form of the *weight* lever, and structural
> rule-addition is what you need when no weight vector suffices.

## A different approach: Scenario-based testing

We might imagine trying to be more goal directed. Rather than randomly picking an expression type, or API command, at each step, we could say, first:
1. "I want to generate an application with op" (for Strata)
2. "I want to generate a `x.C` (for Cedar)
3. "I want to generate a "delete policy P" (for AVP)

Then, second, we generate inputs to produce the necessary context that makes generating 1, 2, or 3 valid, and then generate that.

Thus testing becomes: Enumerate _scenarios_ you want to test (step 1), and then generate contexts for each scenario and run the tests (step 2).

This is basically what S3 HiFi does, where the scenarios are defined by a kind of predicate abstraction over the S3 state space, with especial attention paid to failure cases, and testing those are handled properly.

**Why this is not just "tune one generator harder."** The single-generator route
of the previous sections produces a *distribution* and samples it repeatedly; you
get thoroughness by making the interesting inputs likely and drawing enough
samples. Scenario testing changes the shape of the activity: you *enumerate* a
finite set of behaviorally-distinct situations, then produce one input per
situation. HiFi's headline result is exactly this contrast — systematic
enumeration deterministically covers in ~8 requests what random PBT covers
stochastically in ~3200. You are trading a distribution you sample for a suite
you construct. The two halves of that construction are quite different problems:

- **Second half — realize a scenario (mostly solved).** Given a chosen scenario,
  produce a concrete input that realizes it. This is a constrained generation
  problem, run roughly *backwards*: the scenario fixes a target (a state, or an
  enabled command, or a required judgment) and we generate a context reaching it.
  The mechanisms of the previous sections apply directly. For a scenario "test a
  call to `op`" in Strata, the context is satisfied by a Palka-style rule — I can
  call `op` once I have well-typed values for its arguments. For "test a `x.C`
  dereference" in Cedar, the context is a term with a hole that makes `x.C`
  well-typed. The context-generation machinery below is what does this half.

- **First half — synthesize the scenarios (the open problem).** Where does the
  scenario set come from? HiFi gets it from a human-authored predicate
  abstraction over the state space. The ambition is to *derive* it from the
  inductive specification: the constructors' premises are the features, the
  implications between premises are the state invariant `inv_Ω` that rules out
  spurious combinations, and the satisfying truth-assignments over features are
  the scenarios (partitioned into success vs. error cases). This note does not
  solve the first half — the companion **scenario-generation design** develops it
  as a four-phase pipeline (feature/scenario extraction, goal-directed planning,
  campaign organization by error count, validation), with a hand-written
  BoundedBuffer prototype. See that document for the details and its open
  questions (feature granularity, planner complexity, generation-by-execution vs.
  upfront generation, scaling, non-determinism).

The through-line of this whole note: **you want thorough testing, and you have
two routes to it** — one generator that you tune until its samples cover
everything, or the two-part scenario approach that constructs a covering suite
directly. They share the second-half machinery (constrained, backwards-ish
context generation); they differ in whether a scenario set is synthesized up
front.

## Context generation: the shared machinery

Both routes lean on the same capability, so it deserves its own treatment: given
a target we want to hit (a required judgment, an enabled command), produce a
*context* — a term with a hole — into which the target term can be plugged so the
whole thing is valid.

One way to view this is as a kind of _backwards_ generator. For the Cedar
example: instead of a generator that takes `ɑ`, `Γ`, `τ` and produces `e`, `ε`
such that `ɑ ; Γ ⊢ e : τ ; ε`, we want a generator that takes `ɑ`, `Γ`, `τ`, `ε`
and produces a context `E` such that the hole in `E` can be filled by a term `e`
with `ɑ ; Γ ⊢ e : τ ; ε`. For `x.C` the `Γ` says `x` has optional field `C` of
type `τ`, `ε` is empty, and `C ∈ ɑ`. We are giving *constraints* on the input to
this backwards generator, not the inputs themselves, so we'd have to synthesize
them from those constraints.

But it's not really a backwards generator, because we are producing a context
(which has a hole), not a term. The Palka rule is similar: to call `op`, generate
a context `E` that invokes `op` on its arguments, e.g. `E = [] 1 2` where
`op = +`.

**Is there a general way to derive this?** I think the promising framing is: a
context is itself an object of a *derived inductive relation*, and if we can
state that relation, Specimen derives its generator by the usual machinery. So
the question "can we generate contexts?" reduces to "can we *derive the context
relation* from the term relation?" Sketch, for a typing judgment
`WellTyped : Env → Expr → Ty → Prop`:

```lean
-- WTContext env E envₕ τₕ τ  ≜  E is a one-hole context such that, if the hole
-- is filled by any e with `WellTyped envₕ e τₕ`, then `WellTyped env E[e] τ`.
-- (envₕ, τₕ) are the *requirements the context imposes on its hole*.
inductive WTContext : Env → Ctx → Env → Ty → Ty → Prop where
| Hole  : WTContext env □ env τ τ                    -- the empty context
| ConjR : WellTyped env lhs Bool →                   -- lhs establishes capability
          WTContext (extend env lhs) (Expr.and lhs □) envₕ τₕ Bool
-- ...one such rule per position of the hole in each WellTyped constructor
```

The content of each `WTContext` constructor is mechanical from a `WellTyped`
constructor: pick which sub-expression is the hole, keep the *other* premises as
context obligations (`WellTyped env lhs Bool`), and thread the environment the way
the original rule does (so `x has C && []` correctly delivers `C ∈ ɑ` to the
hole). This is the same move as the step-inlining work, generalized: inlining
pulls a callee relation's constructors into a caller and threads a shared
variable; deriving `WTContext` "pulls the hole out" of `WellTyped` and threads the
environment to the hole. Two things make this more than a rename and are the real
work to validate:

1. **Multiple holes and depth.** `Hole` gives a depth-0 context; the recursive
   rules grow it. We likely want a size/depth bound (as with inlining's `k`) and,
   for realism, more than one hole (to reach `x has C && [] && []`). A one-hole
   relation is the place to start.
2. **Admissibility is automatic here.** For the *single-generator* route we add
   compound rules and must prove them admissible (every term the rule generates
   was already derivable). Here there is no separate obligation: `WTContext` is
   *defined* so that `WTContext env E envₕ τₕ τ` and `WellTyped envₕ e τₕ` imply
   `WellTyped env E[e] τ` — that implication is the derivation target, provable
   once, generically, over the shape of the derivation, rather than per generated
   term.

Concrete next experiment: hand-write `WTContext` for the `AttrGuardExperiment`'s
`WT` relation (its `chk`/`drf` are a stripped-down `has`/`x.C`), derive its
generator with Specimen, and check that it produces *diverse* guarding contexts
for a `drf`, not just the single `chk (sq k) □` pairing the fused experiment
already gets. Success = high `drf` rate *and* context diversity; that would show
the backwards/context half of both routes is derivable, not just hand-buildable.

## Appendix: prior work in this project

The ideas above are not starting from scratch — several pieces are already
built or designed. This appendix positions each within the note's framing so the
main text can stay at the level of intent.

- **Step inlining** ([Lookahead-experiment.md](./Lookahead-experiment.md)) is the
  worked-out form of the *structural rule-addition* lever, for the special case of
  a `Step`/`Trace` state-transition spec. A forward (0-lookahead) generator can
  fail to fire a command *at all* when its precondition was set up by an earlier
  step and can't be read back off the state; inlining `k+1` adjacent steps into
  one constructor moves the cross-step link inside the scheduler's joint-scheduling
  window, so a fresh variable is bound once and the link is *computed forward*
  rather than guessed-and-inverted. The vault and attr-guard experiments show the
  0 → ~320 / 0 → ~580 jumps this produces. This is exactly a mechanically-derived
  Palka-style compound rule — evidence that the "structural" lever is real and, at
  least for step relations, automatable. The `WTContext` sketch above is the
  generalization of this move from step relations to arbitrary judgments.

- **Culling provably-dead constructors** ([Results.md](./Results.md),
  `specimen.cullDeadCtors`) is the static-pruning half of inlining: inlining emits
  `bᵏ` constructors, most of them infeasible, and culling discharges "this
  constructor can never fire" as a `premises → False` goal handed to Lean's own
  automation (`simp_all`/`omega`/`decide`). Sound by construction (drop only what
  Lean proves dead), it is what keeps the structural lever from blowing up. In the
  feedback-loop terms above, this is not a tuning move an agent makes — it's a
  derivation-time optimization that makes the structural lever affordable.

- **Scenario generation** (the companion scenario-generation design, HiFi-derived)
  is the *first half* of the two-part route: deriving the scenario set (features
  from premises, `inv_Ω` from premise implications, scenarios as satisfying
  assignments, campaigns by error count) from the inductive spec, with a
  hand-written BoundedBuffer prototype. The note above deliberately does not
  duplicate it; it only connects the *second* half (realize-a-scenario = backwards
  context generation) to the single-generator machinery.

- **Steering** ([Steering-notes.md](./Steering-notes.md)) is the adjacent, still
  speculative question of *aiming* an already-adequate forward generator at a
  specific rare target — orthogonal to making it adequate. It argues (as the main
  text does) that control-planning and data-solving cannot be staged, only
  interleaved, and connects the reachability pruning of culling to goal-directed
  path search.

- **Generator configuration** ([Generator-config.md](./Generator-config.md)) is
  the plumbing the *reweighting* lever needs: externally-specified size bounds and
  sub-generator selection, in the Basalt style Specimen is expected to target.

### On implicit cross-command constraints

The `Issue`/`Redeem` vault is worth calling out as a case where the constraint
from an earlier command to a later one is *implicit* — the state does not record
what the later step will need. Recall the relation:

```lean
inductive VStep : Vault → VCmd → VResult → Vault → Prop where
| DoIssue  : ∀ t,   VStep none     (VCmd.Issue t)  VResult.IssueOk  (some t)
| DoRedeem : ∀ t k, t = sq k →
             VStep (some t) (VCmd.Redeem k) VResult.RedeemOk none
```

The state is `Option Nat`. It faithfully carries the ticket `t` from `Issue` to
`Redeem` — so in one sense the constraint *is* state-based. But the state tells
you nothing *useful* for generation: `Redeem` needs the *root* `k` with
`t = sq k`, and the state stores the square, from which the root cannot be read
back. The obligation that `t` be a perfect square is never stated at `Issue`
(where `t` is chosen); it is imposed only later, at `Redeem`, and by then the
value is committed. So the earlier command must satisfy a precondition it is never
told about — the link is implicit, discoverable only by looking across the step
boundary. This is precisely why 0-lookahead forward generation scores 0/1000
Redeems and why inlining (which puts both steps in one scope, binds a fresh `k`,
and computes `t = sq k` forward) is the fix. It is also the cleanest small example
of the general point that the state abstraction which makes a spec *look*
state-based can hide the constraint that actually governs generation.
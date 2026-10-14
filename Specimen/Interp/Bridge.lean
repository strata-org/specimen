import Specimen.Interp.Gen
import Specimen.ArbitrarySizedSuchThat

/-!
# Bridging typed Lean values and the interpreter's untyped `Val`

Schedules bottom out at things the interpreter cannot invent: an `Arbitrary Nat`, a `DecOpt` for
`x ≤ y`, a function like `List.length`. Those already exist in Lean, typed. This module carries them
across the boundary.

`ToVal`/`OfVal` convert between a Lean type and `Val`. `ToVal` is needed for anything the
interpreter must *consume from* Lean (a generated leaf value, a function result); `OfVal` for
anything it must *hand back to* Lean (a checker's arguments). Neither is needed to read results:
`Val` has `ToString` and `Repr`, so a sampling loop can print what it produced without any instance
at all.

Instances are provided for the base types and the usual containers. A user datatype needs a couple
of lines:

```lean
instance : ToVal Colour where
  toVal
    | .red   => .ctor ``Colour.red []
    | .green => .ctor ``Colour.green []
```

The `lift*`/`checker*`/`func*` families then turn typed things into the `ValGen`, `ValChecker`,
`ValProducer`, and `FuncTable` entries an `InterpEnv` wants.
-/

open Lean Plausible

namespace Specimen.Interp

/-- Converts a Lean value into the interpreter's untyped `Val`. -/
class ToVal (α : Type) where
  /-- The `Val` representing this value. Must agree with the constructor names and (value-level)
      argument order that schedules use, since patterns are matched against it structurally. -/
  toVal : α → Val

/-- Reads a Lean value back out of the interpreter's untyped `Val`. -/
class OfVal (α : Type) where
  /-- The value this `Val` represents, or a message explaining the mismatch. -/
  ofVal : Val → Except String α

export ToVal (toVal)
export OfVal (ofVal)

/-- Reports a `Val` that did not have the expected shape. -/
private def shapeError (expected : String) (v : Val) : Except String α :=
  .error s!"expected {expected}, got `{v}`"

instance : ToVal Val := ⟨id⟩
instance : OfVal Val := ⟨.ok⟩

instance : ToVal Nat := ⟨fun n => .lit (.natVal n)⟩
instance : OfVal Nat where
  ofVal v := match v.asNat? with
    | some n => .ok n
    | none => shapeError "a `Nat`" v

instance : ToVal Bool where
  toVal b := .ctor (if b then ``Bool.true else ``Bool.false) []
instance : OfVal Bool where
  ofVal
    | .ctor ``Bool.true [] => .ok true
    | .ctor ``Bool.false [] => .ok false
    | v => shapeError "a `Bool`" v

instance : ToVal String := ⟨fun s => .lit (.strVal s)⟩
instance : OfVal String where
  ofVal
    | .lit (.strVal s) => .ok s
    | v => shapeError "a `String`" v

instance : ToVal Int where
  toVal
    | .ofNat n => .ctor ``Int.ofNat [.lit (.natVal n)]
    | .negSucc n => .ctor ``Int.negSucc [.lit (.natVal n)]
instance : OfVal Int where
  ofVal
    | .ctor ``Int.ofNat [.lit (.natVal n)] => .ok (.ofNat n)
    | .ctor ``Int.negSucc [.lit (.natVal n)] => .ok (.negSucc n)
    | v => shapeError "an `Int`" v

instance : ToVal Char where
  toVal c := .ctor ``Char.ofNat [.lit (.natVal c.toNat)]
instance : OfVal Char where
  ofVal
    | .ctor ``Char.ofNat [.lit (.natVal n)] => .ok (Char.ofNat n)
    | v => shapeError "a `Char`" v

instance : ToVal Unit := ⟨fun _ => .ctor ``Unit.unit []⟩
instance : OfVal Unit where
  ofVal
    | .ctor ``Unit.unit [] => .ok ()
    | v => shapeError "`Unit`" v

instance [ToVal α] [ToVal β] : ToVal (α × β) where
  toVal p := .ctor ``Prod.mk [toVal p.1, toVal p.2]
instance [OfVal α] [OfVal β] : OfVal (α × β) where
  ofVal
    | .ctor ``Prod.mk [a, b] => do return (← ofVal a, ← ofVal b)
    | v => shapeError "a pair" v

instance [ToVal α] : ToVal (Option α) where
  toVal
    | none => .ctor ``Option.none []
    | some a => .ctor ``Option.some [toVal a]
instance [OfVal α] : OfVal (Option α) where
  ofVal
    | .ctor ``Option.none [] => .ok none
    | .ctor ``Option.some [a] => some <$> ofVal a
    | v => shapeError "an `Option`" v

instance [ToVal α] [ToVal β] : ToVal (Sum α β) where
  toVal
    | .inl a => .ctor ``Sum.inl [toVal a]
    | .inr b => .ctor ``Sum.inr [toVal b]
instance [OfVal α] [OfVal β] : OfVal (Sum α β) where
  ofVal
    | .ctor ``Sum.inl [a] => .inl <$> ofVal a
    | .ctor ``Sum.inr [b] => .inr <$> ofVal b
    | v => shapeError "a `Sum`" v

/-- `ToVal` for lists, as the `List.nil`/`List.cons` constructor tree schedules pattern-match on. -/
def toValList [ToVal α] : List α → Val
  | [] => .ctor ``List.nil []
  | a :: as => .ctor ``List.cons [toVal a, toValList as]

instance [ToVal α] : ToVal (List α) := ⟨toValList⟩

/-- `OfVal` for lists. -/
partial def ofValList [OfVal α] : Val → Except String (List α)
  | .ctor ``List.nil _ => .ok []
  | .ctor ``List.cons [h, t] => do return (← ofVal h) :: (← ofValList t)
  | v => shapeError "a `List`" v

instance [OfVal α] : OfVal (List α) := ⟨ofValList⟩

/-! ## Lifting generators -/

/-- Erases a typed generator's type, giving the `ValGen` an `Unconstrained` step needs. -/
def liftGen [ToVal α] (g : Gen α) : ValGen := toVal <$> g

/-- The `ValGen` for a type's `Arbitrary` instance. Like the emitted code, it reads its size from
    the ambient `Gen` size rather than from the schedule's budget. -/
def arbitraryGen (α : Type) [Arbitrary α] [ToVal α] : ValGen := liftGen (Arbitrary.arbitrary (α := α))

/-- The `ValEnum` for a type's `Enum` instance — `arbitraryGen`'s counterpart for enumerator schedules. -/
def enumGen (α : Type) [Enum α] [ToVal α] : ValEnum := toVal <$> ExceptT.lift (Enum.enum : Enumerator α)

/-! ## Lifting checkers

    A `ValChecker` receives the fuel the schedule allocated and the hypothesis' *value-level*
    arguments, in argument order — essentially what `DecOpt.decOpt` would see.

    The `checker`/`producer` families below read their arguments from the **end** of that list, so a
    type-class dictionary that survived `valueArgs` (`@LE.le Nat instLENat x y` keeps `instLENat`;
    see `Specimen.Interp.Value`) is ignored rather than mistaken for an argument. Lean orders
    implicit and instance-implicit binders before the explicit ones, so the trailing arguments are
    exactly the explicit ones. Use `checkerOfList` directly if you need every argument. -/

/-- A checker from a function on the whole argument list. Conversion failures become `[interp]`
    errors, so `InterpEnv.check`-style misconfiguration stays distinguishable from a false verdict. -/
def checkerOfList (f : List Val → Except String Bool) : ValChecker :=
  fun _ vals =>
    match f vals with
    | .ok b => .ok b
    | .error e => .error (interpError e)

/-- A checker from a fuel-aware function on the whole argument list, for three-valued checkers that
    can be inconclusive. -/
def checkerOfListFueled (f : Nat → List Val → Except String (Except GenError Bool)) : ValChecker :=
  fun fuel vals =>
    match f fuel vals with
    | .ok r => r
    | .error e => .error (interpError e)

/-! ### Checkers straight from a `DecOpt` instance

    `checker1`/`checker2`/`checker3` take a hand-written `Bool` function, which means every relation the
    interpreter checks needs its decision procedure written twice — once as the `DecOpt` instance the
    pipeline uses, once as a Lean function for the leaf. The two then drift, and the drift is invisible:
    `InterpEnv.correspondence` found **21** such gaps on Cedar, eleven of them relations with a perfectly
    good `DecOpt` instance and no leaf at all, so the interpreter was deriving a checker from the
    definition where the shipped generator calls the hand-written procedure. Measurements taken that way
    describe a different program.

    `DecOpt.decOpt : Nat → Except GenError Bool` is exactly `checkerOfListFueled`'s shape, three-valued
    result included, so the instance can *be* the leaf. -/

/-- A checker for a unary relation, taken from its `DecOpt` instance rather than a duplicate. -/
def checkerOfDecOpt1 [OfVal α] (P : α → Prop) [inst : ∀ a, DecOpt (P a)] : ValChecker :=
  checkerOfListFueled fun fuel vals =>
    match lastArgs 1 vals with
    | [a] => do return (inst (← ofVal a)).decOpt fuel
    | _ => .error s!"checker expected 1 argument, got {vals.length}"

/-- A checker for a binary relation, from its `DecOpt` instance. -/
def checkerOfDecOpt2 [OfVal α] [OfVal β] (P : α → β → Prop) [inst : ∀ a b, DecOpt (P a b)] :
    ValChecker :=
  checkerOfListFueled fun fuel vals =>
    match lastArgs 2 vals with
    | [a, b] => do return (inst (← ofVal a) (← ofVal b)).decOpt fuel
    | _ => .error s!"checker expected 2 arguments, got {vals.length}"

/-- A checker for a ternary relation, from its `DecOpt` instance. -/
def checkerOfDecOpt3 [OfVal α] [OfVal β] [OfVal γ] (P : α → β → γ → Prop)
    [inst : ∀ a b c, DecOpt (P a b c)] : ValChecker :=
  checkerOfListFueled fun fuel vals =>
    match lastArgs 3 vals with
    | [a, b, c] => do return (inst (← ofVal a) (← ofVal b) (← ofVal c)).decOpt fuel
    | _ => .error s!"checker expected 3 arguments, got {vals.length}"

/-- A checker for a unary decidable predicate, applied to the last value argument. -/
def checker1 [OfVal α] (p : α → Bool) : ValChecker :=
  checkerOfList fun vals =>
    match lastArgs 1 vals with
    | [a] => p <$> ofVal a
    | _ => .error s!"checker expected 1 argument, got {vals.length}"

/-- A checker for a binary decidable predicate, applied to the last two value arguments. -/
def checker2 [OfVal α] [OfVal β] (p : α → β → Bool) : ValChecker :=
  checkerOfList fun vals =>
    match lastArgs 2 vals with
    | [a, b] => do return p (← ofVal a) (← ofVal b)
    | _ => .error s!"checker expected 2 arguments, got {vals.length}"

/-- A checker for a ternary decidable predicate, applied to the last three value arguments. -/
def checker3 [OfVal α] [OfVal β] [OfVal γ] (p : α → β → γ → Bool) : ValChecker :=
  checkerOfList fun vals =>
    match lastArgs 3 vals with
    | [a, b, c] => do return p (← ofVal a) (← ofVal b) (← ofVal c)
    | _ => .error s!"checker expected 3 arguments, got {vals.length}"

/-- A checker for a unary `Prop`-valued predicate that is decidable, mirroring the built-in
    `[Decidable P] → DecOpt P` instance the compile-time pipeline uses. -/
def decidableChecker1 [OfVal α] (p : α → Prop) [DecidablePred p] : ValChecker :=
  checker1 (fun a => decide (p a))

/-- A checker for a binary `Prop`-valued predicate that is decidable. -/
def decidableChecker2 [OfVal α] [OfVal β] (p : α → β → Prop)
    [∀ a b, Decidable (p a b)] : ValChecker :=
  checker2 (fun a b => decide (p a b))

/-- A checker from a real `DecOpt` family — the way to reuse a *derived* checker, which is
    three-valued and fuel-sensitive. -/
def decOptChecker1 [OfVal α] (p : α → Prop) [inst : ∀ a, DecOpt (p a)] : ValChecker :=
  checkerOfListFueled fun fuel vals =>
    match lastArgs 1 vals with
    | [a] => do return DecOpt.decOpt (p (← ofVal a)) fuel
    | _ => .error s!"checker expected 1 argument, got {vals.length}"

/-- A binary `DecOpt` family. -/
def decOptChecker2 [OfVal α] [OfVal β] (p : α → β → Prop)
    [inst : ∀ a b, DecOpt (p a b)] : ValChecker :=
  checkerOfListFueled fun fuel vals =>
    match lastArgs 2 vals with
    | [a, b] => do return DecOpt.decOpt (p (← ofVal a) (← ofVal b)) fuel
    | _ => .error s!"checker expected 2 arguments, got {vals.length}"

/-! ## Lifting constrained producers

    A `ValProducer` receives `initSize`, `size`, and the relation's value-level *inputs* in
    argument order, and returns one value per output position in ascending order. Standing in for an
    `ArbitrarySizedSuchThat` instance, use the `size` argument — that is what the schedule
    allocated. -/

/-- A producer with no inputs and one output. -/
def producer0 [ToVal β] (f : Nat → Gen β) : ValProducer :=
  fun _ size _ => (fun b => [toVal b]) <$> f size

/-- A producer with one input and one output. -/
def producer1 [OfVal α] [ToVal β] (f : α → Nat → Gen β) : ValProducer :=
  fun _ size vals =>
    match lastArgs 1 vals with
    | [a] =>
      match ofVal a with
      | .ok a => (fun b => [toVal b]) <$> f a size
      | .error e => throwInterp e
    | _ => throwInterp s!"producer expected 1 input, got {vals.length}"

/-- A producer with two inputs and one output. -/
def producer2 [OfVal α₁] [OfVal α₂] [ToVal β] (f : α₁ → α₂ → Nat → Gen β) : ValProducer :=
  fun _ size vals =>
    match lastArgs 2 vals with
    | [a₁, a₂] =>
      match ofVal a₁, ofVal a₂ with
      | .ok a₁, .ok a₂ => (fun b => [toVal b]) <$> f a₁ a₂ size
      | .error e, _ | _, .error e => throwInterp e
    | _ => throwInterp s!"producer expected 2 inputs, got {vals.length}"

/-! ## Lifting functions -/

/-- A `FuncTable` entry for a nullary constant. -/
def constFunc [ToVal α] (a : α) : List Val → Except String Val :=
  fun _ => .ok (toVal a)

/-- A `FuncTable` entry for a unary function, applied to the last value argument.

    Last, not only: a reified application carries its type-class dictionaries, and not all of them can
    be dropped. `n * n` reifies as `HMul.hMul Nat Nat Nat (instHMul Nat instMulNat) n n`, so a
    `HMul.hMul` entry is handed three values — the opaque `instHMul` atom and the two operands. Lean
    orders implicit and instance-implicit binders first, so the trailing arguments are the explicit
    ones. Use `funcOfList` if you need every argument. -/
def func1 [OfVal α] [ToVal β] (f : α → β) : List Val → Except String Val := fun vals =>
  match lastArgs 1 vals with
  | [a] => (toVal ∘ f) <$> ofVal a
  | _ => .error s!"function expected 1 argument, got {vals.length}"

/-- A `FuncTable` entry for a binary function, applied to the last two value arguments. -/
def func2 [OfVal α] [OfVal β] [ToVal γ] (f : α → β → γ) : List Val → Except String Val := fun vals =>
  match lastArgs 2 vals with
  | [a, b] => do return toVal (f (← ofVal a) (← ofVal b))
  | _ => .error s!"function expected 2 arguments, got {vals.length}"

/-- A `FuncTable` entry for a ternary function, applied to the last three value arguments. -/
def func3 [OfVal α] [OfVal β] [OfVal γ] [ToVal δ] (f : α → β → γ → δ) :
    List Val → Except String Val := fun vals =>
  match lastArgs 3 vals with
  | [a, b, c] => do return toVal (f (← ofVal a) (← ofVal b) (← ofVal c))
  | _ => .error s!"function expected 3 arguments, got {vals.length}"

/-- A `FuncTable` entry that sees every argument, dictionaries included. -/
def funcOfList (f : List Val → Except String Val) : List Val → Except String Val := f

/-! ## Registration helpers

    Thin wrappers so an environment reads as a list of the leaves it provides. -/

namespace InterpEnv

/-- Registers a type's `Arbitrary` instance as the generator for every type with that head name. -/
def withArbitrary (env : InterpEnv) (tyName : Name) (α : Type) [Arbitrary α] [ToVal α] :
    InterpEnv :=
  env.addArbitrary tyName (arbitraryGen α)

/-- Registers a type's `Arbitrary` instance for one exact rendered type (e.g. `"List Nat"`). -/
def withArbitraryAt (env : InterpEnv) (renderedTy : String) (α : Type) [Arbitrary α] [ToVal α] :
    InterpEnv :=
  env.addArbitraryAt renderedTy (arbitraryGen α)

/-- Registers a type's `Enum` instance as the enumerator for every type with that head name.

    Needed as often as `withArbitrary`, and easy to overlook: an `Unconstrained` step in an
    **enumerator**-sort schedule consults `enums`/`enumsAt`, never `arbitrary`. So a closure derived with
    `deriveCheckers` — which brings up enumerator modes to answer the checkers — reports a missing leaf
    for a type whose `Arbitrary` is already registered, and `InterpEnv.check`'s hint says `addArbitrary`
    even when the mode asking is an enumerator. -/
def withEnum (env : InterpEnv) (tyName : Name) (α : Type) [Enum α] [ToVal α] : InterpEnv :=
  env.addEnum tyName (toVal <$> ExceptT.lift (Enum.enum : Enumerator α))

/-- Registers a type's `Enum` instance for one exact rendered type. -/
def withEnumAt (env : InterpEnv) (renderedTy : String) (α : Type) [Enum α] [ToVal α] : InterpEnv :=
  env.addEnumAt renderedTy (toVal <$> ExceptT.lift (Enum.enum : Enumerator α))

/-- Registers both directions for a type that has an `Arbitrary` and an `Enum`, which is what a closure
    needs when checkers (and hence enumerator modes) are derived alongside generators. -/
def withLeaf (env : InterpEnv) (tyName : Name) (α : Type) [Arbitrary α] [Enum α] [ToVal α] :
    InterpEnv :=
  (env.withArbitrary tyName α).withEnum tyName α

/-- Registers a binary decidable relation as a checker, the common case for side conditions like
    `x ≤ y`. The name must be the relation's *head constant* as it appears in schedules. -/
def withDecidable2 (env : InterpEnv) (relName : Name) [OfVal α] [OfVal β] (p : α → β → Prop)
    [∀ a b, Decidable (p a b)] : InterpEnv :=
  env.addChecker relName (decidableChecker2 p)

/-- Registers a unary decidable relation as a checker. -/
def withDecidable1 (env : InterpEnv) (relName : Name) [OfVal α] (p : α → Prop)
    [DecidablePred p] : InterpEnv :=
  env.addChecker relName (decidableChecker1 p)

/-- Registers a unary function. -/
def withFunc1 (env : InterpEnv) (fnName : Name) [OfVal α] [ToVal β] (f : α → β) : InterpEnv :=
  env.addFunc fnName (func1 f)

/-- Registers a **structure field accessor** as a projection on the `Val` directly.

    Worth having rather than reaching for `withFunc1`, because a projection needs no conversion at all.
    `withFunc1 ``TypeEnv.ets TypeEnv.ets` would demand `OfVal TypeEnv` *and* `ToVal EntitySchema`, and
    hence instances for every field of both — for a function that only picks an argument out of a
    constructor it was already handed. Here the `Val` arrives as `.ctor TypeEnv.mk [ets, acts, reqty]`
    and the answer is `args[0]`, whatever the field types are.

    `idx` is the field's position in declaration order, which is the order `ToVal` emits. A structure
    with implicit or instance fields shifts those positions, since `ToVal` emits every field. -/
def withProjection (env : InterpEnv) (fnName : Name) (idx : Nat) : InterpEnv :=
  env.addFunc fnName (fun vals =>
    match lastArgs 1 vals with
    | [.ctor c args] =>
      match args[idx]? with
      | some v => .ok v
      | none =>
        .error s!"projection '{fnName}' wanted field {idx} of `{c}`, which has \
          {args.length} field(s)"
    | [v] => .error s!"projection '{fnName}' expected a constructor, got `{v}`"
    | _ => .error s!"projection '{fnName}' expected 1 argument, got {vals.length}")

/-- Registers a function as the identity on its argument — `id`, and anything else that reifies into a
    premise while carrying no computation. -/
def withIdentity (env : InterpEnv) (fnName : Name) : InterpEnv :=
  env.addFunc fnName (fun vals =>
    match lastArgs 1 vals with
    | [v] => .ok v
    | _ => .error s!"'{fnName}' expected 1 argument, got {vals.length}")

/-- Registers a binary function. -/
def withFunc2 (env : InterpEnv) (fnName : Name) [OfVal α] [OfVal β] [ToVal γ] (f : α → β → γ) :
    InterpEnv :=
  env.addFunc fnName (func2 f)

/-- Registers a ternary function. -/
def withFunc3 (env : InterpEnv) (fnName : Name) [OfVal α] [OfVal β] [OfVal γ] [ToVal δ]
    (f : α → β → γ → δ) : InterpEnv :=
  env.addFunc fnName (func3 f)

/-- Registers a nullary constant, which is how schedules spell literals that are not `Nat`s or
    `String`s. -/
def withConst (env : InterpEnv) (constName : Name) [ToVal α] (a : α) : InterpEnv :=
  env.addFunc constName (constFunc a)

end InterpEnv

end Specimen.Interp

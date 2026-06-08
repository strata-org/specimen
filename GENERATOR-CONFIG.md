# Selecting and Configuring Generators

It is rarely the case that a generator for values of a particular type works for every application. Maybe booleans are the only exception! Thus an important question is: For a particular PBT application, how do we define, select, and configure the right generator? In this document we consider how to control the size of inputs, and how to select sub generators. We discuss some other issues at the end.

## Sizing inputs

Small inputs tend to be preferred to large inputs when testing, due to faster generation times, faster running times, no less fault finding power (due to the small world hypothesis), and easier debugging when faults are found. What’s the best way to specify input sizes when writing a generator? Two knobs: Explicit upper bounds, and probabilistic bounding.

### Explicit bounding

List length uniformly random. Structural termination.

```
def genListNatMax [Gen G] (max : Nat) : G (List Nat) := do
  let size ← RandomChoice.choose 0 max (by omega)
  go size.down
where
  go : (size : Nat) → G (List Nat)
    | 0 => pure []
    | Nat.succ size' => do
        let x ← Nat.arbitrary 
        let xs ← go size'
        return x :: xs
```

Lists with max := 10.

[0, 1, 0, 0]
[3, 1, 0, 1, 3, 1, 0]
[0]
[1, 2, 0, 0, 0, 1, 0, 0, 3, 4]
[2, 0, 1, 1, 4, 0, 0, 2, 1]
[0, 1, 2, 4, 3, 7, 0, 0, 3, 1]
[2, 1, 0, 0, 1, 0, 0, 0, 1]
[3, 2, 2, 0, 4, 1, 1]
[1, 0, 1]
[1, 3, 0, 0, 0, 6, 1]
[0, 2]
[4, 1, 0, 1, 0]
[1, 1, 1, 1, 0, 0]
[1, 0]
[1, 3, 0, 1, 0, 0, 3, 1, 1]
[0, 0, 1, 2, 0, 1, 0]
[0, 0, 1, 0, 0]
[2, 0, 0, 0, 0, 1, 1, 0, 1, 0]
[0, 2]
[0, 0, 0, 2, 0]

### Probabilistic bounding

No bound on the list, but probability distribution controlled by the bias. 

```
def genListNatProb [Gen G] (bias: Rat) : G (List Nat) := do
  if ← RandomChoice.coin bias then
    pure []
  else do
    let x ← Nat.arbitrary
    let xs ← genListNatProb bias
    return x :: xs
partial_fixpoint
```

Lists with bias to 1/4.

[2]
[2, 1, 1, 0, 1]
[2]
[]
[1]
[]
[0, 0, 0]
[2]
[]
[2, 0, 1, 2, 1, 5]
[1, 2, 0, 3, 0, 1]
[1, 2, 0, 1]
[3, 0, 0, 3, 2, 0, 2]
[2]
[4]
[1, 1, 1, 3, 0, 1]
[0, 0, 0]
[0, 0]
[4, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 1, 9, 0, 0, 2]
[1, 1, 1, 0, 1, 4]

### Combination

```
def genListNatProbMax [Gen G] (max : Nat) (bias: Rat) : G (List Nat) := do
  match max with
  | Nat.zero => pure []
  | Nat.succ max' =>
      if ← RandomChoice.coin bias then
        pure []
      else do
        let x ← Nat.arbitrary
        let xs ← genListNatProbMax max' bias
        return x :: xs
```

Lists with bias of 1/4 and a max length of 10

[0, 0, 0]
[0, 3, 1]
[1, 1, 1]
[2, 1, 0]
[0]
[0, 1, 0, 4, 0, 0, 0, 4, 0, 0]
[1, 1, 0, 0, 0, 0, 1]
[0]
[1]
[1, 2, 0, 1, 4, 1]
[2, 0]
[]
[4, 0, 0]
[4, 0, 0, 0]
[0, 2, 0, 1, 0, 1, 1]
[3, 0, 0, 0, 0, 1, 3, 0]
[0]
[]
[2, 2, 2]
[1, 0, 3, 4]

## Calling sub generators

In the examples above we call `Nat.arbitrary` for the elements of a list. This uses a 50/50 probability bound on generating numbers. What if we wanted to use a different generator for Nats, how would we specify it? 

(Embedded in these examples is a default answer to another question, which is how to specify the size of sub-generated values. We assume the size is shared between caller and callee but discuss other ideas below.)

### Sub-generator: Direct call

The easiest approach is to just hard-code a call to the generator.

```
def genNat [Gen G] (max : Nat) : G Nat :=
  ULift.down <$> RandomChoice.choose 0 max (by omega)
  
def genListNatMaxMax [Gen G] (max : Nat) : G (List Nat) := do
  let size ← RandomChoice.choose 0 max (by omega)
  go size.down
where
  go : (size : Nat) → G (List Nat)
    | 0 => pure []
    | Nat.succ size' => do
        let x ← genNat max
        let xs ← go size'
        return x :: xs
```

Doing this requires knowing the name of the generator you want to call (e.g., `genNat`) which may not be convenient. It also hurts polymorphism: A list generator that calls `genNat` can only generate lists of natural numbers, even though the structure of the generator shouldn’t change for other kinds of lists.

### Sub-generator: Typeclass

To solve the problems of locating generators and making them polymorphic, QuickChick selects nested generators by using typeclass resolution.

```
class Arb (T : Type) (G : Type → Type) [Gen G] where
  arb : Nat → G T

instance [Gen G] : Arb Nat G where
  arb := genNat
  
def genListNatMaxMax' [Gen G] [Arb T G] (max : Nat) : G (List T) := do
  let size ← RandomChoice.choose 0 max (by omega)
  go size.down
where
  go : (size : Nat) → G (List T)
    | 0 => pure []
    | Nat.succ size' => do
        let x ← Arb.arb max
        let xs ← go size'
        return x :: xs
```

Here, `genListNatMaxMax'` calls `Arb.arb max` rather than `genNat max`, with the benefit that it works for type `T` for which an `Arb T G` instance exists. 

Using typeclasses means we must create a uniform structure for generators, e.g., that they take a `max` parameter. This is potentially limiting — this structure needs to be the least common denominator for generators we might call. There is also an issue that while we have a level of indirection, there is still only one possible generator per type.

### Sub-generator: Parameter

We could pass the sub-generator to the generator, rather than calling it directly or resolving via typeclass:

```
def genListNatMaxMax'' [Gen G] (g: Nat → G T) (max : Nat) : G (List T) := do
  let size ← RandomChoice.choose 0 max (by omega)
  go size.down
where
  go : (size : Nat) → G (List T)
    | 0 => pure []
    | Nat.succ size' => do
        let x ← g max
        let xs ← go size'
        return x :: xs
```

The drawback with this approach is that the top-most generator must explicitly specify all of the generators of the generators it might call, transitively. But this also affords greater flexibility for the user. For example, we could default to typeclass resolution but allow specific parameters as desired.

```
def genListNatMaxMax'' [Gen G] [Arb T G] (max : Nat) (g : Nat → G T := Arb.arb) : G (List T) := do ...
```

## Managing the size of sub-generated values

However we decide which sub generator to call, how should we decide how to specify the size to the sub generated values. In the examples above, we pass along `max`, which is the initial size passed to the list generator, which is then passed along to the list-element generator. What other options do we have?

## Specifying a *distribution* of values

The size parameter is capturing one aspect of the *distribution* of values that a generator produces. The bias parameter mentioned in [Probabilistic bounding](https://quip-amazon.com/6bgmAib1ARfR#temp:C:YMJ08b4c229332248979671b45e3) makes very large items unlikely, but not impossible. How can we adjust the distribution?

The paper [Tuning Random Generators](https://arxiv.org/pdf/2508.14394) looks at using ML inference to do this. It basically takes generators in which sub-generators are called directly (or inlined in the parent, maybe) and then does ML inference to tune bias parameters against an objective function. I didn’t 

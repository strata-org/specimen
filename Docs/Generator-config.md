# Selecting and Configuring Generators

It is rarely the case that a generator for values of a particular type works for every application. Maybe booleans are the only exception! Thus an important question is: For a particular PBT application, how do we define, select, and configure the right generator? In this document we consider how to control the size of inputs, and how to select sub generators. We discuss some other issues at the end.

## Sizing inputs

A common configuration paramater for generators is a preferred _size_. Intuitively, small inputs are preferred for their faster generation times, faster running times, and easier debugging when faults are found. Large inputs might be better when bugs require executing many distinct code paths, and one large but diverse input might be effectively the same as several small ones. Usually the choice is left up to the user, who best knows their application. But how should that choice be expressed? There are two common knobs: Explicit upper bounds, and probabilistic bounds.

### Explicit bounds

The code examples here and throughout are written in [Basalt](https://github.com/hgoldstein95/basalt/), anticipating that Specimen will eventually target it. 

Here is a generator in which the list length is specified, and chosen uniformly at random.

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

Here is an example in which there is no upper bound on a list's length, but the probability distribution of length controlled by a given bias. 

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

We can create an upper bound on length, while using a bias to control the distribution.

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

Embedded in these examples is a default answer to another question, which is how to specify the size of sub-generated values. We assume the size given to the outer generator (here: `max`) is given to the sub-generators too. We discuss this choice separately in the next section.

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

## Managing the size and distribution of sub-generated values

However we decide which sub generator to call, what configuration parameters should we pass to that call (and indeed, to the parent call originally) to control the size and distribution of generated values?

### Controlling size

In the examples above, we pass along `max` to the list generator as the initial size. Its value is decremented while generating the list, but the unchanged `max` is passed to calls to the list-element generator. This matches the approach of Specimen, where the outer (global) size is called `initSize` and the inner (local) one is called `size`. In Specimen, the inner one bounds termination, and the outer one specifies policy.

While this approach is not bad, it has several issues:

1. The same size may not make sense for every generator. For example, I might want short lists containing potentially large numbers in some cases.

2. The same size may not make sense for every instance of the same generator. For example, if I am generating pairs of numbers and trees of numbers, I might want numbers in the pair to be potentially large but those in the trees to be mostly small.

3. Having to choose the size at all may be difficult: Users may not wish to guess what size makes sense for their application, and would prefer the system dynamically discover a reasonable size.

Note that the use of size to ensure termination (as a kind of "fuel") is not strictly necessary. Basalt's `partial_fixpoint` eliminates the need for fuel; see `Docs/Specimen-Basalt-port.md` for more about this. Thus we should really be thinking of sizing with respect to effectiveness.

### Controlling the distribution

The size parameter is capturing one aspect of the *distribution* of values that a generator produces. 

The bias parameter mentioned in the **Probabilistic bounding** section makes very large items unlikely, but not impossible. How can we adjust the distribution? The paper [Tuning Random Generators](https://arxiv.org/pdf/2508.14394) looks at using ML inference to do this. It basically takes generators in which sub-generators are inlined in the parent and then does ML inference to tune bias parameters against an objective function. The main objective function of interest is "maximum entropy" up to a size bound for the overall objects. This seems useful!

One of the benefits of [Tyche](https://andrewhead.info/assets/pdf/tyche.pdf) is that it allows you to visualize the distribution of generated inputs from your generator, according to metrics you care about. Using that visualization you can tune the generator by hand, or ask an LLM to do it (or help). There are some simple failure modes that Tyche can quickly identify:

1. Generating too many constants or default values
2. Generating too many duplicate values
4. Generating too many invalid (discarded) values
3. Not generating certain kinds of inputs very often (e.g., abstract syntax trees with calls to multi-argument functions when generating lambda-calculus terms)

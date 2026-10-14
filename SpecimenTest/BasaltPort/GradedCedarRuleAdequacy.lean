import SpecimenTest.BasaltPort.GradedRuleAdequacy

/-!
# Real Cedar relations in the `RuleShape.Body` framework

`SpecimenTest/BasaltPort/GradedRuleAdequacy.lean` proves adequacy of a graded enumeration once, over
rules-as-data, and instantiates it at STLC's `typing`. This file instantiates the *same* generic
theorem at four relations lifted from Cedar's live relational typing spec,
`cedar-lean/CedarGen/Relational/TypeOfLean.lean`, chosen to cover both halves of `Body`.

**Leaf premises only (`aux`, no `call`) — §3–§7:**

* `ValidDifferentEntityType` (line 165 there) — the warm-up: 2 constructors, each one producer
  premise, one auxiliary output and one `≠` check.
* `HasAttrInRecord` (line 227 there) — 4 constructors, an auxiliary output in every constructor, a
  genuine **negative** premise (`¬ CapAttrMem`), a `Bool` input that prunes constructors, and two
  constructors with *identical* conclusions.

**Recursive premises (`call`) — §8–§9:**

* `AllLub` (line 390 there) — the smallest Cedar relation that genuinely recurses, and the one whose
  recursive premise's *index* is built from a preceding auxiliary premise's output
  (`Lub acc hd lubTy → AllLub lubTy tl result`). One relation, so no sum encoding: this isolates
  `Body.call`. §8b runs it.
* `Lub` / `LubQualified` / `LubRecord` (lines 70–90 there) — a real **mutual family** whose three
  members produce three different types, encoded with one `RuleSet` over
  `ι := ι₁ ⊕ ι₂ ⊕ ι₃`, `α := α₁ ⊕ α₂ ⊕ α₃` so `call` can cross between members. §9b runs it, §10
  itemises what the encoding costs.

## Transcription, and where it is weak

Cedar's Lean package (`cedar-spec/cedar-lean`) *depends on* Specimen, and the `RuleShape` framework
lives in Specimen's test library, so importing real Cedar here would make the dependency circular. The
relations are **transcribed** instead. That transcription is the weak link, and it is deliberately
minimised in two ways:

1. Every Cedar type that the relations do not *inspect* is left as a type **variable**: `Attr`,
   `Xp` (Cedar's `Expr`), `Ty` (Cedar's `CedarType`), `ET` (`EntityType`), `Ent`
   (`EntitySchemaEntry`), `Act` (`ActionSchemaEntry`). So nothing below depends on what Cedar's
   `Expr` or `CedarType` actually are; instantiating `Ty := CedarType`, `ttTy := .bool .tt`,
   `anyTy := .bool .anyBool` recovers the Cedar relation on the nose.
2. The types the relations *do* inspect — `Map`, `Qualified`, `Key`, `EntityUID` — are copied
   constructor-for-constructor from `Cedar/Data/Map.lean`, `Cedar/Validation/Types.lean`,
   `Cedar/Validation/Typechecker.lean` and `Cedar/Spec/Value.lean`.

The one place the transcription *alters* the source text is `found_in_caps`, where Cedar writes
`MapContains (id a) qty rty`. `id a` is a scheduling annotation (it stops Specimen re-producing `a`
from `rty`); it is `a` definitionally and carries no logical content, so it is dropped. The
scheduling intent is honoured explicitly instead: the body binds `a` from `CapAttrMem` and the
`MapContains` premise is given a producer for `qty` *only*.
-/

open Basalt RuleShape

namespace CedarRule

/-! ## §1 The Cedar fragment, transcribed -/

/-- `Cedar/Data/Map.lean`: a map is a raw association list. Nothing below assumes it is sorted or
duplicate-free — Cedar's `Map.WellFormed` says that, and the relational spec never mentions it. -/
inductive Map (α β : Type) where
  | mk (kvs : List (α × β))

namespace Map
/-- The underlying association list. -/
def kvs {α β : Type} : Map α β → List (α × β) | .mk l => l
@[simp] theorem kvs_mk {α β : Type} (l : List (α × β)) : (Map.mk l).kvs = l := rfl
end Map

/-- `Cedar/Spec/Value.lean`. -/
structure EntityUID (ET : Type) where
  ty : ET
  eid : String

/-- `Cedar/Validation/Types.lean`; `QualifiedType := Qualified CedarType`. -/
inductive Qualified (α : Type) where
  | optional (a : α)
  | required (a : α)
  deriving Repr, DecidableEq

/-- `Cedar/Validation/Typechecker.lean`. -/
inductive Key (Attr Xp : Type) where
  | attr (a : Attr)
  | tag (x : Xp)
  deriving Repr, DecidableEq

/-- `Cedar/Validation/Typechecker.lean`. -/
abbrev Capabilities (Attr Xp : Type) := List (Xp × Key Attr Xp)
/-- `Cedar/Validation/Types.lean`. -/
abbrev RecordType (Attr Ty : Type) := Map Attr (Qualified Ty)
/-- `Cedar/Validation/Types.lean`. -/
abbrev EntitySchema (ET Ent : Type) := Map ET Ent
/-- `Cedar/Validation/Types.lean`. -/
abbrev ActionSchema (ET Act : Type) := Map (EntityUID ET) Act

/-- `TypeOfLean.lean:119`. -/
inductive MapContains {α β : Type} : α → β → Map α β → Prop where
  | here : ∀ k v rest, MapContains k v (.mk ((k, v) :: rest))
  | there : ∀ k v k' v' rest, MapContains k v (.mk rest) → MapContains k v (.mk ((k', v') :: rest))

/-- `TypeOfLean.lean:131`. Note this is *not* plain membership: skipping a cell requires the cell's
key to differ, so the relation says "the first cell keyed `⟨a,b⟩` holds `va`". -/
inductive MapContainsPairKey {ET Act : Type} :
    ET → String → Act → ActionSchema ET Act → Prop where
  | here : ∀ a b va m, MapContainsPairKey a b va (Map.mk ((⟨a, b⟩, va) :: m))
  | nextA : ∀ a b va a' b' v' m, a ≠ a' → MapContainsPairKey a b va (Map.mk m) →
      MapContainsPairKey a b va (Map.mk ((⟨a', b'⟩, v') :: m))
  | nextB : ∀ a b va a' b' v' m, b ≠ b' → MapContainsPairKey a b va (Map.mk m) →
      MapContainsPairKey a b va (Map.mk ((⟨a', b'⟩, v') :: m))

/-- `TypeOfLean.lean:192`. -/
inductive CapAttrMem {Attr Xp : Type} : Xp → Attr → Capabilities Attr Xp → Prop where
  | here : ∀ x a rest, CapAttrMem x a ((x, .attr a) :: rest)
  | there : ∀ x a x' k' rest, CapAttrMem x a rest → CapAttrMem x a ((x', k') :: rest)

/-- `TypeOfLean.lean:165`, verbatim. Mode: inputs `{other, ets, acts}`, output `{ety}`. -/
inductive ValidDifferentEntityType {ET Ent Act : Type} :
    ET → ET → EntitySchema ET Ent → ActionSchema ET Act → Prop where
  | inSchema : ∀ other ety entry ets acts,
      MapContains ety entry ets → ety ≠ other →
      ValidDifferentEntityType other ety ets acts
  | isAction : ∀ other ety eid entry ets acts,
      MapContainsPairKey ety eid entry acts → ety ≠ other →
      ValidDifferentEntityType other ety ets acts

/-- `TypeOfLean.lean:227`, verbatim modulo `id a ↦ a` and `.bool .tt ↦ ttTy`,
`.bool .anyBool ↦ anyTy`. Mode: inputs `{rty, x, c, knownToExist}`, outputs `{a, outTy, outCaps}`. -/
inductive HasAttrInRecord {Attr Xp Ty : Type} (ttTy anyTy : Ty) :
    RecordType Attr Ty → Xp → Attr → Capabilities Attr Xp → Bool → Ty →
    Capabilities Attr Xp → Prop where
  | found_in_caps : ∀ rty x a c knownToExist qty,
      CapAttrMem x a c → MapContains a qty rty →
      HasAttrInRecord ttTy anyTy rty x a c knownToExist ttTy []
  | found_required_known : ∀ rty x a c ty,
      MapContains a (.required ty) rty →
      HasAttrInRecord ttTy anyTy rty x a c true ttTy []
  | found_not_known : ∀ rty x a c qty,
      MapContains a qty rty → ¬ CapAttrMem x a c →
      HasAttrInRecord ttTy anyTy rty x a c false anyTy [(x, .attr a)]
  | found_optional_known : ∀ rty x a c ty,
      MapContains a (.optional ty) rty → ¬ CapAttrMem x a c →
      HasAttrInRecord ttTy anyTy rty x a c true anyTy [(x, .attr a)]

/-! ## §2 The closures, as executable list walks

Each of the four premise relations above is a walk over a *finite* structure: `Map` is an association
list, `Capabilities` is a list. This is the whole reason Cedar's leaves behave differently from
STLC's: the producer is a single finite list, independent of the level, so it satisfies not merely
`Covers` but `Unsized` — and hence may be graded `.flat`. §6 records why that matters. -/

variable {α β ET Ent Act Attr Xp Ty : Type}

theorem MapContains.iff_mem (k : α) (v : β) (m : Map α β) :
    MapContains k v m ↔ (k, v) ∈ m.kvs := by
  obtain ⟨l⟩ := m
  induction l with
  | nil => simp only [Map.kvs_mk, List.not_mem_nil, iff_false]; intro h; cases h
  | cons p l ih =>
      obtain ⟨k', v'⟩ := p
      simp only [Map.kvs_mk, List.mem_cons, Prod.mk.injEq] at ih ⊢
      constructor
      · intro h
        cases h with
        | here => exact Or.inl ⟨rfl, rfl⟩
        | there _ _ _ h => exact Or.inr (ih.mp h)
      · intro h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact .here _ _ _
        · exact .there _ _ _ _ _ (ih.mpr h)

theorem CapAttrMem.iff_mem (x : Xp) (a : Attr) (c : Capabilities Attr Xp) :
    CapAttrMem x a c ↔ (x, Key.attr a) ∈ c := by
  induction c with
  | nil => simp only [List.not_mem_nil, iff_false]; intro h; cases h
  | cons p c ih =>
      obtain ⟨x', k'⟩ := p
      simp only [List.mem_cons, Prod.mk.injEq] at ih ⊢
      constructor
      · intro h
        cases h with
        | here => exact Or.inl ⟨rfl, rfl⟩
        | there _ _ _ h => exact Or.inr (ih.mp h)
      · intro h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact .here _ _ _
        · exact .there _ _ _ _ _ (ih.mpr h)

/-- The first-occurrence walk that `MapContainsPairKey` really denotes: emit each cell, then drop
from the tail's walk anything whose key the head already claimed. -/
def pairKeyList [DecidableEq ET] : List (EntityUID ET × Act) → List (ET × String × Act)
  | [] => []
  | (uid, va) :: rest =>
      (uid.ty, uid.eid, va) ::
        (pairKeyList rest).filter (fun t => decide (t.1 ≠ uid.ty ∨ t.2.1 ≠ uid.eid))

theorem MapContainsPairKey.iff_mem [DecidableEq ET] (a : ET) (b : String) (va : Act)
    (l : List (EntityUID ET × Act)) :
    MapContainsPairKey a b va (Map.mk l) ↔ (a, b, va) ∈ pairKeyList l := by
  induction l with
  | nil => simp only [pairKeyList, List.not_mem_nil, iff_false]; intro h; cases h
  | cons p l ih =>
      obtain ⟨⟨ty, eid⟩, v'⟩ := p
      simp only [pairKeyList, List.mem_cons, List.mem_filter, Prod.mk.injEq,
        decide_eq_true_eq] at ih ⊢
      constructor
      · intro h
        cases h with
        | here => exact Or.inl ⟨rfl, rfl, rfl⟩
        | nextA _ _ _ _ hne h => exact Or.inr ⟨ih.mp h, Or.inl hne⟩
        | nextB _ _ _ _ hne h => exact Or.inr ⟨ih.mp h, Or.inr hne⟩
      · intro h
        rcases h with ⟨rfl, rfl, rfl⟩ | ⟨h, hne⟩
        · exact .here _ _ _ _
        · rcases hne with hne | hne
          · exact .nextA _ _ _ _ _ _ _ hne (ih.mpr h)
          · exact .nextB _ _ _ _ _ _ _ hne (ih.mpr h)

/-- The decision procedure `TypeOfLean.lean:210` supplies as `DecOpt (CapAttrMem x a c)`, which is
`.ok (c.any …)` — always conclusive. -/
def capAttrMemB [DecidableEq Attr] [DecidableEq Xp]
    (x : Xp) (a : Attr) (c : Capabilities Attr Xp) : Bool :=
  c.any (fun p => decide (p.1 = x ∧ p.2 = Key.attr a))

theorem capAttrMemB_iff [DecidableEq Attr] [DecidableEq Xp]
    (x : Xp) (a : Attr) (c : Capabilities Attr Xp) :
    capAttrMemB x a c = true ↔ CapAttrMem x a c := by
  rw [CapAttrMem.iff_mem]
  simp only [capAttrMemB, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    obtain ⟨p1, p2⟩ := p
    cases h1; cases h2; exact hp
  · intro h; exact ⟨(x, Key.attr a), h, rfl, rfl⟩


/-! ## §3 Warm-up: `ValidDifferentEntityType` as `Body` data

Two constructors; each is one producer premise (which binds *both* the output `ety` and a discarded
auxiliary output — `entry`, resp. `eid`/`entry`), one `≠` check, one conclusion. So the body shape is
`aux → check → ret` twice, and no `call` appears: the relation is not recursive. -/

namespace VDET

/-- Inputs of `ValidDifferentEntityType`: `other`, the entity schema, the action schema. -/
abbrev VIx (ET Ent Act : Type) := ET × EntitySchema ET Ent × ActionSchema ET Act

variable {ET Ent Act : Type}

/-- The producer for `MapContains ety entry ets`: the schema's association list, *level-independent*
because the schema is finite. -/
def schemaEnum (ets : EntitySchema ET Ent) : Nat → Lv (ET × Ent) := constP <| fun _ => ets.kvs

theorem sound_schemaEnum (ets : EntitySchema ET Ent) :
    Sound (schemaEnum ets) (fun p => MapContains p.1 p.2 ets) := by
  unfold schemaEnum
  exact sound_constP fun _ p hp => (MapContains.iff_mem p.1 p.2 ets).mpr hp

/-- **`Unsized`, not merely `Covers`.** The finite-leaf phenomenon: unlike STLC's `typeEnum`, this
producer offers every admissible value at *every* level, so `.flat` is legitimate here.

The budget quantifier in `Unsized` collapses (`unsized_constP`) because the producer ignores the
budget: there is no budget at which a finite `Map` walk offers less. -/
theorem unsized_schemaEnum (ets : EntitySchema ET Ent) :
    Unsized (schemaEnum ets) (fun p => MapContains p.1 p.2 ets) := by
  unfold schemaEnum
  exact unsized_constP fun p hp _ => (MapContains.iff_mem p.1 p.2 ets).mp hp

/-- `MonoL` is free for a budget-independent producer. -/
theorem monoL_schemaEnum (ets : EntitySchema ET Ent) : MonoL (schemaEnum ets) :=
  monoL_constP _

/-- The producer for `MapContainsPairKey ety eid entry acts`. -/
def actionEnum [DecidableEq ET] (acts : ActionSchema ET Act) : Nat → Lv (ET × String × Act) := constP <|
  fun _ => pairKeyList acts.kvs

theorem sound_actionEnum [DecidableEq ET] (acts : ActionSchema ET Act) :
    Sound (actionEnum acts) (fun t => MapContainsPairKey t.1 t.2.1 t.2.2 acts) := by
  obtain ⟨l⟩ := acts
  unfold actionEnum
  exact sound_constP fun _ t ht => (MapContainsPairKey.iff_mem t.1 t.2.1 t.2.2 l).mpr ht

theorem unsized_actionEnum [DecidableEq ET] (acts : ActionSchema ET Act) :
    Unsized (actionEnum acts) (fun t => MapContainsPairKey t.1 t.2.1 t.2.2 acts) := by
  obtain ⟨l⟩ := acts
  unfold actionEnum
  exact unsized_constP fun t ht _ => (MapContainsPairKey.iff_mem t.1 t.2.1 t.2.2 l).mp ht

theorem monoL_actionEnum [DecidableEq ET] (acts : ActionSchema ET Act) :
    MonoL (actionEnum acts) := monoL_constP _

/-- The `≠` premise's Kleene verdict: decisive, so `V.inconclusive` never arises. -/
theorem neqVerdict [DecidableEq ET] (a b : ET) :
    (if a = b then V.no else V.yes) ≠ V.no ↔ a ≠ b := by
  by_cases h : a = b <;> simp [h]

/-- `inSchema`. -/
def vdSchema [DecidableEq ET] : VIx ET Ent Act → Body (VIx ET Ent Act) ET
  | (other, ets, _) =>
      .aux .flat (schemaEnum ets) (fun p => MapContains p.1 p.2 ets) fun p =>
        .check (if p.1 = other then V.no else V.yes) (p.1 ≠ other) (.ret p.1)

/-- `isAction`. -/
def vdAction [DecidableEq ET] : VIx ET Ent Act → Body (VIx ET Ent Act) ET
  | (other, _, acts) =>
      .aux .flat (actionEnum acts) (fun t => MapContainsPairKey t.1 t.2.1 t.2.2 acts) fun t =>
        .check (if t.1 = other then V.no else V.yes) (t.1 ≠ other) (.ret t.1)

def vdRules [DecidableEq ET] : RuleSet (VIx ET Ent Act) ET := fun i => [vdSchema i, vdAction i]

/-- The relation, re-indexed the way the enumeration is. -/
def VR : VIx ET Ent Act → ET → Prop := fun i ety => ValidDifferentEntityType i.1 ety i.2.1 i.2.2

theorem hvalid [DecidableEq ET] :
    ∀ i, ∀ b ∈ vdRules (ET := ET) (Ent := Ent) (Act := Act) i, ∀ ety, HoldsR VR b ety → VR i ety := by
  intro ⟨other, ets, acts⟩ b hb ety h
  simp only [vdRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [vdSchema, HoldsR] at h
    obtain ⟨p, hmem, hne, rfl⟩ := h
    exact ValidDifferentEntityType.inSchema other p.1 p.2 ets acts hmem hne
  · simp only [vdAction, HoldsR] at h
    obtain ⟨t, hmem, hne, rfl⟩ := h
    exact ValidDifferentEntityType.isAction other t.1 t.2.1 t.2.2 ets acts hmem hne

theorem hgen [DecidableEq ET] :
    ∀ (i : VIx ET Ent Act) (ety : ET), VR i ety → Derives vdRules i ety := by
  intro ⟨other, ets, acts⟩ ety h
  replace h : ValidDifferentEntityType other ety ets acts := h
  cases h with
  | inSchema entry _ _ hmem hne =>
      refine Derives.intro (b := vdSchema (other, ets, acts)) (by simp [vdRules]) ?_
      exact Holds.aux (b := (ety, entry)) hmem (.check hne (.ret _))
  | isAction eid entry _ _ hmem hne =>
      refine Derives.intro (b := vdAction (other, ets, acts)) (by simp [vdRules]) ?_
      exact Holds.aux (b := (ety, eid, entry)) hmem (.check hne (.ret _))

theorem hsound [DecidableEq ET] :
    ∀ i, ∀ b ∈ vdRules (ET := ET) (Ent := Ent) (Act := Act) i, BodySound b := by
  intro ⟨other, ets, acts⟩ b hb
  simp only [vdRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨sound_schemaEnum ets, fun p => ⟨fun hv => (neqVerdict p.1 other).mp hv, trivial⟩⟩
  · exact ⟨sound_actionEnum acts, fun t => ⟨fun hv => (neqVerdict t.1 other).mp hv, trivial⟩⟩

theorem hcomplete [DecidableEq ET] :
    ∀ i, ∀ b ∈ vdRules (ET := ET) (Ent := Ent) (Act := Act) i, BodyComplete b := by
  intro ⟨other, ets, acts⟩ b hb
  simp only [vdRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨monoL_schemaEnum ets, unsized_schemaEnum ets,
      fun p => ⟨fun hne => (neqVerdict p.1 other).mpr hne, trivial⟩⟩
  · exact ⟨monoL_actionEnum acts, unsized_actionEnum acts,
      fun t => ⟨fun hne => (neqVerdict t.1 other).mpr hne, trivial⟩⟩

/-- **Adequacy for Cedar's `ValidDifferentEntityType`**, as an instance of the generic theorem: no
induction on levels, no induction on the relation beyond the one `cases` in `hgen`. -/
theorem vdet_adequate [DecidableEq ET] (other ety : ET)
    (ets : EntitySchema ET Ent) (acts : ActionSchema ET Act) :
    ValidDifferentEntityType other ety ets acts ↔
      ∃ L l n, enum vdRules L l (other, ets, acts) n ety :=
  adequate hsound hcomplete hvalid hgen (other, ets, acts) ety

/-- …and for the enumeration that runs. -/
theorem vdet_mem_adequate [DecidableEq ET] (other ety : ET)
    (ets : EntitySchema ET Ent) (acts : ActionSchema ET Act) :
    ValidDifferentEntityType other ety ets acts ↔
      ∃ L l n, ety ∈ enumL vdRules L l (other, ets, acts) n :=
  adequateL hsound hcomplete hvalid hgen (other, ets, acts) ety

end VDET

/-! ## §4 `HasAttrInRecord`: the producers

Five finite list walks, one per way a premise of `HasAttrInRecord` is run. All are
level-independent, so all are `Unsized`; see §6. -/

namespace HAIR

variable {Attr Xp Ty : Type}

/-- Generic bridge: membership in a `filterMap` over a map's cells. -/
theorem mem_filterMap_kvs {α β γ : Type} (f : α × β → Option γ) (m : Map α β) (y : γ) :
    y ∈ m.kvs.filterMap f ↔ ∃ p, MapContains p.1 p.2 m ∧ f p = some y := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hf⟩; exact ⟨p, (MapContains.iff_mem p.1 p.2 m).mpr hp, hf⟩
  · rintro ⟨p, hp, hf⟩; exact ⟨p, (MapContains.iff_mem p.1 p.2 m).mp hp, hf⟩

/-- `CapAttrMem x a c` run as a producer of `a`. -/
def capAttrOf [DecidableEq Xp] (x : Xp) : Xp × Key Attr Xp → Option Attr
  | (x', .attr a) => if x' = x then some a else none
  | (_, .tag _) => none

theorem capAttrOf_eq [DecidableEq Xp] (x : Xp) (p : Xp × Key Attr Xp) (a : Attr) :
    capAttrOf x p = some a ↔ p = (x, Key.attr a) := by
  obtain ⟨x', k⟩ := p
  cases k with
  | attr a' =>
      by_cases h : x' = x
      · subst h; simp only [capAttrOf, ite_eq_left, Prod.mk.injEq, Key.attr.injEq]
        simp [eq_comm]
      · simp [capAttrOf, h]
  | tag t => simp [capAttrOf]

def capAttrs [DecidableEq Xp] (x : Xp) (c : Capabilities Attr Xp) : Nat → Lv Attr := constP <|
  fun _ => c.filterMap (capAttrOf x)

theorem mem_capAttrs [DecidableEq Xp] (x : Xp) (c : Capabilities Attr Xp) (L n : Nat) (a : Attr) :
    a ∈ capAttrs x c L n ↔ CapAttrMem x a c := by
  rw [CapAttrMem.iff_mem]
  simp only [capAttrs, constP, List.mem_filterMap, capAttrOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro h; exact ⟨_, h, rfl⟩

theorem sound_capAttrs [DecidableEq Xp] (x : Xp) (c : Capabilities Attr Xp) :
    Sound (capAttrs x c) (fun a => CapAttrMem x a c) := by
  unfold capAttrs
  exact sound_constP fun n a h => (mem_capAttrs x c 0 n a).mp h

theorem unsized_capAttrs [DecidableEq Xp] (x : Xp) (c : Capabilities Attr Xp) :
    Unsized (capAttrs x c) (fun a => CapAttrMem x a c) := by
  unfold capAttrs
  exact unsized_constP fun a h n => (mem_capAttrs x c 0 n a).mpr h

theorem monoL_capAttrs [DecidableEq Xp] (x : Xp) (c : Capabilities Attr Xp) :
    MonoL (capAttrs (Attr := Attr) x c) := monoL_constP _

/-- `MapContains a qty rty` with `a` already bound: a producer of `qty` only. This is what Cedar's
`id a` annotation asks for. -/
def attrEq? [DecidableEq Attr] (a : Attr) : Attr × Qualified Ty → Option (Qualified Ty)
  | (a', q) => if a' = a then some q else none

def valsAt [DecidableEq Attr] (a : Attr) (rty : RecordType Attr Ty) : Nat → Lv (Qualified Ty) := constP <|
  fun _ => rty.kvs.filterMap (attrEq? a)

theorem mem_valsAt [DecidableEq Attr] (a : Attr) (rty : RecordType Attr Ty) (L n : Nat)
    (q : Qualified Ty) : q ∈ valsAt a rty L n ↔ MapContains a q rty := by
  simp only [valsAt, constP]
  rw [mem_filterMap_kvs]
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨a', q'⟩ := p
    simp only [attrEq?] at hf
    split at hf
    · rename_i h; subst h; simp only [Option.some.injEq] at hf; subst hf; exact hp
    · exact absurd hf (by simp)
  · intro h; exact ⟨(a, q), h, by simp [attrEq?]⟩

theorem sound_valsAt [DecidableEq Attr] (a : Attr) (rty : RecordType Attr Ty) :
    Sound (valsAt a rty) (fun q => MapContains a q rty) := by
  unfold valsAt
  exact sound_constP fun n q h => (mem_valsAt a rty 0 n q).mp h

theorem unsized_valsAt [DecidableEq Attr] (a : Attr) (rty : RecordType Attr Ty) :
    Unsized (valsAt a rty) (fun q => MapContains a q rty) := by
  unfold valsAt
  exact unsized_constP fun q h n => (mem_valsAt a rty 0 n q).mpr h

theorem monoL_valsAt [DecidableEq Attr] (a : Attr) (rty : RecordType Attr Ty) :
    MonoL (valsAt a rty) := monoL_constP _

/-- `MapContains a qty rty` with *both* outputs free. -/
def anyEntry (rty : RecordType Attr Ty) : Nat → Lv (Attr × Qualified Ty) := constP <| fun _ => rty.kvs

theorem sound_anyEntry (rty : RecordType Attr Ty) :
    Sound (anyEntry rty) (fun p => MapContains p.1 p.2 rty) := by
  unfold anyEntry
  exact sound_constP fun _ p hp => (MapContains.iff_mem p.1 p.2 rty).mpr hp

theorem unsized_anyEntry (rty : RecordType Attr Ty) :
    Unsized (anyEntry rty) (fun p => MapContains p.1 p.2 rty) := by
  unfold anyEntry
  exact unsized_constP fun p hp _ => (MapContains.iff_mem p.1 p.2 rty).mp hp

theorem monoL_anyEntry (rty : RecordType Attr Ty) : MonoL (anyEntry rty) := monoL_constP _

/-- `MapContains a (.required ty) rty`: a producer of the pair `(a, ty)`. -/
def reqOf : Attr × Qualified Ty → Option (Attr × Ty)
  | (a, .required t) => some (a, t)
  | (_, .optional _) => none

/-- `MapContains a (.optional ty) rty`. -/
def optOf : Attr × Qualified Ty → Option (Attr × Ty)
  | (a, .optional t) => some (a, t)
  | (_, .required _) => none

def reqEntries (rty : RecordType Attr Ty) : Nat → Lv (Attr × Ty) := constP <| fun _ => rty.kvs.filterMap reqOf
def optEntries (rty : RecordType Attr Ty) : Nat → Lv (Attr × Ty) := constP <| fun _ => rty.kvs.filterMap optOf

theorem mem_reqEntries (rty : RecordType Attr Ty) (L n : Nat) (r : Attr × Ty) :
    r ∈ reqEntries rty L n ↔ MapContains r.1 (Qualified.required r.2) rty := by
  simp only [reqEntries, constP]
  rw [mem_filterMap_kvs]
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨a', q'⟩ := p
    cases q' with
    | required t => simp only [reqOf, Option.some.injEq] at hf; subst hf; exact hp
    | optional t => exact absurd hf (by simp [reqOf])
  · intro h; exact ⟨(r.1, Qualified.required r.2), h, by simp [reqOf]⟩

theorem mem_optEntries (rty : RecordType Attr Ty) (L n : Nat) (r : Attr × Ty) :
    r ∈ optEntries rty L n ↔ MapContains r.1 (Qualified.optional r.2) rty := by
  simp only [optEntries, constP]
  rw [mem_filterMap_kvs]
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨a', q'⟩ := p
    cases q' with
    | optional t => simp only [optOf, Option.some.injEq] at hf; subst hf; exact hp
    | required t => exact absurd hf (by simp [optOf])
  · intro h; exact ⟨(r.1, Qualified.optional r.2), h, by simp [optOf]⟩

theorem sound_reqEntries (rty : RecordType Attr Ty) :
    Sound (reqEntries rty) (fun p => MapContains p.1 (Qualified.required p.2) rty) := by
  unfold reqEntries
  exact sound_constP fun n r h => (mem_reqEntries rty 0 n r).mp h
theorem unsized_reqEntries (rty : RecordType Attr Ty) :
    Unsized (reqEntries rty) (fun p => MapContains p.1 (Qualified.required p.2) rty) := by
  unfold reqEntries
  exact unsized_constP fun r h n => (mem_reqEntries rty 0 n r).mpr h
theorem monoL_reqEntries (rty : RecordType Attr Ty) : MonoL (reqEntries rty) := monoL_constP _
theorem sound_optEntries (rty : RecordType Attr Ty) :
    Sound (optEntries rty) (fun p => MapContains p.1 (Qualified.optional p.2) rty) := by
  unfold optEntries
  exact sound_constP fun n r h => (mem_optEntries rty 0 n r).mp h
theorem unsized_optEntries (rty : RecordType Attr Ty) :
    Unsized (optEntries rty) (fun p => MapContains p.1 (Qualified.optional p.2) rty) := by
  unfold optEntries
  exact unsized_constP fun r h n => (mem_optEntries rty 0 n r).mpr h
theorem monoL_optEntries (rty : RecordType Attr Ty) : MonoL (optEntries rty) := monoL_constP _

/-! ### The negative premise's verdict

`¬ CapAttrMem x a c` is discharged by `check`, with the polarity folded into the verdict — `.no` when
the capability *is* present. `TypeOfLean.lean:210` supplies the decision procedure; it is total, so
the verdict is decisive and `V.inconclusive` never arises. §6 records why that is load-bearing. -/

def notCapVerdict [DecidableEq Attr] [DecidableEq Xp] (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) : V :=
  if capAttrMemB x a c then V.no else V.yes

theorem notCapVerdict_ne_no_iff [DecidableEq Attr] [DecidableEq Xp] (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) : notCapVerdict x a c ≠ V.no ↔ ¬ CapAttrMem x a c := by
  simp only [notCapVerdict]
  rw [← capAttrMemB_iff]
  cases capAttrMemB x a c <;> simp

/-! ## §5 `HasAttrInRecord` as `Body` data -/

/-- Inputs: the record type, the receiver expression, the capabilities, `knownToExist`. -/
abbrev HIx (Attr Xp Ty : Type) := RecordType Attr Ty × Xp × Capabilities Attr Xp × Bool
/-- Outputs: the attribute name, the result type, the emitted capabilities. -/
abbrev HOut (Attr Xp Ty : Type) := Attr × Ty × Capabilities Attr Xp

variable [DecidableEq Attr] [DecidableEq Xp]

/-- `found_in_caps`: `a` from the capabilities, `qty` a discarded witness, `knownToExist` free. -/
def hCaps (ttTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, _) =>
      .aux .flat (capAttrs x c) (fun a => CapAttrMem x a c) fun a =>
        .aux .flat (valsAt a rty) (fun q => MapContains a q rty) fun _ =>
          .ret (a, ttTy, [])

/-- `found_required_known`: the `Bool` input is pinned by `cond`. -/
def hReq (ttTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, _, _, kn) =>
      .cond kn (kn = true)
        (.aux .flat (reqEntries rty) (fun p => MapContains p.1 (Qualified.required p.2) rty) fun p =>
          .ret (p.1, ttTy, []))

/-- `found_not_known`: `cond` pins `knownToExist = false`, then the **negative** check. -/
def hNot (anyTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, kn) =>
      .cond (!kn) (kn = false)
        (.aux .flat (anyEntry rty) (fun p => MapContains p.1 p.2 rty) fun p =>
          .check (notCapVerdict x p.1 c) (¬ CapAttrMem x p.1 c)
            (.ret (p.1, anyTy, [(x, Key.attr p.1)])))

/-- `found_optional_known`. -/
def hOpt (anyTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, kn) =>
      .cond kn (kn = true)
        (.aux .flat (optEntries rty) (fun p => MapContains p.1 (Qualified.optional p.2) rty) fun p =>
          .check (notCapVerdict x p.1 c) (¬ CapAttrMem x p.1 c)
            (.ret (p.1, anyTy, [(x, Key.attr p.1)])))

def hRules (ttTy anyTy : Ty) : RuleSet (HIx Attr Xp Ty) (HOut Attr Xp Ty) :=
  fun i => [hCaps ttTy i, hReq ttTy i, hNot anyTy i, hOpt anyTy i]

def HR (ttTy anyTy : Ty) : HIx Attr Xp Ty → HOut Attr Xp Ty → Prop :=
  fun i o => HasAttrInRecord ttTy anyTy i.1 i.2.1 o.1 i.2.2.1 i.2.2.2 o.2.1 o.2.2

theorem hvalid (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules (Attr := Attr) (Xp := Xp) ttTy anyTy i, ∀ o,
      HoldsR (HR ttTy anyTy) b o → HR ttTy anyTy i o := by
  intro ⟨rty, x, c, kn⟩ b hb o h
  simp only [hRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · simp only [hCaps, HoldsR] at h
    obtain ⟨a, hcap, q, hq, rfl⟩ := h
    exact HasAttrInRecord.found_in_caps rty x a c kn q hcap hq
  · simp only [hReq, HoldsR] at h
    obtain ⟨rfl, p, hp, rfl⟩ := h
    exact HasAttrInRecord.found_required_known rty x p.1 c p.2 hp
  · simp only [hNot, HoldsR] at h
    obtain ⟨rfl, p, hp, hnc, rfl⟩ := h
    exact HasAttrInRecord.found_not_known rty x p.1 c p.2 hp hnc
  · simp only [hOpt, HoldsR] at h
    obtain ⟨rfl, p, hp, hnc, rfl⟩ := h
    exact HasAttrInRecord.found_optional_known rty x p.1 c p.2 hp hnc

theorem hgen (ttTy anyTy : Ty) : ∀ (i : HIx Attr Xp Ty) (o : HOut Attr Xp Ty),
    HR ttTy anyTy i o → Derives (hRules ttTy anyTy) i o := by
  intro ⟨rty, x, c, kn⟩ ⟨a, oty, ocaps⟩ h
  replace h : HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps := h
  cases h with
  | found_in_caps _ qty hcap hq =>
      refine Derives.intro (b := hCaps ttTy (rty, x, c, kn)) (by simp [hRules]) ?_
      exact Holds.aux (b := a) hcap (Holds.aux (b := qty) hq (.ret _))
  | found_required_known ty hp =>
      refine Derives.intro (b := hReq ttTy (rty, x, c, true)) (by simp [hRules]) ?_
      exact Holds.cond rfl (Holds.aux (b := (a, ty)) hp (.ret _))
  | found_not_known qty hp hnc =>
      refine Derives.intro (b := hNot anyTy (rty, x, c, false)) (by simp [hRules]) ?_
      exact Holds.cond rfl (Holds.aux (b := (a, qty)) hp (Holds.check hnc (.ret _)))
  | found_optional_known ty hp hnc =>
      refine Derives.intro (b := hOpt anyTy (rty, x, c, true)) (by simp [hRules]) ?_
      exact Holds.cond rfl (Holds.aux (b := (a, ty)) hp (Holds.check hnc (.ret _)))

theorem hsound (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules (Attr := Attr) (Xp := Xp) ttTy anyTy i, BodySound b := by
  intro ⟨rty, x, c, kn⟩ b hb
  simp only [hRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨sound_capAttrs x c, fun a => ⟨sound_valsAt a rty, fun _ => trivial⟩⟩
  · exact ⟨fun h => h, sound_reqEntries rty, fun _ => trivial⟩
  · refine ⟨fun h => by simpa using h, sound_anyEntry rty, fun p => ⟨?_, trivial⟩⟩
    exact fun hv => (notCapVerdict_ne_no_iff x p.1 c).mp hv
  · refine ⟨fun h => h, sound_optEntries rty, fun p => ⟨?_, trivial⟩⟩
    exact fun hv => (notCapVerdict_ne_no_iff x p.1 c).mp hv

theorem hcomplete (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules (Attr := Attr) (Xp := Xp) ttTy anyTy i, BodyComplete b := by
  intro ⟨rty, x, c, kn⟩ b hb
  simp only [hRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨monoL_capAttrs x c, unsized_capAttrs x c,
      fun a => ⟨monoL_valsAt a rty, unsized_valsAt a rty, fun _ => trivial⟩⟩
  · exact ⟨fun h => h, monoL_reqEntries rty, unsized_reqEntries rty, fun _ => trivial⟩
  · refine ⟨fun h => by simpa using h, monoL_anyEntry rty, unsized_anyEntry rty,
      fun p => ⟨?_, trivial⟩⟩
    exact fun hnc => (notCapVerdict_ne_no_iff x p.1 c).mpr hnc
  · refine ⟨fun h => h, monoL_optEntries rty, unsized_optEntries rty, fun p => ⟨?_, trivial⟩⟩
    exact fun hnc => (notCapVerdict_ne_no_iff x p.1 c).mpr hnc

/-- **Adequacy for Cedar's `HasAttrInRecord`**, in the mode `HasType` uses. An instance of the
generic theorem: four `Unsized` facts, two decisive verdicts, two `cond` equivalences. -/
theorem hair_adequate (ttTy anyTy : Ty) (rty : RecordType Attr Ty) (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) (kn : Bool) (oty : Ty) (ocaps : Capabilities Attr Xp) :
    HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps ↔
      ∃ L l n, enum (hRules ttTy anyTy) L l (rty, x, c, kn) n (a, oty, ocaps) :=
  adequate (hsound ttTy anyTy) (hcomplete ttTy anyTy) (hvalid ttTy anyTy) (hgen ttTy anyTy)
    (rty, x, c, kn) (a, oty, ocaps)

/-- …and for the enumeration that runs. -/
theorem hair_mem_adequate (ttTy anyTy : Ty) (rty : RecordType Attr Ty) (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) (kn : Bool) (oty : Ty) (ocaps : Capabilities Attr Xp) :
    HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps ↔
      ∃ L l n, (a, oty, ocaps) ∈ enumL (hRules ttTy anyTy) L l (rty, x, c, kn) n :=
  adequateL (hsound ttTy anyTy) (hcomplete ttTy anyTy) (hvalid ttTy anyTy) (hgen ttTy anyTy)
    (rty, x, c, kn) (a, oty, ocaps)

/-! ### §5b The same relation with the discarded witnesses recognised as don't-cares

`qty` in `found_in_caps`/`found_not_known` and `ty` in `found_required_known`/`found_optional_known`
are pure witnesses: they occur in no conclusion. The framework has no constructor for "∃ witness,
value discarded", and `BodyComplete` demands `Unsized p P` for *every* `b` with `P b`, so the faithful
encoding above is *forced* to enumerate them. The only way out is to rewrite the premise's own
specification `P` to its existential closure and give it a producer of the *residual* outputs. That is
what this rule set does; §7 measures the difference. -/

def hasKey (a : Attr) (rty : RecordType Attr Ty) : Nat → Lv Unit := constP <|
  fun _ => if rty.kvs.any (fun p => decide (p.1 = a)) then [()] else []

theorem mem_hasKey (a : Attr) (rty : RecordType Attr Ty) (L n : Nat) (u : Unit) :
    u ∈ hasKey a rty L n ↔ ∃ q, MapContains a q rty := by
  simp only [hasKey, constP]
  constructor
  · intro h
    split at h
    · rename_i hany
      simp only [List.any_eq_true, decide_eq_true_eq] at hany
      obtain ⟨p, hp, rfl⟩ := hany
      exact ⟨p.2, (MapContains.iff_mem p.1 p.2 rty).mpr hp⟩
    · exact absurd h (by simp)
  · rintro ⟨q, hq⟩
    have hmem : ((a, q) : Attr × Qualified Ty) ∈ rty.kvs := (MapContains.iff_mem a q rty).mp hq
    have hb : (rty.kvs.any (fun p => decide (p.1 = a))) = true := by
      simp only [List.any_eq_true, decide_eq_true_eq]; exact ⟨(a, q), hmem, rfl⟩
    cases u
    simp [hb]

theorem sound_hasKey (a : Attr) (rty : RecordType Attr Ty) :
    Sound (hasKey a rty) (fun _ => ∃ q, MapContains a q rty) := by
  unfold hasKey
  exact sound_constP fun n u h => (mem_hasKey a rty 0 n u).mp h
theorem unsized_hasKey (a : Attr) (rty : RecordType Attr Ty) :
    Unsized (hasKey a rty) (fun _ => ∃ q, MapContains a q rty) := by
  unfold hasKey
  exact unsized_constP fun u h n => (mem_hasKey a rty 0 n u).mpr h
theorem monoL_hasKey (a : Attr) (rty : RecordType Attr Ty) : MonoL (hasKey a rty) := monoL_constP _

def reqKeyOf : Attr × Qualified Ty → Option Attr
  | (a, .required _) => some a
  | (_, .optional _) => none
def optKeyOf : Attr × Qualified Ty → Option Attr
  | (a, .optional _) => some a
  | (_, .required _) => none

def reqKeys (rty : RecordType Attr Ty) : Nat → Lv Attr := constP <| fun _ => rty.kvs.filterMap reqKeyOf
def optKeys (rty : RecordType Attr Ty) : Nat → Lv Attr := constP <| fun _ => rty.kvs.filterMap optKeyOf
def anyKeys (rty : RecordType Attr Ty) : Nat → Lv Attr := constP <| fun _ => rty.kvs.map Prod.fst

omit [DecidableEq Attr] in
theorem mem_reqKeys (rty : RecordType Attr Ty) (L n : Nat) (a : Attr) :
    a ∈ reqKeys rty L n ↔ ∃ t, MapContains a (Qualified.required t) rty := by
  simp only [reqKeys, constP]
  rw [mem_filterMap_kvs]
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨a', q'⟩ := p
    cases q' with
    | required t => simp only [reqKeyOf, Option.some.injEq] at hf; subst hf; exact ⟨t, hp⟩
    | optional t => exact absurd hf (by simp [reqKeyOf])
  · rintro ⟨t, h⟩; exact ⟨(a, Qualified.required t), h, by simp [reqKeyOf]⟩

omit [DecidableEq Attr] in
theorem mem_optKeys (rty : RecordType Attr Ty) (L n : Nat) (a : Attr) :
    a ∈ optKeys rty L n ↔ ∃ t, MapContains a (Qualified.optional t) rty := by
  simp only [optKeys, constP]
  rw [mem_filterMap_kvs]
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨a', q'⟩ := p
    cases q' with
    | optional t => simp only [optKeyOf, Option.some.injEq] at hf; subst hf; exact ⟨t, hp⟩
    | required t => exact absurd hf (by simp [optKeyOf])
  · rintro ⟨t, h⟩; exact ⟨(a, Qualified.optional t), h, by simp [optKeyOf]⟩

omit [DecidableEq Attr] in
theorem mem_anyKeys (rty : RecordType Attr Ty) (L n : Nat) (a : Attr) :
    a ∈ anyKeys rty L n ↔ ∃ q, MapContains a q rty := by
  simp only [anyKeys, constP, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, (MapContains.iff_mem p.1 p.2 rty).mpr hp⟩
  · rintro ⟨q, hq⟩; exact ⟨(a, q), (MapContains.iff_mem a q rty).mp hq, rfl⟩

omit [DecidableEq Attr] in
theorem sound_reqKeys (rty : RecordType Attr Ty) :
    Sound (reqKeys rty) (fun a => ∃ t, MapContains a (Qualified.required t) rty) := by
  unfold reqKeys
  exact sound_constP fun n a h => (mem_reqKeys rty 0 n a).mp h
omit [DecidableEq Attr] in
theorem unsized_reqKeys (rty : RecordType Attr Ty) :
    Unsized (reqKeys rty) (fun a => ∃ t, MapContains a (Qualified.required t) rty) := by
  unfold reqKeys
  exact unsized_constP fun a h n => (mem_reqKeys rty 0 n a).mpr h
omit [DecidableEq Attr] in
theorem monoL_reqKeys (rty : RecordType Attr Ty) : MonoL (reqKeys rty) := monoL_constP _
omit [DecidableEq Attr] in
theorem sound_optKeys (rty : RecordType Attr Ty) :
    Sound (optKeys rty) (fun a => ∃ t, MapContains a (Qualified.optional t) rty) := by
  unfold optKeys
  exact sound_constP fun n a h => (mem_optKeys rty 0 n a).mp h
omit [DecidableEq Attr] in
theorem unsized_optKeys (rty : RecordType Attr Ty) :
    Unsized (optKeys rty) (fun a => ∃ t, MapContains a (Qualified.optional t) rty) := by
  unfold optKeys
  exact unsized_constP fun a h n => (mem_optKeys rty 0 n a).mpr h
omit [DecidableEq Attr] in
theorem monoL_optKeys (rty : RecordType Attr Ty) : MonoL (optKeys rty) := monoL_constP _
omit [DecidableEq Attr] in
theorem sound_anyKeys (rty : RecordType Attr Ty) :
    Sound (anyKeys rty) (fun a => ∃ q, MapContains a q rty) := by
  unfold anyKeys
  exact sound_constP fun n a h => (mem_anyKeys rty 0 n a).mp h
omit [DecidableEq Attr] in
theorem unsized_anyKeys (rty : RecordType Attr Ty) :
    Unsized (anyKeys rty) (fun a => ∃ q, MapContains a q rty) := by
  unfold anyKeys
  exact unsized_constP fun a h n => (mem_anyKeys rty 0 n a).mpr h
omit [DecidableEq Attr] in
theorem monoL_anyKeys (rty : RecordType Attr Ty) : MonoL (anyKeys rty) := monoL_constP _

def hCaps' (ttTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, _) =>
      .aux .flat (capAttrs x c) (fun a => CapAttrMem x a c) fun a =>
        .aux .flat (hasKey a rty) (fun _ => ∃ q, MapContains a q rty) fun _ =>
          .ret (a, ttTy, [])

def hReq' (ttTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, _, _, kn) =>
      .cond kn (kn = true)
        (.aux .flat (reqKeys rty) (fun a => ∃ t, MapContains a (Qualified.required t) rty) fun a =>
          .ret (a, ttTy, []))

def hNot' (anyTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, kn) =>
      .cond (!kn) (kn = false)
        (.aux .flat (anyKeys rty) (fun a => ∃ q, MapContains a q rty) fun a =>
          .check (notCapVerdict x a c) (¬ CapAttrMem x a c)
            (.ret (a, anyTy, [(x, Key.attr a)])))

def hOpt' (anyTy : Ty) : HIx Attr Xp Ty → Body (HIx Attr Xp Ty) (HOut Attr Xp Ty)
  | (rty, x, c, kn) =>
      .cond kn (kn = true)
        (.aux .flat (optKeys rty) (fun a => ∃ t, MapContains a (Qualified.optional t) rty) fun a =>
          .check (notCapVerdict x a c) (¬ CapAttrMem x a c)
            (.ret (a, anyTy, [(x, Key.attr a)])))

def hRules' (ttTy anyTy : Ty) : RuleSet (HIx Attr Xp Ty) (HOut Attr Xp Ty) :=
  fun i => [hCaps' ttTy i, hReq' ttTy i, hNot' anyTy i, hOpt' anyTy i]

theorem hvalid' (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules' (Attr := Attr) (Xp := Xp) ttTy anyTy i, ∀ o,
      HoldsR (HR ttTy anyTy) b o → HR ttTy anyTy i o := by
  intro ⟨rty, x, c, kn⟩ b hb o h
  simp only [hRules', List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · simp only [hCaps', HoldsR] at h
    obtain ⟨a, hcap, _, ⟨q, hq⟩, rfl⟩ := h
    exact HasAttrInRecord.found_in_caps rty x a c kn q hcap hq
  · simp only [hReq', HoldsR] at h
    obtain ⟨rfl, a, ⟨t, ht⟩, rfl⟩ := h
    exact HasAttrInRecord.found_required_known rty x a c t ht
  · simp only [hNot', HoldsR] at h
    obtain ⟨rfl, a, ⟨q, hq⟩, hnc, rfl⟩ := h
    exact HasAttrInRecord.found_not_known rty x a c q hq hnc
  · simp only [hOpt', HoldsR] at h
    obtain ⟨rfl, a, ⟨t, ht⟩, hnc, rfl⟩ := h
    exact HasAttrInRecord.found_optional_known rty x a c t ht hnc

theorem hgen' (ttTy anyTy : Ty) : ∀ (i : HIx Attr Xp Ty) (o : HOut Attr Xp Ty),
    HR ttTy anyTy i o → Derives (hRules' ttTy anyTy) i o := by
  intro ⟨rty, x, c, kn⟩ ⟨a, oty, ocaps⟩ h
  replace h : HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps := h
  cases h with
  | found_in_caps _ qty hcap hq =>
      refine Derives.intro (b := hCaps' ttTy (rty, x, c, kn)) (by simp [hRules']) ?_
      exact Holds.aux (b := a) hcap (Holds.aux (b := ()) ⟨qty, hq⟩ (.ret _))
  | found_required_known ty hp =>
      refine Derives.intro (b := hReq' ttTy (rty, x, c, true)) (by simp [hRules']) ?_
      exact Holds.cond rfl (Holds.aux (b := a) ⟨ty, hp⟩ (.ret _))
  | found_not_known qty hp hnc =>
      refine Derives.intro (b := hNot' anyTy (rty, x, c, false)) (by simp [hRules']) ?_
      exact Holds.cond rfl (Holds.aux (b := a) ⟨qty, hp⟩ (Holds.check hnc (.ret _)))
  | found_optional_known ty hp hnc =>
      refine Derives.intro (b := hOpt' anyTy (rty, x, c, true)) (by simp [hRules']) ?_
      exact Holds.cond rfl (Holds.aux (b := a) ⟨ty, hp⟩ (Holds.check hnc (.ret _)))

theorem hsound' (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules' (Attr := Attr) (Xp := Xp) ttTy anyTy i, BodySound b := by
  intro ⟨rty, x, c, kn⟩ b hb
  simp only [hRules', List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨sound_capAttrs x c, fun a => ⟨sound_hasKey a rty, fun _ => trivial⟩⟩
  · exact ⟨fun h => h, sound_reqKeys rty, fun _ => trivial⟩
  · refine ⟨fun h => by simpa using h, sound_anyKeys rty, fun a => ⟨?_, trivial⟩⟩
    exact fun hv => (notCapVerdict_ne_no_iff x a c).mp hv
  · refine ⟨fun h => h, sound_optKeys rty, fun a => ⟨?_, trivial⟩⟩
    exact fun hv => (notCapVerdict_ne_no_iff x a c).mp hv

theorem hcomplete' (ttTy anyTy : Ty) :
    ∀ i, ∀ b ∈ hRules' (Attr := Attr) (Xp := Xp) ttTy anyTy i, BodyComplete b := by
  intro ⟨rty, x, c, kn⟩ b hb
  simp only [hRules', List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨monoL_capAttrs x c, unsized_capAttrs x c,
      fun a => ⟨monoL_hasKey a rty, unsized_hasKey a rty, fun _ => trivial⟩⟩
  · exact ⟨fun h => h, monoL_reqKeys rty, unsized_reqKeys rty, fun _ => trivial⟩
  · refine ⟨fun h => by simpa using h, monoL_anyKeys rty, unsized_anyKeys rty,
      fun a => ⟨?_, trivial⟩⟩
    exact fun hnc => (notCapVerdict_ne_no_iff x a c).mpr hnc
  · refine ⟨fun h => h, monoL_optKeys rty, unsized_optKeys rty, fun a => ⟨?_, trivial⟩⟩
    exact fun hnc => (notCapVerdict_ne_no_iff x a c).mpr hnc

/-- **The don't-care rule set is adequate too.** Same relation, same generic theorem; the witnesses
are gone from the enumeration but not from the relation. -/
theorem hair_adequate' (ttTy anyTy : Ty) (rty : RecordType Attr Ty) (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) (kn : Bool) (oty : Ty) (ocaps : Capabilities Attr Xp) :
    HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps ↔
      ∃ L l n, enum (hRules' ttTy anyTy) L l (rty, x, c, kn) n (a, oty, ocaps) :=
  adequate (hsound' ttTy anyTy) (hcomplete' ttTy anyTy) (hvalid' ttTy anyTy) (hgen' ttTy anyTy)
    (rty, x, c, kn) (a, oty, ocaps)

theorem hair_mem_adequate' (ttTy anyTy : Ty) (rty : RecordType Attr Ty) (x : Xp) (a : Attr)
    (c : Capabilities Attr Xp) (kn : Bool) (oty : Ty) (ocaps : Capabilities Attr Xp) :
    HasAttrInRecord ttTy anyTy rty x a c kn oty ocaps ↔
      ∃ L l n, (a, oty, ocaps) ∈ enumL (hRules' ttTy anyTy) L l (rty, x, c, kn) n :=
  adequateL (hsound' ttTy anyTy) (hcomplete' ttTy anyTy) (hvalid' ttTy anyTy) (hgen' ttTy anyTy)
    (rty, x, c, kn) (a, oty, ocaps)

end HAIR

/-! ## §7 Ground truth, by evaluation

`enumL` is ordinary code, so the two questions about multiplicity can just be run. -/

namespace Demo

open HAIR

abbrev A := String
abbrev X := Nat
abbrev T := String

/-- One required and one optional attribute; the receiver `0` holds the `name` capability. -/
def rty1 : RecordType A T := .mk [("name", .required "String"), ("age", .optional "Long")]
def caps1 : Capabilities A X := [(0, Key.attr "name")]

/-- A *duplicate key* — legal for the relational `MapContains`, excluded by `Map.WellFormed`. -/
def rty2 : RecordType A T := .mk [("name", .required "String"), ("name", .optional "Long")]

-- Everything lands at level **0**. Under the framework's `pay`-inside-the-body convention (see
-- `GradedRuleAdequacy.lean`: "a rule with no recursive premise costs nothing") a non-recursive
-- relation emits no `pay` at all, and every premise here is a level-preserving `.flat` walk over a
-- finite list. So `HasAttrInRecord`'s whole solution set sits at level 0 and the level index carries
-- no information about it whatsoever. (The earlier `stepOf`-wraps-`pay` framework put the same three
-- solutions at level 1; the *contents* below are unchanged, only the index they live at.)
/-- info: [3, 0, 0, 0] -/
#guard_msgs in
#eval ((List.range 4).map fun n =>
  (enumL (hRules (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty1, 0, caps1, true) n).length)

-- `knownToExist = true`: `found_in_caps` and `found_required_known` have **identical conclusions**
-- for `name`, so it is listed twice. A count-graded enumerator must report 2 here.
/--
info: [("name", "tt", []), ("name", "tt", []), ("age", "anyBool", [(0, CedarRule.Key.attr "age")])]
-/
#guard_msgs in
#eval (enumL (hRules (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty1, 0, caps1, true) 0)

-- `knownToExist = false`: `found_required_known`/`found_optional_known` are pruned by `cond`,
-- `found_not_known` takes over, and `name` is now listed once.
/-- info: [("name", "tt", []), ("age", "anyBool", [(0, CedarRule.Key.attr "age")])] -/
#guard_msgs in
#eval (enumL (hRules (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty1, 0, caps1, false) 0)

-- The don't-care rule set agrees exactly: recognising the discarded witnesses does *not* collapse the
-- identical-conclusion duplicate, because that duplicate comes from two different rules.
/--
info: [("name", "tt", []), ("name", "tt", []), ("age", "anyBool", [(0, CedarRule.Key.attr "age")])]
-/
#guard_msgs in
#eval (enumL (hRules' (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty1, 0, caps1, true) 0)

-- With a duplicate key, the *faithful* encoding lists `name` three times: twice from
-- `found_in_caps` (one per `qty` with `MapContains "name" qty rty2`) and once from
-- `found_required_known`.
/-- info: [("name", "tt", []), ("name", "tt", []), ("name", "tt", [])] -/
#guard_msgs in
#eval (enumL (hRules (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty2, 0, caps1, true) 0)

-- The don't-care encoding lists it twice: the witness-driven duplicate is gone, the
-- two-rules-one-conclusion duplicate remains. Both rule sets satisfy the *same* adequacy theorem,
-- which is membership-only and cannot tell them apart.
/-- info: [("name", "tt", []), ("name", "tt", [])] -/
#guard_msgs in
#eval (enumL (hRules' (Attr := A) (Xp := X) "tt" "anyBool") 0 2 (rty2, 0, caps1, true) 0)

end Demo

/-! ## §8 `AllLub`: the first `Body.call` on a Cedar relation

Neither relation above recurses, so `Body.call` — the constructor the framework is *for* — was
untested. `AllLub` (`TypeOfLean.lean:390`) is the smallest Cedar relation that fixes that, and it was
chosen over the `Lub`/`LubQualified`/`LubRecord` and `LubCompat`/`LubCompatRecord` families for three
reasons:

* **It is a single relation, not a mutual family.** So `ι` and `α` are the relation's own mode split
  and no sum-and-tag encoding is needed. That isolates what is under test: `call` itself, rather than
  `call` plus a tagging discipline. (§9 pays the sum-and-tag cost separately.)
* **Its recursive premise's *index* depends on an auxiliary output.** `cons` reads
  `Lub acc hd lubTy → AllLub lubTy tl result`: `lubTy` is produced by a *different SCC* (so it is an
  `aux` premise) and is then the **input** of the recursive call. That is the shape that makes
  scheduling hard — the sub-goal is not known until the auxiliary premise has committed — and it is
  the shape `Lub`'s own recursion does *not* have (`Lub.set` calls `Lub s₁ s₂ s` on sub-terms of its
  own inputs).
* **Its recursion is on a `List`, not on the type tree.** So the level reached is the list length and
  can be read off an `#eval`, which makes `call`'s level arithmetic (`bindC`: the sub-derivation's
  level plus this rule's `pay` must exhaust the budget) checkable by hand.

### `Lub` is left abstract, deliberately

For `AllLub`, `Lub` is a *different SCC*. The framework's `aux` constructor is exactly the interface
for that: an executable producer plus the specification it claims. So `Lub` enters as a relation
variable `LubR` together with a producer `lubProd` and its three obligations as hypotheses — the same
type-variable discipline the module docstring uses for `Ty`/`Xp`/`ET`. Instantiating
`LubR := Cedar.Lub` and `lubProd := fun t₁ t₂ => constP fun _ => (lub? t₁ t₂).toList` recovers Cedar's
`AllLub` on the nose. Nothing below inspects `Ty` at all. -/

namespace ALub

variable {Ty : Type}

/-- `TypeOfLean.lean:390`, verbatim with `Lub` as a parameter. -/
inductive AllLub (LubR : Ty → Ty → Ty → Prop) : Ty → List Ty → Ty → Prop where
  | nil : ∀ ty, AllLub LubR ty [] ty
  | cons : ∀ acc hd tl lubTy result,
      LubR acc hd lubTy → AllLub LubR lubTy tl result → AllLub LubR acc (hd :: tl) result

/-- Mode, as `HasType.set` uses it (`TypeOfLean.lean:1238`): inputs the accumulator and the list,
output the folded type. -/
abbrev AIx (Ty : Type) := Ty × List Ty

/-- `nil`: `fail` on a non-empty list. The conclusion pins *both* the input list and the output to the
accumulator, and `Body` expresses that with a match on the index plus `ret`. -/
def aNil : AIx Ty → Body (AIx Ty) Ty
  | (acc, []) => .ret acc
  | (_, _ :: _) => .fail

/-- `cons`: the cross-SCC `Lub` premise, then **the recursive call at an index built from that
premise's output**, then the conclusion. `pay` charges the one rule application, so the level a
derivation reaches is exactly the list's length. -/
def aCons (LubR : Ty → Ty → Ty → Prop) (lubProd : Ty → Ty → Nat → Lv Ty) :
    AIx Ty → Body (AIx Ty) Ty
  | (_, []) => .fail
  | (acc, hd :: tl) =>
      .pay (.aux .flat (lubProd acc hd) (fun t => LubR acc hd t) fun lubTy =>
        .call (lubTy, tl) fun result => .ret result)

def aRules (LubR : Ty → Ty → Ty → Prop) (lubProd : Ty → Ty → Nat → Lv Ty) :
    RuleSet (AIx Ty) Ty := fun i => [aNil i, aCons LubR lubProd i]

/-- The relation, re-indexed the way the enumeration is. -/
def AR (LubR : Ty → Ty → Ty → Prop) : AIx Ty → Ty → Prop := fun i r => AllLub LubR i.1 i.2 r

variable {LubR : Ty → Ty → Ty → Prop} {lubProd : Ty → Ty → Nat → Lv Ty}

theorem hvalid : ∀ i, ∀ b ∈ aRules LubR lubProd i, ∀ r, HoldsR (AR LubR) b r → AR LubR i r := by
  intro ⟨acc, l⟩ b hb r h
  simp only [aRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · cases l with
    | nil => simp only [aNil, HoldsR] at h; subst h; exact .nil _
    | cons hd tl => exact (h : HoldsR _ (Body.fail) r).elim
  · cases l with
    | nil => exact (h : HoldsR _ (Body.fail) r).elim
    | cons hd tl =>
        simp only [aCons, HoldsR] at h
        obtain ⟨lubTy, hlub, res, hrec, rfl⟩ := h
        exact .cons acc hd tl lubTy _ hlub hrec

theorem hgen : ∀ (i : AIx Ty) (r : Ty), AR LubR i r → Derives (aRules LubR lubProd) i r := by
  intro ⟨acc, l⟩ r h
  replace h : AllLub LubR acc l r := h
  induction h with
  | nil ty => exact Derives.intro (b := aNil (ty, [])) (by simp [aRules]) (.ret _)
  | cons acc hd tl lubTy result hlub _ ih =>
      refine Derives.intro (b := aCons LubR lubProd (acc, hd :: tl)) (by simp [aRules]) ?_
      exact .pay (Holds.aux (b := lubTy) hlub (.call ih (.ret _)))

/-- `aNil`/`aCons` carry no `check` and no `cond`, so soundness is the `Lub` producer's soundness and
nothing else. -/
theorem hsound (hs : ∀ a b : Ty, Sound (lubProd a b) (fun t => LubR a b t)) :
    ∀ i, ∀ b ∈ aRules LubR lubProd i, BodySound b := by
  intro ⟨acc, l⟩ b hb
  simp only [aRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · cases l <;> exact trivial
  · cases l with
    | nil => exact trivial
    | cons hd tl => exact ⟨hs acc hd, fun _ => fun _ => trivial⟩

/-- Likewise completeness: the `.flat` grade is legitimate because Cedar's `Lub` is a *function* of
its two inputs, so its producer is a one-or-zero element list at every level. **The `call` premise
imposes no obligation at all** — `BodyComplete (.call _ k) = ∀ a, BodyComplete (k a)` — which is the
point: a recursive premise always carries its own size, so there is no grading choice to get wrong. -/
theorem hcomplete (hm : ∀ a b : Ty, MonoL (lubProd a b))
    (hu : ∀ a b : Ty, Unsized (lubProd a b) (fun t => LubR a b t)) :
    ∀ i, ∀ b ∈ aRules LubR lubProd i, BodyComplete b := by
  intro ⟨acc, l⟩ b hb
  simp only [aRules, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · cases l <;> exact trivial
  · cases l with
    | nil => exact trivial
    | cons hd tl => exact ⟨hm acc hd, hu acc hd, fun _ => fun _ => trivial⟩

/-- **Adequacy for Cedar's `AllLub`** — the first instance in this file whose rule set contains a
`Body.call`. Same four hypotheses, same generic theorem. -/
theorem allLub_adequate (hs : ∀ a b : Ty, Sound (lubProd a b) (fun t => LubR a b t))
    (hm : ∀ a b : Ty, MonoL (lubProd a b))
    (hu : ∀ a b : Ty, Unsized (lubProd a b) (fun t => LubR a b t))
    (acc : Ty) (tys : List Ty) (result : Ty) :
    AllLub LubR acc tys result ↔
      ∃ L l n, enum (aRules LubR lubProd) L l (acc, tys) n result :=
  adequate (hsound hs) (hcomplete hm hu) hvalid hgen (acc, tys) result

/-- …and for the enumeration that runs. -/
theorem allLub_mem_adequate (hs : ∀ a b : Ty, Sound (lubProd a b) (fun t => LubR a b t))
    (hm : ∀ a b : Ty, MonoL (lubProd a b))
    (hu : ∀ a b : Ty, Unsized (lubProd a b) (fun t => LubR a b t))
    (acc : Ty) (tys : List Ty) (result : Ty) :
    AllLub LubR acc tys result ↔
      ∃ L l n, result ∈ enumL (aRules LubR lubProd) L l (acc, tys) n :=
  adequateL (hsound hs) (hcomplete hm hu) hvalid hgen (acc, tys) result

end ALub

/-! ## §8b `call` at run time

`AllLub`'s rule set is ordinary code, so `call`'s level arithmetic can be evaluated rather than
argued. Two instantiations: a *functional* `Lub` (Cedar's own situation — at most one lub per pair)
and a *relational* one, to see the recursive fan-out. -/

namespace ACallDemo

open ALub

/-- The functional case: `Lub a b c ↔ c = max a b`, exactly one answer per pair. -/
def maxR (a b c : Nat) : Prop := c = max a b
def maxProd (a b : Nat) : Nat → Lv Nat := constP <| fun _ => [max a b]

theorem sound_maxProd (a b : Nat) : Sound (maxProd a b) (maxR a b) := by
  unfold maxProd
  exact sound_constP fun _ c hc => by simpa [maxR, eq_comm] using hc
theorem unsized_maxProd (a b : Nat) : Unsized (maxProd a b) (maxR a b) := by
  unfold maxProd
  exact unsized_constP fun c hc _ => by simp only [maxR] at hc; simp [hc]
theorem monoL_maxProd (a b : Nat) : MonoL (maxProd a b) := monoL_constP _

/-- The relational case: two incomparable "lubs" per pair, so a list of length `k` has `2^k`
derivations. Nothing about the framework notices the difference. -/
def twoR (a b c : Nat) : Prop := c = a + b ∨ c = a * b
def twoProd (a b : Nat) : Nat → Lv Nat := constP <| fun _ => [a + b, a * b]

theorem sound_twoProd (a b : Nat) : Sound (twoProd a b) (twoR a b) := by
  unfold twoProd
  exact sound_constP fun _ c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
theorem unsized_twoProd (a b : Nat) : Unsized (twoProd a b) (twoR a b) := by
  unfold twoProd
  exact unsized_constP fun c hc _ => by
    rcases hc with rfl | rfl <;> simp
theorem monoL_twoProd (a b : Nat) : MonoL (twoProd a b) := monoL_constP _

-- `AllLub maxR 0 [3,1,2] r` has the unique solution `r = 3`, and — the fact `call` is responsible
-- for — it lands at the level the list's length dictates: each `aCons` application `pay`s one level
-- and `bindC` forces the recursive sub-derivation to account for the rest exactly. Neighbouring
-- levels are empty, so `call` is neither losing nor duplicating level.
/-- info: [[], [], [], [3], [], []] -/
#guard_msgs in
#eval ((List.range 6).map fun n => enumL (aRules maxR maxProd) 0 5 (0, [3, 1, 2]) n)

-- The prefixes, to see the level track the list's length.
/-- info: [[0], [], [], []] -/
#guard_msgs in
#eval ((List.range 4).map fun n => enumL (aRules maxR maxProd) 0 5 (0, ([] : List Nat)) n)
/-- info: [[], [3], [], []] -/
#guard_msgs in
#eval ((List.range 4).map fun n => enumL (aRules maxR maxProd) 0 5 (0, [3]) n)
/-- info: [[], [], [3], []] -/
#guard_msgs in
#eval ((List.range 4).map fun n => enumL (aRules maxR maxProd) 0 5 (0, [3, 1]) n)

-- Starving the iteration count: `l` bounds the recursion depth, so `l = 2` and `l = 3` cannot reach
-- the bottom of a 3-element list and the enumeration is empty at *every* level. This is the `call`
-- analogue of the leaf-budget starvation `adequate`'s `∃ L` absorbs, and it is why `adequate`
-- existentially quantifies `l` as well.
/-- info: [[], [], [], [], [], []] -/
#guard_msgs in
#eval ((List.range 6).map fun n => enumL (aRules maxR maxProd) 0 2 (0, [3, 1, 2]) n)
/-- info: [[], [], [], [], [], []] -/
#guard_msgs in
#eval ((List.range 6).map fun n => enumL (aRules maxR maxProd) 0 3 (0, [3, 1, 2]) n)
-- …and `l = 4` is the first that suffices: three `aCons` unfoldings plus the `aNil` that closes the
-- recursion. So the iteration count `l` counts *rule applications on the recursive spine*, one more
-- than the level, because `aNil` costs an iteration and (having no recursive premise) no level.
/-- info: [[], [], [], [3], [], []] -/
#guard_msgs in
#eval ((List.range 6).map fun n => enumL (aRules maxR maxProd) 0 4 (0, [3, 1, 2]) n)

-- The relational case: `2 ^ 3 = 8` derivations of `AllLub twoR 1 [2,3,4]`, all at one level — the
-- `bindC` in `call` convolves the auxiliary premise's level (0, because `.flat`) with the
-- sub-derivation's, so fan-out costs multiplicity and not level. Duplicates are retained: `AllLub` is
-- a `Prop` and the adequacy theorem is membership-only, exactly as §7 records for `HasAttrInRecord`.
/-- info: [0, 0, 0, 8, 0] -/
#guard_msgs in
#eval ((List.range 5).map fun n => (enumL (aRules twoR twoProd) 0 5 (1, [2, 3, 4]) n).length)
-- `10` and `24` each appear twice: `1+2=3, 3+3=6, 6+4=10` and `1*2=2, 2*3=6, 6+4=10` are different
-- derivations of the same output, and `enumL` keeps both.
/-- info: [10, 24, 13, 36, 9, 20, 10, 24] -/
#guard_msgs in
#eval (enumL (aRules twoR twoProd) 0 5 (1, [2, 3, 4]) 3)

/-- And the adequacy theorem applies to the run: `3` really is the `AllLub`-image of `[3,1,2]`,
read off the executable enumeration by `decide` and transported by `allLub_mem_adequate`. -/
theorem maxR_allLub_3 : AllLub maxR 0 [3, 1, 2] 3 :=
  (allLub_mem_adequate sound_maxProd monoL_maxProd unsized_maxProd 0 [3, 1, 2] 3).mpr
    ⟨0, 5, 3, by decide⟩

end ACallDemo

/-! ## §9 A mutual family under sum-and-tag: `Lub` / `LubQualified` / `LubRecord`

§8's `AllLub` is a single relation, so `Body.call` never had to cross between members of an SCC. Cedar's
real shape is mutual: `TypeOfLean.lean` has three mutual families totalling 46 relations, and the
smallest of them is `[Lub, LubQualified, LubRecord]` (lines 70–90). Its three members produce three
*different* things — a `CedarType`, a `QualifiedType`, a record's association list — so one `RuleSet`
covering the family needs

    ι := ι₁ ⊕ ι₂ ⊕ ι₃    α := α₁ ⊕ α₂ ⊕ α₃

because `call i k` hands `k` the rule set's single `α`. This section pays that cost in full and
measures it; §10 states the bill.

It is also the exact complement of §3–§7: **no `aux` premise appears anywhere in this family.** Every
premise is a `call`, a `cond` on the inputs, or nothing. So `Covers`/`Unsized`/`MonoL` — the grading
obligations the whole framework exists to police — are never mentioned, and the relations of §3–§7
(all leaves, no `call`) and this one (all `call`, no leaves) together cover both halves of `Body`.

### Transcription

`CTy` is `Cedar/Validation/Types.lean`'s `CedarType` with `EntityType` and `ExtType` left as type
variables (`Et`, `Xt`) and `Attr` as `At`, since none of the three relations inspects them. One
deviation: Cedar's `record` field is `Map Attr QualifiedType` and `Lub.record` matches
`.record (.mk r₁)`; the `Map.mk` wrapper carries no content the relation reads, so `CTy.record` holds
the association list directly. `BoolType`/`BoolTypeNeq` are copied verbatim, and `boolTypeNeq_iff`
records that `BoolTypeNeq` is exactly `≠` on a three-element type — which is what makes the `cond`
decidable without a decision procedure. -/

namespace LubFam
inductive BoolTy where | anyBool | tt | ff
  deriving DecidableEq, Repr

inductive BoolTypeNeq : BoolTy → BoolTy → Prop where
  | tt_ff : BoolTypeNeq .tt .ff
  | tt_any : BoolTypeNeq .tt .anyBool
  | ff_tt : BoolTypeNeq .ff .tt
  | ff_any : BoolTypeNeq .ff .anyBool
  | any_tt : BoolTypeNeq .anyBool .tt
  | any_ff : BoolTypeNeq .anyBool .ff

inductive CTy (At Et Xt : Type) where
  | bool (b : BoolTy)
  | int
  | string
  | entity (ety : Et)
  | set (ty : CTy At Et Xt)
  | record (rty : List (At × Qualified (CTy At Et Xt)))
  | ext (xty : Xt)
  deriving Repr

variable {At Et Xt : Type}

abbrev QTy (At Et Xt : Type) := Qualified (CTy At Et Xt)
abbrev RTy (At Et Xt : Type) := List (At × QTy At Et Xt)

mutual
inductive Lub : CTy At Et Xt → CTy At Et Xt → CTy At Et Xt → Prop where
  | boolSame : ∀ b, Lub (.bool b) (.bool b) (.bool b)
  | boolDiff : ∀ b₁ b₂, BoolTypeNeq b₁ b₂ → Lub (.bool b₁) (.bool b₂) (.bool .anyBool)
  | int : Lub .int .int .int
  | string : Lub .string .string .string
  | entity : ∀ ety, Lub (.entity ety) (.entity ety) (.entity ety)
  | ext : ∀ xty, Lub (.ext xty) (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂ s, Lub s₁ s₂ s → Lub (.set s₁) (.set s₂) (.set s)
  | record : ∀ r₁ r₂ r, LubRecord r₁ r₂ r → Lub (.record r₁) (.record r₂) (.record r)

inductive LubQualified : QTy At Et Xt → QTy At Et Xt → QTy At Et Xt → Prop where
  | optional : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.optional t₁) (.optional t₂) (.optional t)
  | required : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.required t₁) (.required t₂) (.required t)

inductive LubRecord : RTy At Et Xt → RTy At Et Xt → RTy At Et Xt → Prop where
  | nil : LubRecord [] [] []
  | cons : ∀ k v₁ v₂ v r₁ r₂ r, LubQualified v₁ v₂ v → LubRecord r₁ r₂ r →
      LubRecord ((k, v₁) :: r₁) ((k, v₂) :: r₂) ((k, v) :: r)
end


/-! ## The sum-and-tag encoding -/

/-- One index type for the whole SCC: the disjoint union of the three members' input tuples. -/
abbrev LIx (At Et Xt : Type) :=
  (CTy At Et Xt × CTy At Et Xt) ⊕ (QTy At Et Xt × QTy At Et Xt) ⊕ (RTy At Et Xt × RTy At Et Xt)

/-- One output type for the whole SCC. This is the sum `Body.call` forces: `call i k` hands `k` the
rule set's single `α`, so a family whose members produce different things must tag. -/
abbrev LOut (At Et Xt : Type) :=
  CTy At Et Xt ⊕ QTy At Et Xt ⊕ RTy At Et Xt

variable [DecidableEq At] [DecidableEq Et] [DecidableEq Xt]

def lBoolSame : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.bool b₁, .bool b₂) => .cond (decide (b₁ = b₂)) (b₁ = b₂) (.ret (.inl (.bool b₂)))
  | _ => .fail

def lBoolDiff : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.bool b₁, .bool b₂) =>
      .cond (decide (b₁ ≠ b₂)) (BoolTypeNeq b₁ b₂) (.ret (.inl (.bool .anyBool)))
  | _ => .fail

def lInt : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.int, .int) => .ret (.inl .int)
  | _ => .fail

def lString : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.string, .string) => .ret (.inl .string)
  | _ => .fail

def lEntity : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.entity e₁, .entity e₂) => .cond (decide (e₁ = e₂)) (e₁ = e₂) (.ret (.inl (.entity e₂)))
  | _ => .fail

def lExt : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.ext x₁, .ext x₂) => .cond (decide (x₁ = x₂)) (x₁ = x₂) (.ret (.inl (.ext x₂)))
  | _ => .fail

/-- `Lub.set`: a same-member recursive `call`, so the tag test on the result can never fail — and the
framework still makes you write it. -/
def lSet : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.set s₁, .set s₂) =>
      .pay (.call (.inl (s₁, s₂)) fun a =>
        match a with
        | .inl s => .ret (.inl (.set s))
        | _ => .fail)
  | _ => .fail

/-- `Lub.record`: a **cross-member** `call` into `LubRecord`, and the tag test is where the encoding's
cost shows up. -/
def lRecord : CTy At Et Xt × CTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.record r₁, .record r₂) =>
      .pay (.call (.inr (.inr (r₁, r₂))) fun a =>
        match a with
        | .inr (.inr r) => .ret (.inl (.record r))
        | _ => .fail)
  | _ => .fail

def lqOpt : QTy At Et Xt × QTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.optional t₁, .optional t₂) =>
      .pay (.call (.inl (t₁, t₂)) fun a =>
        match a with
        | .inl t => .ret (.inr (.inl (.optional t)))
        | _ => .fail)
  | _ => .fail

def lqReq : QTy At Et Xt × QTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | (.required t₁, .required t₂) =>
      .pay (.call (.inl (t₁, t₂)) fun a =>
        match a with
        | .inl t => .ret (.inr (.inl (.required t)))
        | _ => .fail)
  | _ => .fail

def lrNil : RTy At Et Xt × RTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | ([], []) => .ret (.inr (.inr []))
  | _ => .fail

/-- `LubRecord.cons`: two `call`s, one to each of the other two members, nested. -/
def lrCons : RTy At Et Xt × RTy At Et Xt → Body (LIx At Et Xt) (LOut At Et Xt)
  | ((k₁, v₁) :: r₁, (k₂, v₂) :: r₂) =>
      .cond (decide (k₁ = k₂)) (k₁ = k₂)
        (.pay (.call (.inr (.inl (v₁, v₂))) fun a =>
          match a with
          | .inr (.inl v) =>
              .call (.inr (.inr (r₁, r₂))) fun b =>
                match b with
                | .inr (.inr r) => .ret (.inr (.inr ((k₂, v) :: r)))
                | _ => .fail
          | _ => .fail))
  | _ => .fail

/-- One `RuleSet` for the whole family: the index's tag selects which member's constructors apply. -/
def lRules : RuleSet (LIx At Et Xt) (LOut At Et Xt)
  | .inl p => [lBoolSame p, lBoolDiff p, lInt p, lString p, lEntity p, lExt p, lSet p, lRecord p]
  | .inr (.inl p) => [lqOpt p, lqReq p]
  | .inr (.inr p) => [lrNil p, lrCons p]

/-- The tagged relation. The off-diagonal `False` is what makes `hvalid` able to rule out a
wrongly-tagged output: a body at a `.inl` index only ever `ret`s a `.inl`. -/
def LR : LIx At Et Xt → LOut At Et Xt → Prop
  | .inl (t₁, t₂), .inl t => Lub t₁ t₂ t
  | .inr (.inl (q₁, q₂)), .inr (.inl q) => LubQualified q₁ q₂ q
  | .inr (.inr (r₁, r₂)), .inr (.inr r) => LubRecord r₁ r₂ r
  | _, _ => False

theorem boolTypeNeq_iff (b₁ b₂ : BoolTy) : BoolTypeNeq b₁ b₂ ↔ b₁ ≠ b₂ := by
  constructor
  · intro h; cases h <;> simp
  · intro h; cases b₁ <;> cases b₂ <;> first | exact absurd rfl h | constructor

/-! ## The four obligations -/

theorem hsound : ∀ i, ∀ b ∈ lRules (At := At) (Et := Et) (Xt := Xt) i, BodySound b := by
  intro i b hb
  match i with
  | .inl (t₁, t₂) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold lBoolSame; split
        · exact ⟨fun h => of_decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lBoolDiff; split
        · rename_i b₁ b₂ _
          exact ⟨fun h => (boolTypeNeq_iff b₁ b₂).mpr (of_decide_eq_true h), trivial⟩
        · exact trivial
      · unfold lInt; split <;> exact trivial
      · unfold lString; split <;> exact trivial
      · unfold lEntity; split
        · exact ⟨fun h => of_decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lExt; split
        · exact ⟨fun h => of_decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lSet; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
      · unfold lRecord; split
        · exact fun a => by rcases a with _ | (_ | _) <;> exact trivial
        · exact trivial
  | .inr (.inl (q₁, q₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · unfold lqOpt; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
      · unfold lqReq; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
  | .inr (.inr (r₁, r₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · unfold lrNil; split <;> exact trivial
      · unfold lrCons; split
        · refine ⟨fun h => of_decide_eq_true h, fun a => ?_⟩
          rcases a with _ | (_ | _)
          · exact trivial
          · exact fun b => by rcases b with _ | (_ | _) <;> exact trivial
          · exact trivial
        · exact trivial


/-- `BodyComplete` is the mirror image, and — the point of the family — **not one `aux` premise
appears**, so `Covers`/`Unsized`/`MonoL` are never mentioned. This SCC is pure recursion; §3–§7's two
relations were pure leaves. -/
theorem hcomplete : ∀ i, ∀ b ∈ lRules (At := At) (Et := Et) (Xt := Xt) i, BodyComplete b := by
  intro i b hb
  match i with
  | .inl (t₁, t₂) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold lBoolSame; split
        · exact ⟨fun h => decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lBoolDiff; split
        · rename_i b₁ b₂ _
          exact ⟨fun h => decide_eq_true ((boolTypeNeq_iff b₁ b₂).mp h), trivial⟩
        · exact trivial
      · unfold lInt; split <;> exact trivial
      · unfold lString; split <;> exact trivial
      · unfold lEntity; split
        · exact ⟨fun h => decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lExt; split
        · exact ⟨fun h => decide_eq_true h, trivial⟩
        · exact trivial
      · unfold lSet; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
      · unfold lRecord; split
        · exact fun a => by rcases a with _ | (_ | _) <;> exact trivial
        · exact trivial
  | .inr (.inl (q₁, q₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · unfold lqOpt; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
      · unfold lqReq; split
        · exact fun a => by cases a <;> exact trivial
        · exact trivial
  | .inr (.inr (r₁, r₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · unfold lrNil; split <;> exact trivial
      · unfold lrCons; split
        · refine ⟨fun h => decide_eq_true h, fun a => ?_⟩
          rcases a with _ | (_ | _)
          · exact trivial
          · exact fun b => by rcases b with _ | (_ | _) <;> exact trivial
          · exact trivial
        · exact trivial

/-- The rules are valid for the tagged relation. Every `fail` branch is killed by `simp only [HoldsR]`
turning the hypothesis into `False`, and every *wrongly tagged* `call` result is killed by `LR`'s
off-diagonal `False` — which is the sum encoding's one piece of good news: the junk the sum admits is
excluded by the relation, not by extra side conditions in the bodies. -/
theorem hvalid : ∀ i, ∀ b ∈ lRules (At := At) (Et := Et) (Xt := Xt) i, ∀ o,
    HoldsR LR b o → LR i o := by
  intro i b hb o h
  match i with
  | .inl (t₁, t₂) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · cases t₁ <;> cases t₂ <;> simp only [lBoolSame, HoldsR] at h
        obtain ⟨rfl, rfl⟩ := h; exact Lub.boolSame _
      · cases t₁ <;> cases t₂ <;> simp only [lBoolDiff, HoldsR] at h
        obtain ⟨hne, rfl⟩ := h; exact Lub.boolDiff _ _ hne
      · cases t₁ <;> cases t₂ <;> simp only [lInt, HoldsR] at h
        subst h; exact Lub.int
      · cases t₁ <;> cases t₂ <;> simp only [lString, HoldsR] at h
        subst h; exact Lub.string
      · cases t₁ <;> cases t₂ <;> simp only [lEntity, HoldsR] at h
        obtain ⟨rfl, rfl⟩ := h; exact Lub.entity _
      · cases t₁ <;> cases t₂ <;> simp only [lExt, HoldsR] at h
        obtain ⟨rfl, rfl⟩ := h; exact Lub.ext _
      · cases t₁ <;> cases t₂ <;> simp only [lSet, HoldsR] at h
        obtain ⟨x, hx, hk⟩ := h
        rcases x with s | (_ | _) <;> simp only [HoldsR] at hk
        subst hk; exact Lub.set _ _ _ hx
      · cases t₁ <;> cases t₂ <;> simp only [lRecord, HoldsR] at h
        obtain ⟨x, hx, hk⟩ := h
        rcases x with _ | (_ | r) <;> simp only [HoldsR] at hk
        subst hk; exact Lub.record _ _ _ hx
  | .inr (.inl (q₁, q₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · cases q₁ <;> cases q₂ <;> simp only [lqOpt, HoldsR] at h
        obtain ⟨x, hx, hk⟩ := h
        rcases x with t | (_ | _) <;> simp only [HoldsR] at hk
        subst hk; exact LubQualified.optional _ _ _ hx
      · cases q₁ <;> cases q₂ <;> simp only [lqReq, HoldsR] at h
        obtain ⟨x, hx, hk⟩ := h
        rcases x with t | (_ | _) <;> simp only [HoldsR] at hk
        subst hk; exact LubQualified.required _ _ _ hx
  | .inr (.inr (rr₁, rr₂)) =>
      simp only [lRules, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · cases rr₁ <;> cases rr₂ <;> simp only [lrNil, HoldsR] at h
        subst h; exact LubRecord.nil
      · match rr₁, rr₂ with
        | [], _ => simp only [lrCons, HoldsR] at h
        | _ :: _, [] => simp only [lrCons, HoldsR] at h
        | (k₁, v₁) :: r₁, (k₂, v₂) :: r₂ =>
            simp only [lrCons, HoldsR] at h
            obtain ⟨rfl, x, hx, hk⟩ := h
            rcases x with _ | (v | _) <;> simp only [HoldsR] at hk
            obtain ⟨y, hy, hk⟩ := hk
            rcases y with _ | (_ | r) <;> simp only [HoldsR] at hk
            subst hk; exact LubRecord.cons _ _ _ _ _ _ _ hx hy

/-! ### `hgen`: the direction that needs the family's own mutual recursor

One `Derives`-construction lemma per constructor, then the *same twelve* handed to `Lub.rec`,
`LubQualified.rec` and `LubRecord.rec` in turn. This is the sum encoding's real cost: the generic
theorem is stated for one relation, so "the rules generate `R`" has to be re-assembled from a
three-motive induction by hand. -/

private def M1 : ∀ (a b c : CTy At Et Xt), Lub a b c → Prop :=
  fun a b c _ => Derives lRules (.inl (a, b)) (.inl c)
private def M2 : ∀ (a b c : QTy At Et Xt), LubQualified a b c → Prop :=
  fun a b c _ => Derives lRules (.inr (.inl (a, b))) (.inr (.inl c))
private def M3 : ∀ (a b c : RTy At Et Xt), LubRecord a b c → Prop :=
  fun a b c _ => Derives lRules (.inr (.inr (a, b))) (.inr (.inr c))

private theorem cBoolSame (b : BoolTy) :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt))
      (.inl (.bool b, .bool b)) (.inl (.bool b)) :=
  Derives.intro (b := lBoolSame ((.bool b : CTy At Et Xt), .bool b)) (by simp [lRules])
    (by unfold lBoolSame; exact .cond rfl (.ret _))

private theorem cBoolDiff (b₁ b₂ : BoolTy) (hne : BoolTypeNeq b₁ b₂) :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt))
      (.inl (.bool b₁, .bool b₂)) (.inl (.bool .anyBool)) :=
  Derives.intro (b := lBoolDiff ((.bool b₁ : CTy At Et Xt), .bool b₂)) (by simp [lRules])
    (by unfold lBoolDiff; exact .cond hne (.ret _))

private theorem cInt :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt)) (.inl (.int, .int)) (.inl .int) :=
  Derives.intro (b := lInt ((.int : CTy At Et Xt), .int)) (by simp [lRules])
    (by unfold lInt; exact .ret _)

private theorem cString :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt)) (.inl (.string, .string)) (.inl .string) :=
  Derives.intro (b := lString ((.string : CTy At Et Xt), .string)) (by simp [lRules])
    (by unfold lString; exact .ret _)

private theorem cEntity (e : Et) :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt))
      (.inl (.entity e, .entity e)) (.inl (.entity e)) :=
  Derives.intro (b := lEntity ((.entity e : CTy At Et Xt), .entity e)) (by simp [lRules])
    (by unfold lEntity; exact .cond rfl (.ret _))

private theorem cExt (x : Xt) :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt))
      (.inl (.ext x, .ext x)) (.inl (.ext x)) :=
  Derives.intro (b := lExt ((.ext x : CTy At Et Xt), .ext x)) (by simp [lRules])
    (by unfold lExt; exact .cond rfl (.ret _))

private theorem cSet (s₁ s₂ s : CTy At Et Xt) (_ : Lub s₁ s₂ s)
    (ih : Derives lRules (.inl (s₁, s₂)) (.inl s)) :
    Derives lRules (.inl ((.set s₁ : CTy At Et Xt), .set s₂)) (.inl (.set s)) :=
  Derives.intro (b := lSet ((.set s₁ : CTy At Et Xt), .set s₂)) (by simp [lRules])
    (by unfold lSet; exact .pay (.call ih (.ret _)))

private theorem cRecord (r₁ r₂ r : RTy At Et Xt) (_ : LubRecord r₁ r₂ r)
    (ih : Derives lRules (.inr (.inr (r₁, r₂))) (.inr (.inr r))) :
    Derives lRules (.inl ((.record r₁ : CTy At Et Xt), .record r₂)) (.inl (.record r)) :=
  Derives.intro (b := lRecord ((.record r₁ : CTy At Et Xt), .record r₂)) (by simp [lRules])
    (by unfold lRecord; exact .pay (.call ih (.ret _)))

private theorem cOpt (t₁ t₂ t : CTy At Et Xt) (_ : Lub t₁ t₂ t)
    (ih : Derives lRules (.inl (t₁, t₂)) (.inl t)) :
    Derives lRules (.inr (.inl ((.optional t₁ : QTy At Et Xt), .optional t₂)))
      (.inr (.inl (.optional t))) :=
  Derives.intro (b := lqOpt ((.optional t₁ : QTy At Et Xt), .optional t₂)) (by simp [lRules])
    (by unfold lqOpt; exact .pay (.call ih (.ret _)))

private theorem cReq (t₁ t₂ t : CTy At Et Xt) (_ : Lub t₁ t₂ t)
    (ih : Derives lRules (.inl (t₁, t₂)) (.inl t)) :
    Derives lRules (.inr (.inl ((.required t₁ : QTy At Et Xt), .required t₂)))
      (.inr (.inl (.required t))) :=
  Derives.intro (b := lqReq ((.required t₁ : QTy At Et Xt), .required t₂)) (by simp [lRules])
    (by unfold lqReq; exact .pay (.call ih (.ret _)))

private theorem cNil :
    Derives (lRules (At := At) (Et := Et) (Xt := Xt))
      (.inr (.inr ([], []))) (.inr (.inr [])) :=
  Derives.intro (b := lrNil (([] : RTy At Et Xt), [])) (by simp [lRules])
    (by unfold lrNil; exact .ret _)

private theorem cCons (k : At) (v₁ v₂ v : QTy At Et Xt) (r₁ r₂ r : RTy At Et Xt)
    (_ : LubQualified v₁ v₂ v) (_ : LubRecord r₁ r₂ r)
    (ihv : Derives lRules (.inr (.inl (v₁, v₂))) (.inr (.inl v)))
    (ihr : Derives lRules (.inr (.inr (r₁, r₂))) (.inr (.inr r))) :
    Derives lRules (.inr (.inr (((k, v₁) :: r₁ : RTy At Et Xt), (k, v₂) :: r₂)))
      (.inr (.inr ((k, v) :: r))) :=
  Derives.intro (b := lrCons (((k, v₁) :: r₁ : RTy At Et Xt), (k, v₂) :: r₂)) (by simp [lRules])
    (by unfold lrCons; exact .cond rfl (.pay (.call ihv (.call ihr (.ret _)))))

theorem hgenLub : ∀ {a b c : CTy At Et Xt}, Lub a b c → Derives lRules (.inl (a, b)) (.inl c) :=
  fun h => Lub.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3)
    (fun b => cBoolSame b) (fun b₁ b₂ hne => cBoolDiff b₁ b₂ hne) cInt cString
    (fun e => cEntity e) (fun x => cExt x) cSet cRecord cOpt cReq cNil cCons h

theorem hgenQ : ∀ {a b c : QTy At Et Xt},
    LubQualified a b c → Derives lRules (.inr (.inl (a, b))) (.inr (.inl c)) :=
  fun h => LubQualified.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3)
    (fun b => cBoolSame b) (fun b₁ b₂ hne => cBoolDiff b₁ b₂ hne) cInt cString
    (fun e => cEntity e) (fun x => cExt x) cSet cRecord cOpt cReq cNil cCons h

theorem hgenR : ∀ {a b c : RTy At Et Xt},
    LubRecord a b c → Derives lRules (.inr (.inr (a, b))) (.inr (.inr c)) :=
  fun h => LubRecord.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3)
    (fun b => cBoolSame b) (fun b₁ b₂ hne => cBoolDiff b₁ b₂ hne) cInt cString
    (fun e => cEntity e) (fun x => cExt x) cSet cRecord cOpt cReq cNil cCons h

/-- …and the three legs reassembled into the single hypothesis `adequate` asks for. -/
theorem hgen : ∀ (i : LIx At Et Xt) (o : LOut At Et Xt), LR i o → Derives lRules i o := by
  intro i o h
  match i, o with
  | .inl (t₁, t₂), .inl t => exact hgenLub h
  | .inr (.inl (q₁, q₂)), .inr (.inl q) => exact hgenQ h
  | .inr (.inr (r₁, r₂)), .inr (.inr r) => exact hgenR h
  | .inl _, .inr _ | .inr (.inl _), .inl _ | .inr (.inl _), .inr (.inr _)
  | .inr (.inr _), .inl _ | .inr (.inr _), .inr (.inl _) => exact h.elim

/-! ## The payoff: three adequacy theorems from one `RuleSet` -/

theorem lub_adequate (t₁ t₂ t : CTy At Et Xt) :
    Lub t₁ t₂ t ↔ ∃ L l n, (Sum.inl t : LOut At Et Xt) ∈ enumL lRules L l (.inl (t₁, t₂)) n :=
  adequateL hsound hcomplete hvalid hgen (.inl (t₁, t₂)) (.inl t)

theorem lubQualified_adequate (q₁ q₂ q : QTy At Et Xt) :
    LubQualified q₁ q₂ q ↔
      ∃ L l n, (Sum.inr (Sum.inl q) : LOut At Et Xt) ∈
        enumL lRules L l (.inr (.inl (q₁, q₂))) n :=
  adequateL hsound hcomplete hvalid hgen (.inr (.inl (q₁, q₂))) (.inr (.inl q))

theorem lubRecord_adequate (r₁ r₂ r : RTy At Et Xt) :
    LubRecord r₁ r₂ r ↔
      ∃ L l n, (Sum.inr (Sum.inr r) : LOut At Et Xt) ∈
        enumL lRules L l (.inr (.inr (r₁, r₂))) n :=
  adequateL hsound hcomplete hvalid hgen (.inr (.inr (r₁, r₂))) (.inr (.inr r))


/-! ### §9b The family at run time

`Lub` is a *function* of its two inputs, so each enumeration below is single-valued; §8b's `twoR` is
where fan-out is measured. What is worth running here is the **level** and the **tags**. -/

namespace LubDemo

abbrev S := String
/-- `CedarType` with all three parameters at `String`. -/
abbrev CT := CTy S S S

/-- Two record types differing only in one attribute's `BoolType`. -/
def t1 : CT := .record [("a", .required (.bool .tt)), ("b", .optional .int)]
def t2 : CT := .record [("a", .required (.bool .ff)), ("b", .optional .int)]

-- The lub lands at level **5**, and 5 is the number of `pay`s on the whole *three-member* derivation:
-- `lRecord` (1) + `lrCons "a"` (1) + `lqReq` (1) + `lrCons "b"` (1) + `lqOpt` (1); the `Lub` steps on
-- `.bool`/`.int` and the closing `lrNil` charge nothing. So under sum-and-tag the level is a global
-- count across the SCC, not a per-member depth — see §10.
/-- info: [0, 0, 0, 0, 0, 1, 0] -/
#guard_msgs in
#eval ((List.range 7).map fun n => (enumL lRules 0 12 (Sum.inl (t1, t2) : LIx S S S) n).length)

-- …and it is the right answer: `tt ⊔ ff = anyBool`, `int ⊔ int = int`, keys preserved.
/--
info: [Sum.inl (CedarRule.LubFam.CTy.record
   [("a", CedarRule.Qualified.required (CedarRule.LubFam.CTy.bool (CedarRule.LubFam.BoolTy.anyBool))),
    ("b", CedarRule.Qualified.optional (CedarRule.LubFam.CTy.int))])]
-/
#guard_msgs in
#eval (enumL lRules 0 12 (Sum.inl (t1, t2) : LIx S S S) 5)

-- The sum admits junk — a `.inr` output at a `.inl` index is a well-typed inhabitant of `α` — but the
-- rules never emit it. Every output at every level carries the index's own tag.
/-- info: ["inl"] -/
#guard_msgs in
#eval ((List.range 7).flatMap fun n =>
  (enumL lRules 0 12 (Sum.inl (t1, t2) : LIx S S S) n).map fun o =>
    match o with | .inl _ => "inl" | .inr (.inl _) => "inrinl" | .inr (.inr _) => "inrinr")

-- The `LubRecord` member, queried directly: the *same* `RuleSet`, a different index tag. This is the
-- sub-goal `lRecord` reaches by a cross-member `call`.
/-- info: [0, 0, 1, 0, 0, 0, 0] -/
#guard_msgs in
#eval ((List.range 7).map fun n =>
  (enumL lRules 0 12 (Sum.inr (Sum.inr ([("a", Qualified.required (CTy.bool .tt))],
    [("a", Qualified.required (CTy.bool .ff))])) : LIx S S S) n).length)

/--
info: [Sum.inr (Sum.inr [("a", CedarRule.Qualified.required (CedarRule.LubFam.CTy.bool (CedarRule.LubFam.BoolTy.anyBool)))])]
-/
#guard_msgs in
#eval (enumL lRules 0 12 (Sum.inr (Sum.inr ([("a", Qualified.required (CTy.bool .tt))],
    [("a", Qualified.required (CTy.bool .ff))])) : LIx S S S) 2)

/-- And the adequacy theorem carries the run back to the relation. -/
theorem lub_t1_t2 : Lub t1 t2 (.record [("a", .required (.bool .anyBool)), ("b", .optional .int)]) :=
  (lub_adequate _ _ _).mpr ⟨0, 12, 5, by exact List.Mem.head _⟩

end LubDemo

end LubFam

end CedarRule

/-! # §10 What did not fit

The five questions the exercise was set up to answer, answered against what compiled above.

## `check` on a NEGATIVE premise (`¬ CapAttrMem`)

It works, and needs nothing the verdict algebra lacks: `Body.check` carries an arbitrary `Prop` and an
arbitrary `V`, so polarity lives entirely in `notCapVerdict` (`.no` exactly when the capability *is*
present). `hsound`/`hcomplete` discharge it from `capAttrMemB_iff`, which is Cedar's own decision
procedure (`DecOpt (CapAttrMem x a c)`, `TypeOfLean.lean:210`).

Two things *are* wrong, and neither is about polarity:

1. **`V` has three verdicts but adequacy admits two.** `BodySound` needs `v ≠ .no → P` and
   `BodyComplete` needs `P → v ≠ .no`; together `v ≠ .no ↔ P`. So `.inconclusive` is legal only where
   `P` provably holds, i.e. only where `.yes` would also have been legal. `V.inconclusive` carries no
   proof-relevant content in this framework — the K3 leg is exercised by `denote` and by nothing else.
   This is the file's `check discards the conclusiveness flag` caveat restated as a sharper claim: it
   is not that the flag is dropped, it is that the two obligations *force* decisiveness.
2. **`denote` keeps on `.inconclusive`, and that default is wrong-signed for a negative premise.** In
   the real deriver an inconclusive verdict is what "the sub-checker ran out of budget" produces, and
   the conventional safe reading of "keep it" is over-approximation. For `¬ CapAttrMem` the safe
   reading is the *opposite*: keeping an unknown means claiming the capability is absent, which
   `BodySound`'s `v ≠ .no → ¬ CapAttrMem` cannot justify. There is no "drop-on-unknown" verdict, so a
   stratified-negation premise over a relation that is only *semi*-decidable would be inexpressible
   soundly. `CapAttrMem` is a walk over a finite list, so it never goes inconclusive and the gap does
   not bite here — but it is a gap, and Cedar has negated premises elsewhere
   (`MapNotContainsKey`, `BoolTypeNeq`, `PrimNeq`) that are only decidable for the same reason.

## Discarded auxiliary outputs (`qty` / `ty`)

**The framework enumerates them, and cannot be told not to.** `BodyComplete` demands
`Unsized p P` (or `Covers p P`) for *every* `b` with `P b`, so if the premise's specification is
`fun qty => MapContains a qty rty` then the producer must list every such `qty` — there is no
`Body` constructor meaning "some witness exists, value irrelevant", and no way to weaken the
obligation to "at least one". §7's duplicate-key evaluation shows the cost: three copies of
`("name", tt, [])` where two are right.

The only available fix is to rewrite the *premise's own specification* to its existential closure and
give the producer the residual outputs — `hRules'` in §5b, adequate by the same generic theorem
(`hair_adequate'`). That is a hand transformation on the rule data, justified by nothing in the
framework; a deriver would have to perform it and no theorem here checks that it preserved meaning.
`HoldsR` happens to be insensitive to it (`∃ u : Unit, (∃ q, P q) ∧ …` and `∃ q, P q ∧ …` are
equivalent) but that equivalence is re-proved by hand in `hvalid'`/`hgen'`, not once and for all.

## `knownToExist`, a `Bool` input that prunes constructors

`cond`/`fail` cover it completely, and with no slack: `hReq`/`hOpt` use `.cond kn (kn = true)` and
`hNot` uses `.cond (!kn) (kn = false)`; the obligations are `t = true → c` and `c → t = true`, both
`Bool.not_eq_true'` at worst. `hCaps` is the interesting one — `found_in_caps` quantifies over
`knownToExist` and constrains it in no way, so the body simply *ignores* the input and no `cond`
appears. The three-way split (pinned true / pinned false / unconstrained) is expressible because the
index is available to every body.

What the framework does *not* give is any check that the four `cond`s are jointly exhaustive or
disjoint. Nothing would complain if a fifth rule pinned `kn = true` and duplicated `hReq`; the
`cond`-false branches are just empty unions.

## Two constructors with identical conclusions

**Nothing breaks, and nothing is said.** §7 shows `("name", tt, [])` listed twice at the same level,
from `found_in_caps` and `found_required_known`. The relational side is a `Prop`, so the multiplicity
is invisible there, and `adequate`/`adequateL` are *membership* statements
(`R i a ↔ ∃ l n, a ∈ enumL …`): they neither require nor forbid duplicates. So a count-graded
enumerator that must report 2 gets no support from this theorem — the theorem cannot distinguish
`hRules` (three copies on `rty2`) from `hRules'` (two copies), which is exactly what the two
`#guard_msgs` blocks demonstrate, both against the *same* `HasAttrInRecord`. Validating a `Cnt` leg
needs a statement about the number of `Holds` derivations, which is a different theorem: it would have
to count `Body` derivations rather than quantify over them, and — see the parent file's
`No Cnt leg` caveat — `bind`/`guard` have no count interpretation anyway.

## Cedar leaves are finite by construction

**Confirmed, and it is the single biggest difference from STLC.** `Map` is a raw association list and
`Capabilities` is a list, so every premise of both relations is a walk over a structure that is already
in hand: `schemaEnum`, `actionEnum`, `capAttrs`, `valsAt`, `anyEntry`, `reqEntries`, `optEntries`,
`hasKey`, `reqKeys`, `optKeys`, `anyKeys` are all `fun _ => <finite list>`. Consequently each satisfies
`Unsized` — the obligation the parent file *refutes* for STLC's `typeEnum` (`not_unsized_typeEnum`) —
so every premise here is graded `.flat`, the grading choice the whole framework exists to police is
never in doubt, and `Graded.pay` is the only thing that consumes level.

That helps in three concrete ways and hurts in one:

* `Attr = String` and `EntityType = Name` are *infinite*, but no producer ever draws from them: `a` is
  produced by walking `c` or `rty`, `ety` by walking `ets`/`acts`. This is precisely the design intent
  recorded in `TypeOfLean.lean`'s comments on `ValidDifferentEntityType` and `GetAttrInRecord`, and it
  is why `String` being infinite is irrelevant.
* Every solution appears at level 0 (§7's `[3, 0, 0, 0]`) — no body emits `pay`, because no premise
  recurses — so the branch-and-bound level discipline is doing no work at all for these two
  relations.
* `Unsized` being available means a mis-grading to `.sized` would still be *complete* here
  (`covers_of_unsized`), merely slower — the STLC counterexample has no analogue at a finite leaf. So
  these two relations cannot serve as a regression test for the bug the framework was built to catch.
* The hurt: because the producers are finite lists rather than level-indexed families, the *only*
  source of level is `pay`, and no body emits one, so all of `HasAttrInRecord` is a single level wide
  at level 0. Any size-based diversity in the generated attribute/type has to come from the recursive
  relations that *call* this one; nothing in this relation contributes gradation.

## `Body.call`, as exercised by §8 and §9

§3–§7 contain no `call` at all: neither `ValidDifferentEntityType` nor `HasAttrInRecord` recurses, so
the `bindC` leg of `denote` was never taken and the framework's most important constructor was
untested on Cedar. §8 (`AllLub`, a single recursive relation) and §9
(`Lub`/`LubQualified`/`LubRecord`, a mutual family under sum-and-tag) close that. The verdict:

**`call` was adequate to the job, in both shapes, with no change to any generic theorem.**
`adequate`/`adequateL` were instantiated four more times from the same four obligations, and `call`
contributes *nothing* to `BodySound` and only `∀ a, BodyComplete (k a)` to `BodyComplete` — which is
the design paying off: a recursive premise always carries its own size, so unlike `aux` there is no
grading choice to get wrong. Four things are worth recording.

1. **The recursive index may depend on an auxiliary output, and that costs nothing.** `AllLub.cons`
   reads `Lub acc hd lubTy → AllLub lubTy tl result`: the sub-goal is not known until the `aux`
   premise has committed. `Body`'s continuation-passing shape makes this free — `k : β → Body ι α`, so
   `.call (lubTy, tl)` is just a Lean term mentioning `lubTy`. No `Body` constructor, no obligation and
   no proof case is needed for it. This is the shape that makes *scheduling* hard, and the framework is
   silent about it: nothing in `BodyComplete` notices that a dead-end `lubTy` wastes the whole
   recursive subtree.
2. **The level a `call` derivation reaches is the number of `pay`s on its spine, and `bindC` accounts
   for it exactly.** §8b evaluates `AllLub maxR 0 [3,1,2]` at levels 0–5 and finds the unique answer at
   level 3 and nothing at 2 or 4; the prefixes land at 0/1/2. §9b's record lub lands at level 5, which
   is the `pay` count over the whole *three-member* derivation. So under sum-and-tag the level is a
   global count across the SCC rather than a per-member depth — correct, but it means a branch-and-bound
   budget for one member is implicitly a budget for the whole family.
3. **The iteration count `l` is a separate starvation axis from the leaf budget `L`.** §8b shows
   `l = 3` enumerating *nothing at any level* for a 3-element list, and `l = 4` the first that suffices
   (three `aCons` unfoldings plus the `aNil` that closes the recursion). `adequate` absorbs this with
   `∃ l`, and a real runner has to iterate it; for §3–§7 `l = 1` always sufficed and the axis was
   invisible.
4. **Multiplicity behaves as §"Two constructors with identical conclusions" predicts, now with
   recursion.** §8b's relational `twoR` gives `2^3 = 8` derivations of a 3-element list, all at one
   level, with two *duplicate* outputs (`10` and `24` each arise two ways). `bindC` convolves the
   auxiliary premise's level with the sub-derivation's, so fan-out costs multiplicity and not level,
   and the membership-only adequacy theorem still cannot see it.

## What the sum-and-tag encoding costs

The earlier draft of this section guessed that sum-and-tag "costs no new generic proof". §9 shows that
guess is **half right**: the generic theorems are untouched, but four things have to be built by hand,
and they are what will not scale to `TypeOfLean.lean`'s 46-relation families without a generator.

1. **A tag test in every `call` continuation, which is provably dead code.** `call i k` gives `k` the
   rule set's single `α`, so each of §9's six `call`s is followed by
   `match a with | .inr (.inr r) => … | _ => .fail`. `hvalid` proves the wrong tag never arrives — it
   is excluded by `LR`'s off-diagonal `False`, and §9b's third `#eval` confirms every output at a
   `.inl` index is `.inl`-tagged — but the framework cannot know that, so the deriver must emit the
   branch and the enumerator pays the match at run time. There is no `Body` constructor for "this call
   is at a member whose output type is `α₃`", i.e. no way to recover the per-member typing.
2. **`hgen` must be re-assembled from the family's own mutual recursor.** `adequate` asks for
   `∀ i a, R i a → Derives rules i a` at the *summed* index; the family's induction principle has three
   motives. §9 pays this as twelve `Derives`-construction lemmas (`cBoolSame` … `cCons`), three
   applications of `Lub.rec`/`LubQualified.rec`/`LubRecord.rec` with the same twelve arguments, and a
   six-case junk dispatch for the off-diagonal indices. It is mechanical and `O(constructors)`, but it
   is *not* one proof — and 46 relations is the reason this has to be generated rather than written.
3. **The tagged relation `LR` is a modelling obligation, not a derived object.** Its off-diagonal has
   to be `False` for `hvalid` to be provable, and nothing in the framework says so or checks it. A
   deriver emits `LR` too, and a wrong off-diagonal (say `True`) yields a rule set that is still sound
   and complete against a relation nobody wanted.
4. **`DecidableEq` does not survive the nesting, so `decide` is not available on `α`.** `CTy` nests
   through `List (At × Qualified (CTy …))` and Lean's `DecidableEq` deriving handler refuses it (Cedar's
   own `CedarType` nests through `Map` the same way). §9b's membership witness is therefore
   `List.Mem.head _` rather than `by decide`. Any tooling that wants `decide`-checked ground truth on a
   summed `α` has to supply `DecidableEq` by hand.

What §9 does *not* show is the encoding on a family with **`aux` premises as well as `call`s**. The
`Lub` family is pure recursion (no producer anywhere) and §3–§7 are pure leaves (no `call` anywhere);
the two halves of `Body` have each been exercised against Cedar, but not simultaneously in one SCC.
`HasType` itself — 40-odd constructors mixing recursive premises, cross-SCC checkers and leaf
generators — is the case that would test the interaction, and it is the next thing to try.

## The remaining gap

* **The transcription is the weak link.** `cedar-lean` depends on `specimen`, and `RuleShape` lives in
  `specimen`'s `SpecimenTest` library on an unlanded branch, so no single Lake project sees both. The
  relations here were copied by hand; the mitigation is that every Cedar type the relations do not
  inspect is a type *variable* (see the module docstring), so `ValidDifferentEntityType` and
  `HasAttrInRecord` below are strictly more general than Cedar's and instantiate to them. The residual
  risk is confined to the constructor lists of `Map`, `Qualified`, `Key`, `EntityUID` and the four
  relation bodies. Closing it properly means landing `RuleShape` in the `Specimen` library (not
  `SpecimenTest`) so `cedar-lean` can import it, at which point these instances can be restated
  against `CedarGen.Relational.Lean` directly. §8's `AllLub` reduces this risk further by leaving
  `Lub` a relation *variable*: only `AllLub`'s own two constructors are transcribed there. §9 raises it
  again — `CTy` and the twelve `Lub`-family constructors are copied by hand.
-/

/-! # Axiom audit -/

#print axioms CedarRule.VDET.vdet_adequate
#print axioms CedarRule.VDET.vdet_mem_adequate
#print axioms CedarRule.HAIR.hair_adequate
#print axioms CedarRule.HAIR.hair_mem_adequate
#print axioms CedarRule.HAIR.hair_adequate'
#print axioms CedarRule.HAIR.hair_mem_adequate'
#print axioms CedarRule.ALub.allLub_adequate
#print axioms CedarRule.ALub.allLub_mem_adequate
#print axioms CedarRule.ACallDemo.maxR_allLub_3
#print axioms CedarRule.LubFam.lub_adequate
#print axioms CedarRule.LubFam.lubQualified_adequate
#print axioms CedarRule.LubFam.lubRecord_adequate
#print axioms CedarRule.LubFam.LubDemo.lub_t1_t2

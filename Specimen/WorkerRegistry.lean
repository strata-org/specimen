import Specimen.Schedules

/-! The workers a derivation emitted: for each, its sort and the mode it produces. The derivation
records them as it declares them (`emitSpecComponents`), so that what is a derived worker, and of what
sort, is known without reading it off the worker's name. -/

open Lean

namespace Specimen

/-- Where a derived worker's instance is visible: everywhere, where a namespace is current or open (a
`scoped derive_mutual`), or in the file that derived it (`local`). -/
inductive WorkerVisibility where
  | global
  | scoped (ns : Name)
  | «local» (mod : Name)
  deriving Inhabited, BEq, Repr

/-- A derived worker: its sort, the relation and outputs of the mode it produces, and where its
instance is visible. -/
structure WorkerInfo where
  sort : Schedules.DeriveSort
  rel : Name
  outs : List Nat
  visibility : WorkerVisibility := .global
  deriving Inhabited

/-- The visibility of the instances a `derive_mutual` with attribute kind `kind` declares. -/
def WorkerVisibility.ofAttrKind (kind : AttributeKind) (currNs mainMod : Name) : WorkerVisibility :=
  match kind with
  | .global => .global
  | .scoped => .scoped currNs
  | .local => .local mainMod

/-- Whether an instance of this visibility is in scope with namespace `currNs` current, the namespaces
`opened` open, in module `mainMod`. -/
def WorkerVisibility.visibleIn (v : WorkerVisibility) (currNs : Name) (opened : List Name)
    (mainMod : Name) : Bool :=
  match v with
  | .global => true
  | .scoped ns => ns.isPrefixOf currNs || opened.contains ns
  | .local m => m == mainMod

initialize specimenWorkerExt : SimplePersistentEnvExtension (Name × WorkerInfo) (NameMap WorkerInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (w, i) => m.insert w i
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (w, i) => m.insert w i) m) {} }

/-- What the derivation recorded of `w`, if `w` is a derived worker. -/
def workerInfo? (env : Environment) (w : Name) : Option WorkerInfo :=
  (specimenWorkerExt.getState env).find? w

/-- Whether `w` is a derived worker, of one of `sorts` if given. -/
def isDerivedWorker (env : Environment) (w : Name) (sorts : List Schedules.DeriveSort := []) : Bool :=
  match workerInfo? env w with
  | some i => sorts.isEmpty || sorts.contains i.sort
  | none => false

/-- Every derived worker this module and its imports declare. -/
def derivedWorkers (env : Environment) : Array (Name × WorkerInfo) :=
  (specimenWorkerExt.getState env).foldl (fun acc w i => acc.push (w, i)) #[]

end Specimen

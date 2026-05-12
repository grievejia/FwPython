import FwPython.Common.Env
import FwPython.Common.Heap
import FwPython.Gradual.Checked.Core.Syntax

/-! ## Checked values -/

/-- A checked runtime value is an object reference. -/
inductive CheckedValue : Type where
  | objRef : Nat → CheckedValue
  deriving DecidableEq, Repr

/-! ## Checked heap objects -/
/-- Payload carried by a checked heap object. Ordinary objects have no extra data;
    bound-method objects capture a receiver OID and a checked method definition. -/
inductive CheckedObjectPayload : Type where
  | ordinary
  | boundMethod : Nat → CheckedMethod → CheckedObjectPayload
  deriving DecidableEq, Repr

/-- A checked heap object carries a class name and a payload. -/
structure CheckedHeapObject where
  className : Identifier
  payload : CheckedObjectPayload
  deriving DecidableEq, Repr

/-! ## Checked heap -/

/-- Checked object heap for the checked machine. -/
abbrev CheckedHeap := RuntimeHeap CheckedHeapObject

namespace CheckedHeap

abbrev heapMap (self : CheckedHeap) := RuntimeHeap.heapMap self
abbrev heapCounter (self : CheckedHeap) := RuntimeHeap.heapCounter self
abbrev alloc (self : CheckedHeap) (obj : CheckedHeapObject) : Nat × CheckedHeap :=
  RuntimeHeap.alloc self obj
abbrev lookup (self : CheckedHeap) (oid : Nat) : Option CheckedHeapObject :=
  RuntimeHeap.lookup self oid
abbrev IdsBounded (self : CheckedHeap) : Prop := RuntimeHeap.IdsBounded self

/-- The initial checked heap with pre-allocated constant objects:
    - `NONE` (oid 0, class `NoneType`)
    - `TRUE` (oid 1, class `Bool`)
    - `FALSE` (oid 2, class `Bool`) -/
def initial : CheckedHeap where
  heapMap := [(noneOid, ⟨noneClass, .ordinary⟩),
              (trueOid, ⟨boolClass, .ordinary⟩),
              (falseOid, ⟨boolClass, .ordinary⟩)]
  heapCounter := 3

end CheckedHeap

/-! ## Environment and result -/

/-- Checked variable environment: maps variable names to checked values. -/
abbrev CheckedEnv := NamedEnv CheckedValue

/-- Evaluation of a checked expression can result in success, blame, or
    a runtime error. The `runtimeError` constructor is part of the raw
    machine and is reachable on ill-typed inputs; for compiled well-typed
    programs `gradual_soundness_at` rules it out via
    `CheckedStateSafe.not_runtimeError`. -/
inductive CheckedResult : Type where
  | success : CheckedValue → CheckedResult
  | blame : Label → CheckedResult
  | runtimeError : String → CheckedResult
  deriving DecidableEq, Repr

/-! ## Enforcement -/

/-- The result of runtime type enforcement: either success with a value,
    or blame identifying the boundary responsible. -/
inductive EnforceResult : Type where
  | ok : CheckedValue → EnforceResult
  | blame : Label → EnforceResult
  deriving DecidableEq, Repr

/-- Runtime boundary enforcement relation. `EnforceValue ct heap v c labels r`
    holds when enforcing boundary contract `c` on value `v` (under class
    table `ct` and heap `heap`) with blame tree `labels` produces result `r`.

    The heap is read-only: enforcement does not allocate or mutate.
    Callable enforcement is shallow: invokable bound-method references pass
    unchanged and ordinary object references blame.
    The relation is partial: it is defined only when the heap and class table
    contain the objects and classes needed to evaluate the check. -/
inductive EnforceValue (ct : GClassTable) (heap : CheckedHeap) :
    (v : CheckedValue) → (c : BoundaryContract) → BoundaryLabels c → EnforceResult → Prop where

  /-- Unknown contract: any value passes (no-op boundary). -/
  | unknown : EnforceValue ct heap v .unknown labels (.ok v)

  /-- Bottom contract: no value passes. -/
  | bottom : EnforceValue ct heap v .bottom labels (.blame labels.direct)

  /-- An objRef passes class enforcement if its runtime class has the target
      in its MRO. -/
  | classObjRefOk :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∈ mro →
      EnforceValue ct heap (.objRef oid) (.class_ cname) labels (.ok (.objRef oid))

  /-- An objRef fails class enforcement if its runtime class does not have the
      target in its MRO. -/
  | classObjRefBlame :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∉ mro →
      EnforceValue ct heap (.objRef oid) (.class_ cname) labels (.blame labels.direct)

  /-- An objRef to a bound method passes callable enforcement unchanged. -/
  | callableObjRefTransparentOk :
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ →
      EnforceValue ct heap (.objRef oid) (.callable domC codC) labels
        (.ok (.objRef oid))

  /-- An objRef to an ordinary object fails callable enforcement. -/
  | callableObjRefBlame :
      heap.lookup oid = some ⟨cname, .ordinary⟩ →
      EnforceValue ct heap (.objRef oid) (.callable domC codC) labels (.blame labels.direct)

  /-- Union: left branch succeeds. -/
  | unionLeft :
      EnforceValue ct heap v T (labels.subtree (.unionLeft .here)) (.ok v') →
      EnforceValue ct heap v (.union T U) labels (.ok v')

  /-- Union: left blames, right succeeds. -/
  | unionRight :
      EnforceValue ct heap v T (labels.subtree (.unionLeft .here))
        (.blame (labels.subtree (.unionLeft .here)).direct) →
      EnforceValue ct heap v U (labels.subtree (.unionRight .here)) (.ok v') →
      EnforceValue ct heap v (.union T U) labels (.ok v')

  /-- Union: both branches blame. -/
  | unionBlame :
      EnforceValue ct heap v T (labels.subtree (.unionLeft .here))
        (.blame (labels.subtree (.unionLeft .here)).direct) →
      EnforceValue ct heap v U (labels.subtree (.unionRight .here))
        (.blame (labels.subtree (.unionRight .here)).direct) →
      EnforceValue ct heap v (.union T U) labels (.blame labels.direct)

  /-- Intersection: enforce T then U sequentially; both succeed. -/
  | intersectionOk :
      EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here)) (.ok v') →
      EnforceValue ct heap v' U (labels.subtree (.intersectionRight .here)) (.ok v'') →
      EnforceValue ct heap v (.intersection T U) labels (.ok v'')

  /-- Intersection: T blames. -/
  | intersectionBlameLeft :
      EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here))
        (.blame (labels.subtree (.intersectionLeft .here)).direct) →
      EnforceValue ct heap v (.intersection T U) labels (.blame labels.direct)

  /-- Intersection: T succeeds but U blames. -/
  | intersectionBlameRight :
      EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here)) (.ok v') →
      EnforceValue ct heap v' U (labels.subtree (.intersectionRight .here))
        (.blame (labels.subtree (.intersectionRight .here)).direct) →
      EnforceValue ct heap v (.intersection T U) labels (.blame labels.direct)

  /-- Class negation: objRef passes when its runtime class MRO does
      not contain the target. -/
  | negClassObjRefOk :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∉ mro →
      EnforceValue ct heap (.objRef oid) (.negClass cname) labels (.ok (.objRef oid))

  /-- Class negation: objRef blames when its runtime class MRO contains
      the target. -/
  | negClassObjRefBlame :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∈ mro →
      EnforceValue ct heap (.objRef oid) (.negClass cname) labels (.blame labels.direct)

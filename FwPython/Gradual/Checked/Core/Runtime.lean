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

/-- Runtime operation that created a checked-machine blame signal. -/
inductive BlameCause : Type where
  /-- `boundary value target` records the value rejected by the runtime boundary
      and the checked target whose compiled contract failed. -/
  | boundary :
      (value : CheckedValue) →
      (target : CheckedTarget) →
      BlameCause
  /-- `missingAttribute value attrName` records the receiver value whose dynamic
      method lookup failed and the requested attribute name. -/
  | missingAttribute :
      (receiver : CheckedValue) →
      (attributeName : Identifier) →
      BlameCause
  /-- `methodParameter value method` records the explicit argument rejected by
      the resolved checked method's parameter boundary and the checked method
      that supplied that boundary. -/
  | methodParameter :
      (argument : CheckedValue) →
      (method : CheckedMethod) →
      BlameCause
  deriving DecidableEq, Repr

/-- Blame payload preserved by the checked machine after blame is raised. -/
structure BlameInfo where
  /-- Source obligation reported for this blame. -/
  obligation : SourceObligation
  /-- Runtime operation and value/context that created the blame signal. -/
  cause : BlameCause
  deriving DecidableEq, Repr

/-- Evaluation of a checked expression can result in success, blame, or
    a runtime error. The `runtimeError` constructor is part of the raw
    machine and is reachable on ill-typed inputs; for compiled well-typed
    programs `gradual_soundness_at` rules it out via
    `CheckedStateSafe.not_runtimeError`. -/
inductive CheckedResult : Type where
  | success : CheckedValue → CheckedResult
  | blame : BlameInfo → CheckedResult
  | runtimeError : String → CheckedResult
  deriving DecidableEq, Repr

/-! ## Enforcement -/

/-- The result of runtime type enforcement. -/
inductive EnforceResult : Type where
  /-- The current value satisfies the contract and is returned unchanged by the machine. -/
  | ok : EnforceResult
  /-- Contract enforcement rejected the current value; the machine supplies source meaning. -/
  | blame : EnforceResult
  deriving DecidableEq, Repr

/-- Runtime boundary enforcement relation. `EnforceValue ct heap v c r` means
    checking value `v` against boundary contract `c` in class table `ct` and
    heap `heap` produces contract-only outcome `r`; on `.ok` the machine keeps
    `v` unchanged, and on `.blame` the machine supplies source obligation and
    runtime cause from the current frame or method.

    The heap is read-only: enforcement does not allocate or mutate.
    Callable enforcement is shallow: invokable bound-method references pass
    unchanged and ordinary object references blame.
    The relation is partial: it is defined only when the heap and class table
    contain the objects and classes needed to evaluate the check. -/
inductive EnforceValue (ct : GClassTable) (heap : CheckedHeap) :
    CheckedValue → BoundaryContract → EnforceResult → Prop where

  /-- Unknown contract: any value passes (no-op boundary). -/
  | unknown : EnforceValue ct heap v .unknown .ok

  /-- Bottom contract: no value passes. -/
  | bottom : EnforceValue ct heap v .bottom .blame

  /-- An objRef passes class enforcement if its runtime class has the target
      in its MRO. -/
  | classObjRefOk :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∈ mro →
      EnforceValue ct heap (.objRef oid) (.class_ cname) .ok

  /-- An objRef fails class enforcement if its runtime class does not have the
      target in its MRO. -/
  | classObjRefBlame :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∉ mro →
      EnforceValue ct heap (.objRef oid) (.class_ cname) .blame

  /-- An objRef to a bound method passes callable enforcement unchanged. -/
  | callableObjRefTransparentOk :
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ →
      EnforceValue ct heap (.objRef oid) (.callable domC codC) .ok

  /-- An objRef to an ordinary object fails callable enforcement. -/
  | callableObjRefBlame :
      heap.lookup oid = some ⟨cname, .ordinary⟩ →
      EnforceValue ct heap (.objRef oid) (.callable domC codC) .blame

  /-- Union: left branch succeeds. -/
  | unionLeft :
      EnforceValue ct heap v T .ok →
      EnforceValue ct heap v (.union T U) .ok

  /-- Union: left blames, right succeeds. -/
  | unionRight :
      EnforceValue ct heap v T .blame →
      EnforceValue ct heap v U .ok →
      EnforceValue ct heap v (.union T U) .ok

  /-- Union: both branches blame. -/
  | unionBlame :
      EnforceValue ct heap v T .blame →
      EnforceValue ct heap v U .blame →
      EnforceValue ct heap v (.union T U) .blame

  /-- Intersection: both sides accept the same current value. -/
  | intersectionOk :
      EnforceValue ct heap v T .ok →
      EnforceValue ct heap v U .ok →
      EnforceValue ct heap v (.intersection T U) .ok

  /-- Intersection: T blames. -/
  | intersectionBlameLeft :
      EnforceValue ct heap v T .blame →
      EnforceValue ct heap v (.intersection T U) .blame

  /-- Intersection: T succeeds but U blames on the same current value. -/
  | intersectionBlameRight :
      EnforceValue ct heap v T .ok →
      EnforceValue ct heap v U .blame →
      EnforceValue ct heap v (.intersection T U) .blame

  /-- Class negation: objRef passes when its runtime class MRO does
      not contain the target. -/
  | negClassObjRefOk :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∉ mro →
      EnforceValue ct heap (.objRef oid) (.negClass cname) .ok

  /-- Class negation: objRef blames when its runtime class MRO contains
      the target. -/
  | negClassObjRefBlame :
      heap.lookup oid = some obj →
      findGClass ct obj.className = some cls →
      GComputeMro ct cls mro →
      cname ∈ mro →
      EnforceValue ct heap (.objRef oid) (.negClass cname) .blame

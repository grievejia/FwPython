import FwPython.Gradual

/-! # EnforceValue Regression Examples

Concrete derivations exercising contract-only enforcement outcomes.
-/

variable {ct : GClassTable} {heap : CheckedHeap}

/-! ## unknown / bottom -/

/-- Enforcement against `unknown` always succeeds. -/
example : EnforceValue ct heap v .unknown .ok :=
  .unknown

/-- Enforcement against `bottom` always blames. -/
example : EnforceValue ct heap v .bottom .blame :=
  .bottom

/-! ## class enforcement -/

/-- An objRef passes class enforcement when its class has the target in MRO. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hmem : cname ∈ mro) :
    EnforceValue ct heap (.objRef oid) (.class_ cname) .ok :=
  .classObjRefOk hlook hfind hmro hmem

/-- An objRef fails class enforcement when its class does not have the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hnotmem : cname ∉ mro) :
    EnforceValue ct heap (.objRef oid) (.class_ cname) .blame :=
  .classObjRefBlame hlook hfind hmro hnotmem

/-! ## callable enforcement (shallow) -/

/-- Enforcing `callable domC codC` on a bound-method object reference succeeds. -/
example
    (hlook : heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩) :
    EnforceValue ct heap (.objRef oid) (.callable domC codC) .ok :=
  .callableObjRefTransparentOk hlook

/-- Enforcing `callable domC codC` on an ordinary object blames. -/
example
    (hlook : heap.lookup oid = some ⟨cname, .ordinary⟩) :
    EnforceValue ct heap (.objRef oid) (.callable domC codC) .blame :=
  .callableObjRefBlame hlook

/-! ## union enforcement -/

/-- Union: left branch succeeds. -/
example
    (hT : EnforceValue ct heap v T .ok) :
    EnforceValue ct heap v (.union T U) .ok :=
  .unionLeft hT

/-- Union: left blames, right succeeds. -/
example
    (hT : EnforceValue ct heap v T .blame)
    (hU : EnforceValue ct heap v U .ok) :
    EnforceValue ct heap v (.union T U) .ok :=
  .unionRight hT hU

/-- Union: both branches blame. -/
example
    (hT : EnforceValue ct heap v T .blame)
    (hU : EnforceValue ct heap v U .blame) :
    EnforceValue ct heap v (.union T U) .blame :=
  .unionBlame hT hU

/-! ## intersection enforcement -/

/-- Intersection: both branches accept the current value. -/
example
    (hT : EnforceValue ct heap v T .ok)
    (hU : EnforceValue ct heap v U .ok) :
    EnforceValue ct heap v (.intersection T U) .ok :=
  .intersectionOk hT hU

/-- Intersection: left branch blames. -/
example
    (hT : EnforceValue ct heap v T .blame) :
    EnforceValue ct heap v (.intersection T U) .blame :=
  .intersectionBlameLeft hT

/-- Intersection: left succeeds but right blames. -/
example
    (hT : EnforceValue ct heap v T .ok)
    (hU : EnforceValue ct heap v U .blame) :
    EnforceValue ct heap v (.intersection T U) .blame :=
  .intersectionBlameRight hT hU

/-! ## negClass enforcement -/

/-- Class negation passes when the runtime class MRO does not contain the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hnmem : cname ∉ mro) :
    EnforceValue ct heap (.objRef oid) (.negClass cname) .ok :=
  .negClassObjRefOk hlook hfind hmro hnmem

/-- Class negation blames when the runtime class MRO contains the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hmem : cname ∈ mro) :
    EnforceValue ct heap (.objRef oid) (.negClass cname) .blame :=
  .negClassObjRefBlame hlook hfind hmro hmem

/-! ## determinism regression -/

/-- Determinism: two derivations for the same inputs yield the same result. -/
example
    (h1 : EnforceValue ct heap v T r₁)
    (h2 : EnforceValue ct heap v T r₂) :
    r₁ = r₂ :=
  enforceValue_deterministic h1 h2

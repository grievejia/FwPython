import FwPython.Gradual.Checked.Enforce

/-! # EnforceValue Regression Examples

Concrete derivations exercising each enforcement case under the
shallow-callable encoding: base cases (`unknown`/`bottom`), class
enforcement on object references, transparent callable enforcement, and the
union/intersection/negation cases. Bound-method references pass through
`callable` checks unchanged; enforcement does not construct wrappers. -/

/-! ## Setup: a small class table and heap -/

variable {ct : GClassTable} {heap : CheckedHeap}

/-! ## unknown / bottom -/

/-- Enforcement against `unknown` always succeeds, preserving the value. -/
example : EnforceValue ct heap v .unknown ℓ (.ok v) :=
  .unknown

/-- Enforcement against `bottom` always blames. -/
example : EnforceValue ct heap v .bottom ℓ (.blame ℓ.direct) :=
  .bottom

/-! ## class enforcement -/

/-- An objRef passes class enforcement when its class has the target in MRO. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hmem : cname ∈ mro) :
    EnforceValue ct heap (.objRef oid) (.class_ cname) ℓ (.ok (.objRef oid)) :=
  .classObjRefOk hlook hfind hmro hmem

/-- An objRef fails class enforcement when its class doesn't have the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hnotmem : cname ∉ mro) :
    EnforceValue ct heap (.objRef oid) (.class_ cname) ℓ (.blame ℓ.direct) :=
  .classObjRefBlame hlook hfind hmro hnotmem

/-! ## callable enforcement (shallow) -/

/-- Enforcing `callable domC codC` on a bound-method object reference is
    transparent: the reference passes through unchanged. -/
example
    (hlook : heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩) :
    EnforceValue ct heap (.objRef oid) (.callable domC codC) ℓ (.ok (.objRef oid)) :=
  .callableObjRefTransparentOk hlook

/-- Enforcing `callable domC codC` on an ordinary object blames. -/
example
    (hlook : heap.lookup oid = some ⟨cname, .ordinary⟩) :
    EnforceValue ct heap (.objRef oid) (.callable domC codC) ℓ (.blame ℓ.direct) :=
  .callableObjRefBlame hlook

/-! ## union enforcement -/

/-- Union: left branch succeeds. -/
example
    (labels : BoundaryLabels (.union T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.unionLeft .here)) (.ok v')) :
    EnforceValue ct heap v (.union T U) labels (.ok v') :=
  .unionLeft hT

/-- Union: left blames, right succeeds. -/
example
    (labels : BoundaryLabels (.union T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.unionLeft .here))
      (.blame (labels.subtree (.unionLeft .here)).direct))
    (hU : EnforceValue ct heap v U (labels.subtree (.unionRight .here)) (.ok v')) :
    EnforceValue ct heap v (.union T U) labels (.ok v') :=
  .unionRight hT hU

/-- Union: both branches blame. -/
example
    (labels : BoundaryLabels (.union T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.unionLeft .here))
      (.blame (labels.subtree (.unionLeft .here)).direct))
    (hU : EnforceValue ct heap v U (labels.subtree (.unionRight .here))
      (.blame (labels.subtree (.unionRight .here)).direct)) :
    EnforceValue ct heap v (.union T U) labels (.blame labels.direct) :=
  .unionBlame hT hU

/-- Union with unknown on the left always succeeds. -/
example : EnforceValue ct heap v (.union .unknown T) ℓ (.ok v) :=
  .unionLeft .unknown

/-- Union with bottom on the left falls through to the right branch. -/
example
    (hT : EnforceValue ct heap v T (ℓ.subtree (.unionRight .here)) (.ok v')) :
    EnforceValue ct heap v (.union .bottom T) ℓ (.ok v') :=
  .unionRight .bottom hT

/-! ## intersection enforcement -/

/-- Intersection: both branches succeed sequentially. -/
example
    (labels : BoundaryLabels (.intersection T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here)) (.ok v'))
    (hU : EnforceValue ct heap v' U (labels.subtree (.intersectionRight .here)) (.ok v'')) :
    EnforceValue ct heap v (.intersection T U) labels (.ok v'') :=
  .intersectionOk hT hU

/-- Intersection: left branch blames, short-circuits. -/
example
    (labels : BoundaryLabels (.intersection T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here))
      (.blame (labels.subtree (.intersectionLeft .here)).direct)) :
    EnforceValue ct heap v (.intersection T U) labels (.blame labels.direct) :=
  .intersectionBlameLeft hT

/-- Intersection: left succeeds but right blames. -/
example
    (labels : BoundaryLabels (.intersection T U))
    (hT : EnforceValue ct heap v T (labels.subtree (.intersectionLeft .here)) (.ok v'))
    (hU : EnforceValue ct heap v' U (labels.subtree (.intersectionRight .here))
      (.blame (labels.subtree (.intersectionRight .here)).direct)) :
    EnforceValue ct heap v (.intersection T U) labels (.blame labels.direct) :=
  .intersectionBlameRight hT hU

/-- Intersection with `unknown` on the left: if the right succeeds, intersection succeeds. -/
example
    (hU : EnforceValue ct heap v U (ℓ.subtree (.intersectionRight .here)) (.ok v')) :
    EnforceValue ct heap v (.intersection .unknown U) ℓ (.ok v') :=
  .intersectionOk .unknown hU

/-- Intersection with `unknown` on the left: if the right blames, intersection blames. -/
example
    (hU : EnforceValue ct heap v U (ℓ.subtree (.intersectionRight .here))
      (.blame (ℓ.subtree (.intersectionRight .here)).direct)) :
    EnforceValue ct heap v (.intersection .unknown U) ℓ (.blame ℓ.direct) :=
  .intersectionBlameRight .unknown hU

/-! ## negClass enforcement (atomic class negation) -/

/-- Class negation on objRef: passes when the runtime class MRO does not
    contain the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hnmem : cname ∉ mro) :
    EnforceValue ct heap (.objRef oid) (.negClass cname) ℓ (.ok (.objRef oid)) :=
  .negClassObjRefOk hlook hfind hmro hnmem

/-- Class negation on objRef: blames when the runtime class MRO contains
    the target. -/
example
    (hlook : heap.lookup oid = some obj)
    (hfind : findGClass ct obj.className = some cls)
    (hmro : GComputeMro ct cls mro)
    (hmem : cname ∈ mro) :
    EnforceValue ct heap (.objRef oid) (.negClass cname) ℓ (.blame ℓ.direct) :=
  .negClassObjRefBlame hlook hfind hmro hmem

/-! ## intersection composition: callable then class -/

/-- Left-callable / right-class intersection on a bound-method reference: the
    callable check passes transparently and the class check then runs against
    the bound-method runtime class. -/
example
    (labels : BoundaryLabels (.intersection (.callable domC codC) (.class_ cname)))
    (hlook : heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩)
    (hfind : findGClass ct boundMethodClass = some cls)
    (hmro : GComputeMro ct cls mro)
    (hmem : cname ∈ mro) :
    EnforceValue ct heap (.objRef oid)
      (.intersection (.callable domC codC) (.class_ cname)) labels
      (.ok (.objRef oid)) :=
  .intersectionOk
    (.callableObjRefTransparentOk hlook)
    (.classObjRefOk hlook hfind hmro hmem)

/-- Left-negClass / right-callable intersection on a bound-method reference:
    the class negation succeeds (BoundMethod MRO excludes the target) and the
    callable check passes transparently. -/
example
    (labels : BoundaryLabels (.intersection (.negClass cname) (.callable domC codC)))
    (hlook : heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩)
    (hfind : findGClass ct boundMethodClass = some cls)
    (hmro : GComputeMro ct cls mro)
    (hnmem : cname ∉ mro) :
    EnforceValue ct heap (.objRef oid)
      (.intersection (.negClass cname) (.callable domC codC)) labels
      (.ok (.objRef oid)) :=
  .intersectionOk
    (.negClassObjRefOk hlook hfind hmro hnmem)
    (.callableObjRefTransparentOk hlook)

/-! ## determinism regression -/

/-- Determinism: two derivations for the same inputs yield the same result. -/
example
    (h1 : EnforceValue ct heap v T ℓ r₁)
    (h2 : EnforceValue ct heap v T ℓ r₂) :
    r₁ = r₂ :=
  enforceValue_deterministic h1 h2

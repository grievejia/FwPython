import FwPython.Gradual.Checked.Core

/-! ## Checked heap allocation lemmas -/

/-! ### Allocation lemmas -/

theorem checkedHeap_alloc_lookup_new
    {h : CheckedHeap} {newObj : CheckedHeapObject} {oid : Nat} {h' : CheckedHeap}
    (halloc : h.alloc newObj = (oid, h')) :
    h'.lookup oid = some newObj :=
  RuntimeHeap.alloc_lookup_new halloc

theorem checkedHeap_alloc_preserves_old
    {h : CheckedHeap} {newObj : CheckedHeapObject} {oidNew : Nat} {h' : CheckedHeap}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h'))
    {oid : Nat} {obj : CheckedHeapObject}
    (hlook : h.lookup oid = some obj) :
    h'.lookup oid = some obj :=
  RuntimeHeap.alloc_preserves_old hbounded halloc hlook

theorem lookup_checkedAlloc_of_lookup
    {h : CheckedHeap} {oid : Nat} {obj newObj : CheckedHeapObject}
    (hbounded : h.IdsBounded)
    (hlookup : h.lookup oid = some obj) :
    (h.alloc newObj).2.lookup oid = some obj :=
  RuntimeHeap.lookup_alloc_of_lookup hbounded hlookup

theorem checkedHeap_alloc_idsBounded
    {h : CheckedHeap} {newObj : CheckedHeapObject} {oidNew : Nat} {h' : CheckedHeap}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h')) :
    h'.IdsBounded :=
  RuntimeHeap.alloc_idsBounded hbounded halloc

theorem checkedHeap_alloc_preserves_bool_exhaustive
    {h : CheckedHeap} {newObj : CheckedHeapObject} {oidNew : Nat} {h' : CheckedHeap}
    (halloc : h.alloc newObj = (oidNew, h'))
    (hneBool : newObj.className ≠ boolClass)
    (honly : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid) :
    ∀ oid obj, h'.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid := by
  exact RuntimeHeap.alloc_preserves_property_exhaustive halloc hneBool honly

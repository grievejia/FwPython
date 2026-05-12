import FwPython.Static.Semantics.Core

/-! ## Heap allocation and payload lemmas -/

theorem lookup_alloc_of_lookup
    {h : Heap} {oid : Nat} {obj newObj : HeapObject}
    (hbounded : h.IdsBounded)
    (hlookup : h.lookup oid = some obj) :
    (h.alloc newObj).2.lookup oid = some obj :=
  RuntimeHeap.lookup_alloc_of_lookup hbounded hlookup

/-- Payload mismatch gives absurdity (bound method vs ordinary). -/
theorem payload_absurd
    {hp : Heap} {oid : Nat} {c₁ c₂ : Identifier} {r : Nat} {m : Method}
    (h1 : hp.lookup oid = some ⟨c₁, .boundMethod r m⟩)
    (h2 : hp.lookup oid = some ⟨c₂, .ordinary⟩) : False :=
  ObjectPayload.noConfusion (congrArg HeapObject.payload (Option.some.inj (h1.symm.trans h2)))

/-- Unify two bound-method payload lookups at the same OID. -/
theorem unify_payload
    {hp : Heap} {oid : Nat} {c₁ c₂ : Identifier}
    {r₁ r₂ : Nat} {m₁ m₂ : Method}
    (h1 : hp.lookup oid = some ⟨c₁, .boundMethod r₁ m₁⟩)
    (h2 : hp.lookup oid = some ⟨c₂, .boundMethod r₂ m₂⟩) :
    c₁ = c₂ ∧ r₁ = r₂ ∧ m₁ = m₂ := by
  obtain ⟨rfl, rfl, rfl⟩ := HeapObject.mk.inj (Option.some.inj (h1.symm.trans h2))
  exact ⟨rfl, rfl, rfl⟩

/-! ## Heap allocation helpers -/

theorem heap_alloc_lookup_new
    {h : Heap} {newObj : HeapObject} {oid : Nat} {h' : Heap}
    (halloc : h.alloc newObj = (oid, h')) :
    h'.lookup oid = some newObj :=
  RuntimeHeap.alloc_lookup_new halloc

theorem heap_alloc_preserves_old
    {h : Heap} {newObj : HeapObject} {oidNew : Nat} {h' : Heap}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h'))
    {oid : Nat} {obj : HeapObject}
    (hlook : h.lookup oid = some obj) :
    h'.lookup oid = some obj :=
  RuntimeHeap.alloc_preserves_old hbounded halloc hlook

theorem heap_alloc_idsBounded
    {h : Heap} {newObj : HeapObject} {oidNew : Nat} {h' : Heap}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h')) :
    h'.IdsBounded :=
  RuntimeHeap.alloc_idsBounded hbounded halloc

theorem heap_alloc_preserves_bool_exhaustive
    {h : Heap} {newObj : HeapObject} {oidNew : Nat} {h' : Heap}
    (halloc : h.alloc newObj = (oidNew, h'))
    (hneBool : newObj.className ≠ boolClass)
    (honly : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid) :
    ∀ oid obj, h'.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid := by
  exact RuntimeHeap.alloc_preserves_property_exhaustive halloc hneBool honly

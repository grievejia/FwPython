import FwPython.Common.Identifier

/-! # Runtime heap container and allocation lemmas, parameterized over the object payload. -/

/-- A heap stores objects at numeric object IDs together with a fresh-ID
counter. -/
structure RuntimeHeap (Object : Type) where
  /-- Objects stored at their numeric identifiers. Lookup selects the first matching entry. -/
  heapMap : List (Nat × Object)
  /-- The identifier assigned by the next allocation. -/
  heapCounter : Nat
  deriving DecidableEq, Repr

namespace RuntimeHeap

def lookupList (oid : Nat) : List (Nat × Object) → Option Object
  | [] => none
  | (oid', obj) :: rest =>
      if oid' = oid then
        some obj
      else
        lookupList oid rest

/-- Allocate a new object on the heap. Returns `(newOid, updatedHeap)`. -/
def alloc (h : RuntimeHeap Object) (obj : Object) : Nat × RuntimeHeap Object :=
  let oid := h.heapCounter
  (oid, ⟨(oid, obj) :: h.heapMap, oid + 1⟩)

/-- Look up an object by object ID. -/
def lookup (h : RuntimeHeap Object) (oid : Nat) : Option Object :=
  lookupList oid h.heapMap

/-- Every object ID present in the heap is strictly below the fresh counter. -/
def IdsBounded (h : RuntimeHeap Object) : Prop :=
  ∀ oid obj, h.lookup oid = some obj → oid < h.heapCounter

theorem lookup_alloc_of_lookup
    {h : RuntimeHeap Object} {oid : Nat} {obj newObj : Object}
    (hbounded : h.IdsBounded)
    (hlookup : h.lookup oid = some obj) :
    (h.alloc newObj).2.lookup oid = some obj := by
  unfold RuntimeHeap.alloc RuntimeHeap.lookup lookupList
  rw [if_neg (Nat.ne_of_gt (hbounded oid obj hlookup))]
  exact hlookup

theorem alloc_lookup_new
    {h : RuntimeHeap Object} {newObj : Object} {oid : Nat} {h' : RuntimeHeap Object}
    (halloc : h.alloc newObj = (oid, h')) :
    h'.lookup oid = some newObj := by
  unfold RuntimeHeap.alloc at halloc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  unfold RuntimeHeap.lookup lookupList
  rw [if_pos rfl]

theorem alloc_preserves_old
    {h : RuntimeHeap Object} {newObj : Object} {oidNew : Nat} {h' : RuntimeHeap Object}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h'))
    {oid : Nat} {obj : Object}
    (hlook : h.lookup oid = some obj) :
    h'.lookup oid = some obj := by
  unfold RuntimeHeap.alloc at halloc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  have hlt := hbounded oid obj hlook
  unfold RuntimeHeap.lookup lookupList
  rw [if_neg (Nat.ne_of_gt hlt)]
  exact hlook

theorem alloc_idsBounded
    {h : RuntimeHeap Object} {newObj : Object} {oidNew : Nat} {h' : RuntimeHeap Object}
    (hbounded : h.IdsBounded)
    (halloc : h.alloc newObj = (oidNew, h')) :
    h'.IdsBounded := by
  unfold RuntimeHeap.alloc at halloc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  intro oid obj hlook
  simp only [RuntimeHeap.lookup, lookupList] at hlook ⊢
  split at hlook
  · next heq =>
      omega
  · next hne =>
      exact Nat.lt_succ_of_lt (hbounded oid obj hlook)

theorem alloc_preserves_property_exhaustive
    {h : RuntimeHeap Object} {newObj : Object} {oidNew : Nat} {h' : RuntimeHeap Object}
    {Property : Object → Prop} {LocationProperty : Nat → Prop}
    (halloc : h.alloc newObj = (oidNew, h'))
    (hnew : ¬ Property newObj)
    (hold : ∀ oid obj, h.lookup oid = some obj → Property obj → LocationProperty oid) :
    ∀ oid obj, h'.lookup oid = some obj → Property obj → LocationProperty oid := by
  unfold RuntimeHeap.alloc at halloc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  intro oid obj hlook hproperty
  simp only [RuntimeHeap.lookup, lookupList] at hlook
  split at hlook
  · exact absurd (Option.some.inj hlook ▸ hproperty) hnew
  · exact hold oid obj hlook hproperty

/-- Allocation preserves an object property when the new object also satisfies it. -/
theorem alloc_preserves_property
    {h : RuntimeHeap Object} {newObj : Object} {oidNew : Nat} {h' : RuntimeHeap Object}
    {Property : Object → Prop}
    (halloc : h.alloc newObj = (oidNew, h'))
    (hnew : Property newObj)
    (hold : ∀ oid obj, h.lookup oid = some obj → Property obj) :
    ∀ oid obj, h'.lookup oid = some obj → Property obj := by
  unfold RuntimeHeap.alloc at halloc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
  intro oid obj lookup
  simp only [RuntimeHeap.lookup, lookupList] at lookup
  split at lookup
  · exact Option.some.inj lookup ▸ hnew
  · exact hold oid obj lookup

end RuntimeHeap

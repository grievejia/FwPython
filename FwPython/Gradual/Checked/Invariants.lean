import FwPython.Gradual.Checked.Core

/-! # Checked Heap Well-Formedness

Runtime-only invariants for the checked heap. These do not include
typing or wrapper-compatibility facts; those belong to a future
milestone. -/

/-- The checked heap is consistent with the gradual class table and checked class table. -/
structure CheckedHeapWellFormed (ct : GClassTable) (cct : CheckedClassTable)
    (h : CheckedHeap) : Prop where
  idsBounded : h.IdsBounded
  classesExist : ∀ oid obj, h.lookup oid = some obj →
    ∃ c mro, findGClass ct obj.className = some c ∧ GComputeMro ct c mro
  initialNone : h.lookup noneOid = some ⟨noneClass, .ordinary⟩
  initialTrue : h.lookup trueOid = some ⟨boolClass, .ordinary⟩
  initialFalse : h.lookup falseOid = some ⟨boolClass, .ordinary⟩
  boolExhaustive : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
    oid = trueOid ∨ oid = falseOid
  payloadBoundMethod : ∀ oid cname recvOid (m : CheckedMethod),
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    cname = boundMethodClass
  payloadReceiverValid : ∀ oid cname recvOid (m : CheckedMethod),
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    ∃ recvObj, h.lookup recvOid = some recvObj ∧
      CheckedMethodInReceiverMro ct cct recvObj.className m

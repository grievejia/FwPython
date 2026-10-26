import FwPython.Gradual.Checked.Core

/-! # Checked Heap Well-Formedness

Runtime-only invariants for the checked heap. These do not include
typing facts; value typing is tracked by the checked type-system
judgments that consume these heap invariants. -/

/-- The checked heap is consistent with the gradual class table and checked class table. -/
structure CheckedHeapWellFormed (ct : GClassTable) (cct : CheckedClassTable)
    (h : CheckedHeap) : Prop where
  /-- Every allocated object identifier is below the heap allocation frontier. -/
  idsBounded : h.IdsBounded
  /-- Every stored object names a selected class with a successful MRO. -/
  classesExist : ∀ oid obj, h.lookup oid = some obj →
    ∃ c mro, findGClass ct obj.className = some c ∧ GComputeMro ct c mro
  /-- The distinguished None identifier contains the ordinary None singleton. -/
  initialNone : h.lookup noneOid = some ⟨noneClass, .ordinary⟩
  /-- The distinguished true identifier contains an ordinary Boolean. -/
  initialTrue : h.lookup trueOid = some ⟨boolClass, .ordinary⟩
  /-- The distinguished false identifier contains an ordinary Boolean. -/
  initialFalse : h.lookup falseOid = some ⟨boolClass, .ordinary⟩
  /-- Every Boolean object is one of the two distinguished Boolean singletons. -/
  boolExhaustive : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
    oid = trueOid ∨ oid = falseOid
  /-- BoundMethod membership identifies exactly the objects with an invokable method payload. -/
  boundMethodShape : ∀ oid obj, h.lookup oid = some obj →
    (obj.className = boundMethodClass ↔
      ∃ receiver method, obj.payload = .boundMethod receiver method)
  /-- Every invokable payload refers to an existing receiver and a method selected by its MRO. -/
  payloadReceiverValid : ∀ oid cname recvOid (m : CheckedMethod),
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    ∃ recvObj, h.lookup recvOid = some recvObj ∧
      CheckedMethodInReceiverMro ct cct recvObj.className m

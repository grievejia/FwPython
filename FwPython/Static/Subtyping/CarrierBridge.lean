import FwPython.Static.Subtyping.Carrier
import FwPython.Static.TypeSystem.Invariants

/-! ## Concrete-to-abstract bridge -/

/-- Compatibility bridge into the legacy abstract carrier. -/
def HeapObject.toAbstract (obj : HeapObject) : AbstractObject :=
  match obj.payload with
  | .ordinary => .ordinary obj.className
  | .boundMethod _ m => .boundMethod m.paramTy m.returnTy

/-- When `className = boundMethodClass` for bound-method payload,
`toAbstract.runtimeClass = className`. -/
theorem HeapObject.toAbstract_runtimeClass (obj : HeapObject)
    (h : ∀ recvOid m, obj.payload = .boundMethod recvOid m →
      obj.className = boundMethodClass) :
    obj.toAbstract.runtimeClass = obj.className := by
  cases obj with
  | mk cn payload =>
    cases payload with
    | ordinary => rfl
    | boundMethod recvOid m =>
      simp [HeapObject.toAbstract, AbstractObject.runtimeClass]
      exact (h recvOid m rfl).symm

/-! ## Concrete-to-semantic bridge -/

/-- Constructive class/MRO witness for a successful heap lookup. -/
def HeapWellFormed.lookupClassWitness
    (hheap : HeapWellFormed ct heap) (hwf : WellFormedClassTable ct)
    {oid obj : _} (hlook : heap.lookup oid = some obj) :
    ClassLookupWitness ct obj.className := by
  cases hfind : findClass ct obj.className with
  | none =>
      exact False.elim <| by
        obtain ⟨_, _, hfind', _⟩ := hheap.classesExist oid obj hlook
        simp [hfind] at hfind'
  | some cls =>
      let w := hwf.allMrosExist _ _ hfind
      exact ⟨cls, w.mro, hfind, w.hmro⟩

/-- Build the semantic carrier object for a concrete heap lookup. This remains
constructive by computing the class lookup directly and taking MRO witnesses
from `WellFormedClassTable`. -/
def HeapWellFormed.lookupSemObject
    (hheap : HeapWellFormed ct heap)
    (hwf : WellFormedClassTable ct)
    {oid obj : _}
    (hlook : heap.lookup oid = some obj) :
    SemObject ct :=
  match obj.payload with
  | .ordinary =>
      let info := hheap.lookupClassWitness hwf hlook
      .ordinaryCurrent
        { cname := obj.className
          cls := info.cls
          mro := info.mro
          hfind := info.hfind
          hmro := info.hmro }
  | .boundMethod _ m =>
      .boundMethod
        { actualParam := m.paramTy
          actualReturn := m.returnTy
          cls := hwf.boundMethodExists.cls
          mro := hwf.boundMethodExists.mro
          hfind := hwf.boundMethodExists.hfind
          hmro := hwf.boundMethodExists.hmro }

theorem HeapWellFormed.lookupSemObject_hasAncestor
    (hheap : HeapWellFormed ct heap) (hwf : WellFormedClassTable ct)
    {oid obj : _} (hlook : heap.lookup oid = some obj)
    (hfind : findClass ct obj.className = some cls) (hmro : ComputeMro ct cls mro) :
    (hheap.lookupSemObject hwf hlook).hasAncestor C ↔ C ∈ mro := by
  obtain ⟨cname, payload⟩ := obj
  cases payload with
  | ordinary =>
      change (hheap.lookupSemObject hwf hlook).hasAncestor C ↔ C ∈ mro
      let info := hheap.lookupClassWitness hwf hlook
      have hcls_eq : info.cls = cls := by
        have h := info.hfind
        rw [show findClass ct cname = some cls from hfind] at h
        cases h; rfl
      subst hcls_eq
      change C ∈ info.mro ↔ C ∈ mro
      simp [determinism info.hmro hmro]
  | boundMethod recvOid m =>
      change (hheap.lookupSemObject hwf hlook).hasAncestor C ↔ C ∈ mro
      have hcname := hheap.payloadBoundMethod oid cname recvOid m hlook
      subst hcname
      have hcls_eq : cls = hwf.boundMethodExists.cls := by
        rw [hwf.boundMethodExists.hfind] at hfind; cases hfind; rfl
      subst hcls_eq
      simp [HeapWellFormed.lookupSemObject, SemObject.hasAncestor,
        BoundMethodOrd.hasAncestor, determinism hwf.boundMethodExists.hmro hmro]

theorem HeapWellFormed.lookupSemObject_boundMethod_signature
    (hheap : HeapWellFormed ct heap) (hwf : WellFormedClassTable ct)
    {oid cname recvOid m}
    (hlook : heap.lookup oid = some ⟨cname, .boundMethod recvOid m⟩) :
    ∃ bm : BoundMethodOrd ct,
      hheap.lookupSemObject hwf hlook = .boundMethod bm ∧
      bm.actualParam = m.paramTy ∧
      bm.actualReturn = m.returnTy :=
  ⟨_, rfl, rfl, rfl⟩

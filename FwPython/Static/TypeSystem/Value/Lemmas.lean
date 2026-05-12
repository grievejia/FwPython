import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.TypeSystem.Context
import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.Value.Typing
import FwPython.Static.TypeSystem.Invariants
import FwPython.Static.Subtyping.Inversion
import FwPython.Static.Subtyping.CarrierBridge

/-! ## Value typing helper lemmas -/

/-- Value typing is monotone under heap extension that preserves existing entries. -/
theorem value_has_type_mono
    (hval : ValueHasType ct heap v T)
    (hmono : ∀ {oid obj}, heap.lookup oid = some obj → heap'.lookup oid = some obj) :
    ValueHasType ct heap' v T := by
  induction hval with
  | objRef hlook hsub => exact .objRef (hmono hlook) hsub
  | objRefCallable hlook hlookRecv hprov =>
    exact .objRefCallable (hmono hlook) (hmono hlookRecv) hprov
  | sub _ hsub hwf ih => exact .sub (ih hmono) hsub hwf
  | interIntro _ _ hwf ih1 ih2 => exact .interIntro (ih1 hmono) (ih2 hmono) hwf
  | objRefNegClass hlook hwfNeg hfindObj hmroObj hnot =>
    exact .objRefNegClass (hmono hlook) hwfNeg hfindObj hmroObj hnot

/-- Environment typing is monotone under heap extension that preserves existing entries. -/
theorem env_has_type_mono
    (henv : EnvHasType ct heap env Γ)
    (hmono : ∀ {oid obj}, heap.lookup oid = some obj → heap'.lookup oid = some obj) :
    EnvHasType ct heap' env Γ := by
  intro x T hlook
  rcases henv x T hlook with ⟨v, henvLook, hval⟩
  exact ⟨v, henvLook, value_has_type_mono hval hmono⟩

/-- An objRef value always has a heap entry, regardless of sub layers. -/
theorem objRef_has_heap_entry (h : ValueHasType ct heap (.objRef oid) T) :
    ∃ obj, heap.lookup oid = some obj := by
  generalize hv : Value.objRef oid = v at h
  induction h with
  | objRef hlook _ => cases hv; exact ⟨_, hlook⟩
  | objRefCallable hlook _ _ => cases hv; exact ⟨_, hlook⟩
  | sub _ _ _ ih => exact ih hv
  | interIntro _ _ _ ih1 _ => exact ih1 hv
  | objRefNegClass hlook _ _ _ _ => cases hv; exact ⟨_, hlook⟩

/-! ## Semantic value typing inversion -/

/-- Semantic bridge for a concrete heap object, given explicit class/MRO
    witnesses and the heap-side bound-method class invariant. -/
private def HeapObject.toSemObject
    (obj : HeapObject)
    (hfind : findClass ct obj.className = some cls)
    (hmro : ComputeMro ct cls mro)
    (hbound : ∀ recvOid m, obj.payload = .boundMethod recvOid m →
      obj.className = boundMethodClass) :
    SemObject ct :=
  match hpay : obj.payload with
  | .ordinary =>
      .ordinaryCurrent
        { cname := obj.className
          cls := cls
          mro := mro
          hfind := hfind
          hmro := hmro }
  | .boundMethod recvOid m =>
      .boundMethod
        { actualParam := m.paramTy
          actualReturn := m.returnTy
          cls := cls
          mro := mro
          hfind := by
            simpa [hbound recvOid m hpay] using hfind
          hmro := hmro }

private theorem HeapObject.toSemObject_hasAncestor
    (obj : HeapObject)
    (hfind : findClass ct obj.className = some cls) (hmro : ComputeMro ct cls mro)
    (hbound : ∀ recvOid m, obj.payload = .boundMethod recvOid m →
      obj.className = boundMethodClass) :
    (obj.toSemObject hfind hmro hbound).hasAncestor C ↔ C ∈ mro := by
  obtain ⟨_, payload⟩ := obj
  cases payload <;>
    simp [HeapObject.toSemObject, SemObject.hasAncestor,
      CurrentOrd.hasAncestor, BoundMethodOrd.hasAncestor]

/-- An object reference's type denotes the actual runtime object in the
    semantic value semantics. -/
private theorem objRef_sem_denotes_of_sem
    (hbound : ∀ recvOid m, obj.payload = .boundMethod recvOid m →
      obj.className = boundMethodClass)
    (hval : ValueHasType ct heap (.objRef oid) T)
    (hlook : heap.lookup oid = some obj)
    (hfind : findClass ct obj.className = some cls)
    (hmro : ComputeMro ct cls mro) :
    T.semDenotes ct (obj.toSemObject hfind hmro hbound) := by
  generalize hv : Value.objRef oid = v at hval
  induction hval generalizing obj cls mro with
  | @objRef obj' _ cname _ _ hlook' hsub =>
      cases hv
      have heq := Option.some.inj (hlook'.symm.trans hlook)
      cases heq
      have hmem : cname ∈ mro := class_subtype_mem_mro hsub hfind hmro
      simpa [Ty.semDenotes] using
        (HeapObject.toSemObject_hasAncestor
          (obj := obj') (C := cname) (hfind := hfind) (hmro := hmro) (hbound := hbound)).2 hmem
  | @objRefCallable recvObj ct' m _ _ bmClass recvOid hlook' hlookRecv hprov =>
      cases hv
      have heq := Option.some.inj (hlook'.symm.trans hlook)
      cases heq
      simpa [Ty.semDenotes, HeapObject.toSemObject, hbound recvOid m rfl] using
        (show IsSubtype ct' (m.paramTy) (m.paramTy) ∧
            IsSubtype ct' (m.returnTy) (m.returnTy) from ⟨.refl, .refl⟩)
  | sub _ hsub _ ih =>
      exact semDenotes_at_obj_sound (obj := HeapObject.toSemObject obj hfind hmro hbound) hsub
        (ih hbound hlook hfind hmro hv)
  | interIntro _ _ _ ih1 ih2 =>
      exact ⟨ih1 hbound hlook hfind hmro hv, ih2 hbound hlook hfind hmro hv⟩
  | @objRefNegClass obj' _ C cls' mro' _ _ hlook' _ hfindObj hmroObj hnot =>
      cases hv
      have heq := Option.some.inj (hlook'.symm.trans hlook)
      cases heq
      have hsameCls : _ := Option.some.inj (hfindObj.symm.trans hfind)
      subst hsameCls
      have hmro_eq := determinism hmro hmroObj
      rw [← hmro_eq] at hnot
      show ¬ (HeapObject.toSemObject obj' hfind hmro hbound).hasAncestor C
      intro hanc
      exact hnot <|
        (HeapObject.toSemObject_hasAncestor
          (obj := obj') (C := C) (hfind := hfind) (hmro := hmro) (hbound := hbound)).1 hanc

/-- An object reference's type denotes the actual runtime object in the
    semantic value semantics. -/
theorem objRef_sem_denotes
    (hheap : HeapWellFormed ct heap)
    (hval : ValueHasType ct heap (.objRef oid) T)
    (hlook : heap.lookup oid = some obj)
    (hfind : findClass ct obj.className = some cls)
    (hmro : ComputeMro ct cls mro) :
    T.semDenotes ct
      (obj.toSemObject hfind hmro
        (fun recvOid m hpay =>
          hheap.payloadBoundMethod oid obj.className recvOid m (hpay ▸ hlook))) :=
  objRef_sem_denotes_of_sem
    (hbound := fun recvOid m hpay =>
      hheap.payloadBoundMethod oid obj.className recvOid m (hpay ▸ hlook))
    hval hlook hfind hmro

/-- Helper: build the bound-method class invariant for a heap-resident object. -/
private def boundOfHeap (hheap : HeapWellFormed ct heap) {oid obj}
    (hlook : heap.lookup oid = some obj) :
    ∀ recvOid m, obj.payload = .boundMethod recvOid m → obj.className = boundMethodClass :=
  fun recvOid m hpay =>
    hheap.payloadBoundMethod oid obj.className recvOid m (hpay ▸ hlook)

/-- Extract the actual class subtype from an objRef typed at a class target. -/
theorem objRef_class_subtype
    (hheap : HeapWellFormed ct heap)
    (hval : ValueHasType ct heap (.objRef oid) T)
    (hclass : IsSubtype ct T (.class_ C))
    (hlook : heap.lookup oid = some obj)
    (hfind : findClass ct obj.className = some cls)
    (hmro : ComputeMro ct cls mro) :
    IsSubtype ct (.class_ obj.className) (.class_ C) := by
  let hbound := boundOfHeap hheap hlook
  let sobj := obj.toSemObject hfind hmro hbound
  have hsem : T.semDenotes ct sobj :=
    objRef_sem_denotes hheap hval hlook hfind hmro
  have hanc : sobj.hasAncestor C := by
    simpa [Ty.semDenotes] using semDenotes_at_obj_sound (obj := sobj) hclass hsem
  exact .class_ hfind hmro <|
    (HeapObject.toSemObject_hasAncestor (obj := obj) (C := C) hfind hmro hbound).1 hanc

/-- Decompose an objRef union typing into the disjunction of class subtypes. -/
theorem objRef_union_class_decompose
    (hheap : HeapWellFormed ct heap)
    (hval : ValueHasType ct heap (.objRef oid) (.union (.class_ c1) (.class_ c2)))
    (hlook : heap.lookup oid = some obj)
    (hfind : findClass ct obj.className = some cls)
    (hmro : ComputeMro ct cls mro) :
    IsSubtype ct (.class_ obj.className) (.class_ c1) ∨
    IsSubtype ct (.class_ obj.className) (.class_ c2) := by
  let hbound := boundOfHeap hheap hlook
  have hsem : (Ty.union (.class_ c1) (.class_ c2)).semDenotes ct
      (obj.toSemObject hfind hmro hbound) :=
    objRef_sem_denotes hheap hval hlook hfind hmro
  rcases hsem with h | h
  · exact .inl (.class_ hfind hmro <|
      (HeapObject.toSemObject_hasAncestor (obj := obj) (C := c1) hfind hmro hbound).1 h)
  · exact .inr (.class_ hfind hmro <|
      (HeapObject.toSemObject_hasAncestor (obj := obj) (C := c2) hfind hmro hbound).1 h)

/-- Extract provenance from an objRef's callable ValueHasType. -/
theorem objRef_callable_provenance
    (hheap : HeapWellFormed ct heap)
    (hval : ValueHasType ct heap (.objRef oid) T)
    (hsubCallable : IsSubtype ct T (.callable P R)) :
    ∃ recvOid m recvObj,
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ ∧
      heap.lookup recvOid = some recvObj ∧
      MethodInReceiverMro ct recvObj.className m ∧
      IsSubtype ct (.callable m.paramTy m.returnTy) (.callable P R) := by
  obtain ⟨obj, hlook⟩ := objRef_has_heap_entry hval
  obtain ⟨cls, mro, hfind, hmro⟩ := hheap.classesExist _ _ hlook
  let hbound := boundOfHeap hheap hlook
  let sobj := obj.toSemObject hfind hmro hbound
  have hcall : Ty.semDenotes ct (.callable P R) sobj :=
    semDenotes_at_obj_sound (obj := sobj) hsubCallable
      (objRef_sem_denotes hheap hval hlook hfind hmro)
  obtain ⟨cn, payload⟩ := obj
  cases payload with
  | ordinary => simp [sobj, Ty.semDenotes, HeapObject.toSemObject] at hcall
  | boundMethod recvOid m =>
      have hcname := hheap.payloadBoundMethod oid cn recvOid m hlook
      subst hcname
      obtain ⟨recvObj, hlookRecv, hprov⟩ :=
        hheap.payloadReceiverValid oid boundMethodClass recvOid m hlook
      have hsig : IsSubtype ct P m.paramTy ∧ IsSubtype ct m.returnTy R := by
        simpa [sobj, hbound, Ty.semDenotes, HeapObject.toSemObject] using hcall
      exact ⟨recvOid, m, recvObj, hlook, hlookRecv, hprov, .callable hsig.1 hsig.2⟩

/-- Canonical form for callable types: the heap object has bound-method payload. -/
theorem canonical_callable
    (hheap : HeapWellFormed ct heap)
    (h : ValueHasType ct heap v (.callable paramTy returnTy)) :
    ∃ oid recvOid m recvObj,
      v = .objRef oid ∧
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid m⟩ ∧
      heap.lookup recvOid = some recvObj ∧
      MethodInReceiverMro ct recvObj.className m := by
  cases v with
  | objRef oid =>
    obtain ⟨recvOid, m, recvObj, hlook, hlookRecv, hprov, _⟩ :=
      objRef_callable_provenance hheap h .refl
    exact ⟨oid, recvOid, m, recvObj, rfl, hlook, hlookRecv, hprov⟩

/-- Canonical form for class types: must be an object reference. -/
theorem canonical_class
    (h : ValueHasType ct heap v (.class_ cname)) :
    ∃ oid obj, v = .objRef oid ∧ heap.lookup oid = some obj :=
  let .objRef oid := v; let ⟨obj, hlook⟩ := objRef_has_heap_entry h; ⟨oid, obj, rfl, hlook⟩

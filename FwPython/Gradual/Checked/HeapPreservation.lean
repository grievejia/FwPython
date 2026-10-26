import FwPython.Gradual.Checked.Invariants
import FwPython.Gradual.Checked.Heap
import FwPython.Gradual.Checked.MultiStep
import FwPython.Gradual.MRO.LookupLemmas
import FwPython.Gradual.Invariants

/-! # Heap Invariant Preservation for the Checked Machine

Every heap invariant in `CheckedHeapWellFormed` is preserved by each step
of the checked continuation machine. Most `Step` constructors leave the heap
unchanged; the interesting cases are `newSuccess`, `returnAttrAccess`, and
`returnDynAttrAccess`, which allocate. -/

namespace Checked

/-! ## Helper: list of all non-allocating constructors

Every constructor below leaves `s.heap = s'.heap`, so each invariant
field is trivially preserved. We factor this list into a macro-like
pattern to avoid repeating it six times. -/

private theorem step_preserves_idsBounded
    (hstep : Step ct cct s s') (hbounded : s.heap.IdsBounded) :
    s'.heap.IdsBounded := by
  cases hstep with
  | newSuccess _ _ _ _ halloc
  | returnAttrAccess _ _ _ _ halloc
  | returnDynAttrAccess _ _ _ _ halloc =>
    exact checkedHeap_alloc_idsBounded hbounded halloc
  | _ => exact hbounded

theorem step_preserves_heapMonotonicity
    (hstep : Step ct cct s s') (hbounded : s.heap.IdsBounded)
    {oid : Nat} {obj : CheckedHeapObject}
    (hlook : s.heap.lookup oid = some obj) :
    s'.heap.lookup oid = some obj := by
  cases hstep with
  | newSuccess _ _ _ _ halloc
  | returnAttrAccess _ _ _ _ halloc
  | returnDynAttrAccess _ _ _ _ halloc =>
    exact checkedHeap_alloc_preserves_old hbounded halloc hlook
  | _ => exact hlook

private theorem step_preserves_classesExist
    (hstep : Step ct cct s s') (hbounded : s.heap.IdsBounded)
    (hclasses : ∀ oid obj, s.heap.lookup oid = some obj →
      ∃ c mro, findGClass ct obj.className = some c ∧ GComputeMro ct c mro)
    (hallMros : ∀ cname c, findGClass ct cname = some c → GClassMroWitness ct c)
    (hBMExists : GClassLookupWitness ct boundMethodClass) :
    ∀ oid obj, s'.heap.lookup oid = some obj →
      ∃ c mro, findGClass ct obj.className = some c ∧ GComputeMro ct c mro := by
  cases hstep with
  | newSuccess hfind _ _ _ halloc =>
    intro oid obj hlook; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold CheckedHeap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · exact Option.some.inj hlook ▸ ⟨_, (hallMros _ _ hfind).mro, hfind, (hallMros _ _ hfind).hmro⟩
    · exact hclasses oid obj hlook
  | returnAttrAccess _ _ _ _ halloc
  | returnDynAttrAccess _ _ _ _ halloc =>
    intro oid obj hlook; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold CheckedHeap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · exact Option.some.inj hlook ▸
        ⟨hBMExists.cls, hBMExists.mro, hBMExists.hfind, hBMExists.hmro⟩
    · exact hclasses oid obj hlook
  | _ => exact hclasses

private theorem step_preserves_boolExhaustive
    (hstep : Step ct cct s s')
    (honly : ∀ oid obj, s.heap.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid) :
    ∀ oid obj, s'.heap.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid := by
  cases hstep with
  | newSuccess _ hne_bool _ _ halloc =>
    exact checkedHeap_alloc_preserves_bool_exhaustive halloc hne_bool honly
  | returnAttrAccess _ _ _ _ halloc
  | returnDynAttrAccess _ _ _ _ halloc =>
    exact checkedHeap_alloc_preserves_bool_exhaustive halloc
      (show boundMethodClass ≠ boolClass by decide) honly
  | _ => exact honly

/-- Allocation preserves the equivalence between BoundMethod class and invokable payload. -/
private theorem step_preserves_boundMethodShape
    (hstep : Step ct cct s s')
    (shape : ∀ oid obj, s.heap.lookup oid = some obj →
      (obj.className = boundMethodClass ↔ ∃ receiver method, obj.payload = .boundMethod receiver method)) :
    ∀ oid obj, s'.heap.lookup oid = some obj →
      (obj.className = boundMethodClass ↔ ∃ receiver method, obj.payload = .boundMethod receiver method) := by
  cases hstep with
  | newSuccess _ _ _ notMethod halloc =>
    exact RuntimeHeap.alloc_preserves_property halloc (by simp [notMethod]) shape
  | returnAttrAccess _ _ _ _ halloc
  | returnDynAttrAccess _ _ _ _ halloc =>
    exact RuntimeHeap.alloc_preserves_property halloc
      ⟨fun _ => ⟨_, _, rfl⟩, fun _ => rfl⟩ shape
  | _ => exact shape

private theorem step_preserves_payloadReceiverValid
    (hstep : Step ct cct s s') (hbounded : s.heap.IdsBounded)
    (hprv : ∀ oid cname recvOid m,
      s.heap.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
      ∃ recvObj, s.heap.lookup recvOid = some recvObj ∧
        CheckedMethodInReceiverMro ct cct recvObj.className m) :
    ∀ oid cname recvOid m,
      s'.heap.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
      ∃ recvObj, s'.heap.lookup recvOid = some recvObj ∧
        CheckedMethodInReceiverMro ct cct recvObj.className m := by
  cases hstep with
  | newSuccess _ _ _ _ halloc =>
    intro oid cname recvOid m hlook; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold CheckedHeap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · exact absurd (Option.some.inj hlook) (by simp [CheckedHeapObject.mk.injEq])
    · obtain ⟨recvObj, hrecv, hprov⟩ := hprv oid cname recvOid m hlook
      exact ⟨recvObj, lookup_checkedAlloc_of_lookup hbounded hrecv, hprov⟩
  | returnAttrAccess hlookObj hfindCls hMro hfindMethod halloc
  | returnDynAttrAccess hlookObj hfindCls hMro hfindMethod halloc =>
    intro oid cname recvOid m hlook; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold CheckedHeap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · obtain ⟨rfl, rfl⟩ := congrArg CheckedHeapObject.payload (Option.some.inj hlook)
      exact ⟨_, lookup_checkedAlloc_of_lookup hbounded hlookObj, _, _, hfindCls, hMro,
        findCheckedMethodInMro_name hfindMethod ▸ hfindMethod⟩
    · obtain ⟨recvObj, hrecv, hprov⟩ := hprv oid cname recvOid m hlook
      exact ⟨recvObj, lookup_checkedAlloc_of_lookup hbounded hrecv, hprov⟩
  | _ => exact hprv

/-! ## Combined one-step preservation -/

/-- A single step preserves `CheckedHeapWellFormed`. -/
theorem step_preserves_checkedHeapWellFormed
    (hstep : Step ct cct s s')
    (hwf : CheckedHeapWellFormed ct cct s.heap)
    (hwfct : WellFormedGClassTable ct) :
    CheckedHeapWellFormed ct cct s'.heap where
  idsBounded := step_preserves_idsBounded hstep hwf.idsBounded
  classesExist := step_preserves_classesExist hstep hwf.idsBounded hwf.classesExist
    hwfct.allMrosExist hwfct.boundMethodExists
  initialNone := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialNone
  initialTrue := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialTrue
  initialFalse := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialFalse
  boolExhaustive := step_preserves_boolExhaustive hstep hwf.boolExhaustive
  boundMethodShape := step_preserves_boundMethodShape hstep hwf.boundMethodShape
  payloadReceiverValid := step_preserves_payloadReceiverValid hstep hwf.idsBounded
    hwf.payloadReceiverValid

/-! ## Multi-step preservation -/

/-- Multi-step execution preserves `CheckedHeapWellFormed`. -/
theorem steps_preserves_checkedHeapWellFormed
    (hsteps : Steps ct cct s s')
    (hwf : CheckedHeapWellFormed ct cct s.heap)
    (hwfct : WellFormedGClassTable ct) :
    CheckedHeapWellFormed ct cct s'.heap := by
  induction hsteps with
  | refl => exact hwf
  | step hs _ ih => exact ih (step_preserves_checkedHeapWellFormed hs hwf hwfct)

/-! ## Initial heap well-formedness -/

private theorem initialHeap_lookup_cases
    {P : Prop}
    (hlook : CheckedHeap.initial.lookup oid = some obj)
    (hnone : obj = ⟨noneClass, .ordinary⟩ → P)
    (hbool : obj = ⟨boolClass, .ordinary⟩ → P) : P := by
  unfold CheckedHeap.initial at hlook
  simp only [CheckedHeap.lookup, RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at hlook
  split at hlook
  · exact hnone (Option.some.inj hlook).symm
  · split at hlook
    · exact hbool (Option.some.inj hlook).symm
    · split at hlook
      · exact hbool (Option.some.inj hlook).symm
      · cases hlook

/-- The initial checked heap is well-formed under any well-formed gradual class table. -/
theorem checkedHeapInitial_wellFormed
    (hwfct : WellFormedGClassTable ct) :
    CheckedHeapWellFormed ct cct CheckedHeap.initial where
  idsBounded := by
    intro oid obj hlook
    unfold CheckedHeap.initial at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at hlook
    split at hlook
    · rename_i hzero
      cases hzero
      decide
    · split at hlook
      · rename_i htrue
        cases htrue
        decide
      · split at hlook
        · rename_i hfalse
          cases hfalse
          decide
        · cases hlook
  classesExist := by
    intro oid obj hlook
    exact initialHeap_lookup_cases hlook
      (fun h => h ▸ hwfct.noneExists.exists) (fun h => h ▸ hwfct.boolExists.exists)
  initialNone := by decide
  initialTrue := by decide
  initialFalse := by decide
  boolExhaustive := by
    intro oid obj hlook hcls
    unfold CheckedHeap.initial at hlook
    simp only [CheckedHeap.lookup, RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at hlook
    split at hlook
    · cases Option.some.inj hlook; simp [noneClass, boolClass] at hcls
    · split at hlook
      · rename_i htrue
        exact .inl htrue.symm
      · split at hlook
        · rename_i hfalse
          exact .inr hfalse.symm
        · cases hlook
  boundMethodShape := by
    intro oid obj lookup
    exact initialHeap_lookup_cases lookup
      (fun equal => by cases equal; simp [noneClass, boundMethodClass])
      (fun equal => by cases equal; simp [boolClass, boundMethodClass])
  payloadReceiverValid := fun _ _ _ _ hlook => initialHeap_lookup_cases hlook nofun nofun

/-! ## Execution-level corollary -/

/-- Any execution from the initial heap preserves `CheckedHeapWellFormed`. -/
theorem evaluatesFrom_preserves_checkedHeapWellFormed
    (hwfct : WellFormedGClassTable ct)
    (hexec : evaluatesFrom ct cct CheckedHeap.initial env expr heap' result) :
    CheckedHeapWellFormed ct cct heap' := by
  obtain ⟨⟨_, _, _, _⟩, hsteps, hfinal⟩ := hexec
  have hwf := steps_preserves_checkedHeapWellFormed hsteps
    (checkedHeapInitial_wellFormed hwfct) hwfct
  simp only [finalResult?] at hfinal; split at hfinal <;> simp_all

end Checked

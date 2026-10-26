import FwPython.Static.Semantics.MultiStep
import FwPython.Static.Semantics.Heap
import FwPython.Static.MRO.LookupLemmas
import FwPython.Static.TypeSystem.Invariants

/-! # Heap Invariant Preservation for the Small-Step Machine

Every heap invariant required by the type system (`HeapWellFormed`) is
preserved by each step of the continuation machine.  Most `Step`
constructors leave the heap unchanged, so the interesting cases are
`newSuccess` and `returnAttrAccess`, which allocate.  These reuse the
shared allocation lemmas from `FwPython.Static.Semantics.Heap`. -/

/-- An initial heap lookup selects None, True, or False with its preallocated object ID. -/
private theorem initialHeap_lookup_cases {P : Prop}
    (lookup : Heap.initial.lookup oid = some obj)
    (hnone : oid = noneOid → obj = ⟨noneClass, .ordinary⟩ → P)
    (hbool : (oid = trueOid ∨ oid = falseOid) → obj = ⟨boolClass, .ordinary⟩ → P) : P := by
  unfold Heap.initial at lookup
  simp only [Heap.lookup, RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at lookup
  split at lookup
  · rename_i equal
    exact hnone equal.symm (Option.some.inj lookup).symm
  · split at lookup
    · rename_i equal
      exact hbool (.inl equal.symm) (Option.some.inj lookup).symm
    · split at lookup
      · rename_i equal
        exact hbool (.inr equal.symm) (Option.some.inj lookup).symm
      · cases lookup

/-- The builtin objects in the initial heap satisfy every static heap requirement. -/
theorem Heap.initial_wellFormed (hwfct : WellTypedClassHierarchy ct) :
    HeapWellFormed ct Heap.initial where
  idsBounded := by
    intro oid obj lookup
    exact initialHeap_lookup_cases lookup
      (fun equal _ => by cases equal; decide)
      (fun alternatives _ => by rcases alternatives with rfl | rfl <;> decide)
  classesExist := by
    intro oid obj lookup
    exact initialHeap_lookup_cases lookup
      (fun _ equal => equal ▸ hwfct.noneExists.exists)
      (fun _ equal => equal ▸ hwfct.boolExists.exists)
  initialNone := by decide
  initialTrue := by decide
  initialFalse := by decide
  boolExhaustive := by
    intro oid obj lookup classEq
    exact initialHeap_lookup_cases lookup
      (fun _ equal => by cases equal; simp [noneClass, boolClass] at classEq)
      (fun alternatives _ => alternatives)
  boundMethodShape := by
    intro oid obj lookup
    exact initialHeap_lookup_cases lookup
      (fun _ equal => by cases equal; simp [noneClass, boundMethodClass])
      (fun _ equal => by cases equal; simp [boolClass, boundMethodClass])
  payloadReceiverValid := fun _ _ _ _ lookup =>
    initialHeap_lookup_cases lookup (fun _ => nofun) (fun _ => nofun)

namespace SmallStep

/-! ## One-step preservation -/

/-- A single step preserves `Heap.IdsBounded`. -/
theorem step_preserves_idsBounded
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (hbounded : s.heap.IdsBounded) :
    s'.heap.IdsBounded := by
  cases hstep with
  | newSuccess _ _ _ _ halloc =>
    exact heap_alloc_idsBounded hbounded halloc
  | returnAttrAccess _ _ _ _ halloc =>
    exact heap_alloc_idsBounded hbounded halloc
  | focusAttrAccess | focusCall | focusCond _
  | condIsInstanceTrue _ _ _ _ _ | condIsInstanceFalse _ _ _ _ _
  | condIsInstanceVarNotFound _
  | varSuccess _ | varError _
  | newClassNotFound _ | newBuiltinError _ _
  | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _
  | isInstanceVarNotFound _
  | returnAttrAccessNotFound _ _ _ _
  | returnCallCallee _ | returnCallNotInvokable _
  | returnAwaitArgument | returnCondTrue | returnCondFalse
  | returnCondNotBool _ _ | returnFromBody
  | errorUnwindAttrAccess | errorUnwindCallCallee
  | errorUnwindAwaitArgument | errorUnwindCond
  | errorUnwindReturnTo =>
    exact hbounded

/-- A single step preserves existing heap entries (monotonicity). -/
theorem step_preserves_heapMonotonicity
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (hbounded : s.heap.IdsBounded)
    {oid : Nat} {obj : HeapObject}
    (hlook : s.heap.lookup oid = some obj) :
    s'.heap.lookup oid = some obj := by
  cases hstep with
  | newSuccess _ _ _ _ halloc =>
    exact heap_alloc_preserves_old hbounded halloc hlook
  | returnAttrAccess _ _ _ _ halloc =>
    exact heap_alloc_preserves_old hbounded halloc hlook
  | focusAttrAccess | focusCall | focusCond _
  | condIsInstanceTrue _ _ _ _ _ | condIsInstanceFalse _ _ _ _ _
  | condIsInstanceVarNotFound _
  | varSuccess _ | varError _
  | newClassNotFound _ | newBuiltinError _ _
  | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _
  | isInstanceVarNotFound _
  | returnAttrAccessNotFound _ _ _ _
  | returnCallCallee _ | returnCallNotInvokable _
  | returnAwaitArgument | returnCondTrue | returnCondFalse
  | returnCondNotBool _ _ | returnFromBody
  | errorUnwindAttrAccess | errorUnwindCallCallee
  | errorUnwindAwaitArgument | errorUnwindCond
  | errorUnwindReturnTo =>
    exact hlook

/-- A single step preserves `classesExist`. -/
theorem step_preserves_classesExist
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (hbounded : s.heap.IdsBounded)
    (hclasses : ∀ oid obj, s.heap.lookup oid = some obj →
      ∃ c mro, findClass ct obj.className = some c ∧ ComputeMro ct c mro)
    (hallMros : ∀ cname c, findClass ct cname = some c → ClassMroWitness ct c)
    (hBMExists : ∃ c, findClass ct boundMethodClass = some c) :
    ∀ oid obj, s'.heap.lookup oid = some obj →
      ∃ c mro, findClass ct obj.className = some c ∧ ComputeMro ct c mro := by
  cases hstep with
  | newSuccess hfind _ _ _ halloc =>
    intro oid obj hlook
    unfold Heap.alloc at halloc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold Heap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · obtain rfl := Option.some.inj hlook
      exact ⟨_, (hallMros _ _ hfind).mro, hfind, (hallMros _ _ hfind).hmro⟩
    · exact hclasses oid obj hlook
  | returnAttrAccess _ _ _ _ halloc =>
    intro oid obj hlook
    unfold Heap.alloc at halloc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold Heap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · obtain rfl := Option.some.inj hlook
      obtain ⟨c, hfc⟩ := hBMExists
      exact ⟨c, (hallMros _ _ hfc).mro, hfc, (hallMros _ _ hfc).hmro⟩
    · exact hclasses oid obj hlook
  | focusAttrAccess | focusCall | focusCond _
  | condIsInstanceTrue _ _ _ _ _ | condIsInstanceFalse _ _ _ _ _
  | condIsInstanceVarNotFound _
  | varSuccess _ | varError _
  | newClassNotFound _ | newBuiltinError _ _
  | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _
  | isInstanceVarNotFound _
  | returnAttrAccessNotFound _ _ _ _
  | returnCallCallee _ | returnCallNotInvokable _
  | returnAwaitArgument | returnCondTrue | returnCondFalse
  | returnCondNotBool _ _ | returnFromBody
  | errorUnwindAttrAccess | errorUnwindCallCallee
  | errorUnwindAwaitArgument | errorUnwindCond
  | errorUnwindReturnTo =>
    exact hclasses

/-- A single step preserves Bool OID exhaustiveness. -/
theorem step_preserves_boolExhaustive
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (honly : ∀ oid obj, s.heap.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid) :
    ∀ oid obj, s'.heap.lookup oid = some obj → obj.className = boolClass →
      oid = trueOid ∨ oid = falseOid := by
  cases hstep with
  | newSuccess _ hne_bool _ _ halloc =>
    exact heap_alloc_preserves_bool_exhaustive halloc hne_bool honly
  | returnAttrAccess _ _ _ _ halloc =>
    exact heap_alloc_preserves_bool_exhaustive halloc
      (show boundMethodClass ≠ boolClass by decide) honly
  | focusAttrAccess | focusCall | focusCond _
  | condIsInstanceTrue _ _ _ _ _ | condIsInstanceFalse _ _ _ _ _
  | condIsInstanceVarNotFound _
  | varSuccess _ | varError _
  | newClassNotFound _ | newBuiltinError _ _
  | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _
  | isInstanceVarNotFound _
  | returnAttrAccessNotFound _ _ _ _
  | returnCallCallee _ | returnCallNotInvokable _
  | returnAwaitArgument | returnCondTrue | returnCondFalse
  | returnCondNotBool _ _ | returnFromBody
  | errorUnwindAttrAccess | errorUnwindCallCallee
  | errorUnwindAwaitArgument | errorUnwindCond
  | errorUnwindReturnTo =>
    exact honly

/-- Allocation preserves the equivalence between BoundMethod class and invokable payload. -/
theorem step_preserves_boundMethodShape
    (hstep : Step ct s s')
    (shape : ∀ oid obj, s.heap.lookup oid = some obj →
      (obj.className = boundMethodClass ↔ ∃ receiver method, obj.payload = .boundMethod receiver method)) :
    ∀ oid obj, s'.heap.lookup oid = some obj →
      (obj.className = boundMethodClass ↔ ∃ receiver method, obj.payload = .boundMethod receiver method) := by
  cases hstep with
  | newSuccess _ _ _ notMethod halloc =>
    exact RuntimeHeap.alloc_preserves_property halloc (by simp [notMethod]) shape
  | returnAttrAccess _ _ _ _ halloc =>
    exact RuntimeHeap.alloc_preserves_property halloc
      ⟨fun _ => ⟨_, _, rfl⟩, fun _ => rfl⟩ shape
  | _ => exact shape

/-- A single step preserves receiver validity: bound-method receivers exist
    in the heap with valid method provenance. -/
theorem step_preserves_payloadReceiverValid
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (hbounded : s.heap.IdsBounded)
    (hprv : ∀ oid cname recvOid m,
      s.heap.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
      ∃ recvObj, s.heap.lookup recvOid = some recvObj ∧
        MethodInReceiverMro ct recvObj.className m) :
    ∀ oid cname recvOid m,
      s'.heap.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
      ∃ recvObj, s'.heap.lookup recvOid = some recvObj ∧
        MethodInReceiverMro ct recvObj.className m := by
  cases hstep with
  | newSuccess _ _ _ _ halloc =>
    intro oid cname recvOid m hlook
    unfold Heap.alloc at halloc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold Heap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · exact absurd (Option.some.inj hlook) (by simp [HeapObject.mk.injEq])
    · obtain ⟨recvObj, hrecv, hmethod⟩ := hprv oid cname recvOid m hlook
      exact ⟨recvObj, lookup_alloc_of_lookup hbounded hrecv, hmethod⟩
  | returnAttrAccess hlookObj hfindClass hmroEval hmethodEval halloc =>
    intro oid cname recvOid m hlook
    unfold Heap.alloc at halloc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc
    unfold Heap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook
    split at hlook
    · simp [HeapObject.mk.injEq, ObjectPayload.boundMethod.injEq] at hlook
      obtain ⟨_, rfl, rfl⟩ := hlook
      exact ⟨_, lookup_alloc_of_lookup hbounded hlookObj,
        method_in_receiver_mro_of_lookup hfindClass hmroEval hmethodEval⟩
    · obtain ⟨recvObj, hrecv, hmethod⟩ := hprv oid cname recvOid m hlook
      exact ⟨recvObj, lookup_alloc_of_lookup hbounded hrecv, hmethod⟩
  | focusAttrAccess | focusCall | focusCond _
  | condIsInstanceTrue _ _ _ _ _ | condIsInstanceFalse _ _ _ _ _
  | condIsInstanceVarNotFound _
  | varSuccess _ | varError _
  | newClassNotFound _ | newBuiltinError _ _
  | constNone | constTrue | constFalse
  | isInstanceTrue _ _ _ _ _ | isInstanceFalse _ _ _ _ _
  | isInstanceVarNotFound _
  | returnAttrAccessNotFound _ _ _ _
  | returnCallCallee _ | returnCallNotInvokable _
  | returnAwaitArgument | returnCondTrue | returnCondFalse
  | returnCondNotBool _ _ | returnFromBody
  | errorUnwindAttrAccess | errorUnwindCallCallee
  | errorUnwindAwaitArgument | errorUnwindCond
  | errorUnwindReturnTo =>
    exact hprv

/-! ## Combined one-step HeapWellFormed preservation -/

/-- A single step preserves `HeapWellFormed`. -/
theorem step_preserves_heapWellFormed
    {ct : ClassTable} {s s' : State}
    (hstep : Step ct s s')
    (hwf : HeapWellFormed ct s.heap)
    (hwfct : WellTypedClassHierarchy ct) :
    HeapWellFormed ct s'.heap where
  idsBounded := step_preserves_idsBounded hstep hwf.idsBounded
  classesExist := step_preserves_classesExist hstep hwf.idsBounded hwf.classesExist
    hwfct.allMrosExist hwfct.toWellFormedClassHierarchy.boundMethodExists_find
  initialNone := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialNone
  initialTrue := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialTrue
  initialFalse := step_preserves_heapMonotonicity hstep hwf.idsBounded hwf.initialFalse
  boolExhaustive := step_preserves_boolExhaustive hstep hwf.boolExhaustive
  boundMethodShape := step_preserves_boundMethodShape hstep hwf.boundMethodShape
  payloadReceiverValid := step_preserves_payloadReceiverValid hstep hwf.idsBounded hwf.payloadReceiverValid

end SmallStep

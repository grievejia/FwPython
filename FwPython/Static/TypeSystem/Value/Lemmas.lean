import FwPython.Static.TypeSystem.Invariants
import FwPython.Static.TypeSystem.Value.Typing
import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.ObjectTypeLowerBound

/-! ## Value typing helper lemmas -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- Value typing is monotone under heap extension that preserves existing entries. -/
theorem value_has_type_mono
    (hval : ValueHasType structural heap v T)
    (hmono : ∀ {oid obj}, heap.lookup oid = some obj → heap'.lookup oid = some obj) :
    ValueHasType structural heap' v T := by
  induction hval with
  | objRef hlook hsub => exact .objRef (hmono hlook) hsub
  | objRefCallable hlook =>
    exact .objRefCallable (hmono hlook)
  | sub _ hsub ih => exact .sub (ih hmono) hsub
  | interIntro _ _ hwf ih1 ih2 => exact .interIntro (ih1 hmono) (ih2 hmono) hwf
  | objRefNegClass hlook hwfNeg hfindObj hmroObj hnot =>
    exact .objRefNegClass (hmono hlook) hwfNeg hfindObj hmroObj hnot

/-- Environment typing is monotone under heap extension that preserves existing entries. -/
theorem env_has_type_mono
    (henv : EnvHasType structural heap env Γ)
    (hmono : ∀ {oid obj}, heap.lookup oid = some obj → heap'.lookup oid = some obj) :
    EnvHasType structural heap' env Γ := by
  intro x T hlook
  rcases henv x T hlook with ⟨v, henvLook, hval⟩
  exact ⟨v, henvLook, value_has_type_mono hval hmono⟩

/-- A typed object reference always has a heap entry. -/
theorem objRef_has_heap_entry (h : ValueHasType structural heap (.objRef oid) T) :
    ∃ obj, heap.lookup oid = some obj := by
  generalize hv : Value.objRef oid = v at h
  induction h with
  | objRef hlook _ => cases hv; exact ⟨_, hlook⟩
  | objRefCallable hlook => cases hv; exact ⟨_, hlook⟩
  | sub _ _ ih => exact ih hv
  | interIntro _ _ _ ih1 _ => exact ih1 hv
  | objRefNegClass hlook _ _ _ _ => cases hv; exact ⟨_, hlook⟩

/-! ## Object type bounds and declared method types

`valueHasType_lowerBound` places the lower bound for the object's exact class
below every assigned type when the static class table and heap are well formed.
For bound methods,
`valueHasType_declaredFunction_provenance` uses the stored method's valid signature
to put its declared function type below every assigned type.
Preservation combines these subtype facts with method-body typing to relate a
call's input and result requirements to the body that executes.
-/

open FwPython.Static.Subtyping

/-- Well-typed values have well-formed types. -/
theorem valueHasType_wellFormed
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct h)
    (hval : ValueHasType hwf.toWellFormedClassHierarchy h v T) : WellFormedTy ct T := by
  induction hval with
  | objRef _ hsub => exact hsub.targetWellFormed
  | objRefCallable hlook =>
    obtain ⟨_, _, hprov⟩ := hheap.payloadReceiverValid _ _ _ _ hlook
    exact methodInReceiverMro_wellFormed hwf hprov
  | sub _ included _ => exact included.targetWellFormed
  | interIntro _ _ hwfI _ _ => exact hwfI
  | objRefNegClass _ hwfNeg _ _ _ => exact hwfNeg

/-- In a well-typed class hierarchy and a well-formed heap, the lower bound from the exact object's
class MRO lies below every type assigned to its reference. -/
theorem valueHasType_lowerBound (hwf : WellTypedClassHierarchy ct) (hheap : HeapWellFormed ct heap)
    (typed : ValueHasType hwf.toWellFormedClassHierarchy heap (.objRef oid) T)
    (lookup : heap.lookup oid = some obj) :
    let classKnown : obj.className ∈ ct.map ClassDecl.name := by
      obtain ⟨_, _, found, _⟩ := hheap.classesExist _ _ lookup
      exact findClass_name_known found
    IsSubtype hwf.toWellFormedClassHierarchy
      (objectTypeLowerBound hwf.toWellFormedClassHierarchy obj.className classKnown).raw T := by
  intro classKnown
  generalize equal : Value.objRef oid = value at typed
  induction typed generalizing oid obj with
  | objRef found included =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      exact .trans (objectTypeLowerBound_ownClass hwf.toWellFormedClassHierarchy _ classKnown) included
  | objRefCallable found =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      cases (hheap.boundMethodShape _ _ found).mpr ⟨_, _, rfl⟩
      exact (objectTypeLowerBound_callable_iff hwf.toWellFormedClassHierarchy boundMethodClass classKnown
        (valueHasType_wellFormed hwf hheap (ValueHasType.objRefCallable found))).mpr rfl
  | sub _ included inductionHypothesis =>
      exact .trans (inductionHypothesis hheap lookup equal) included
  | interIntro _ _ _ leftInduction rightInduction =>
      exact .interIntro (leftInduction hheap lookup equal) (rightInduction hheap lookup equal)
  | objRefNegClass found excludedValid foundClass computed excluded =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      apply (objectTypeLowerBound_negClass_iff hwf.toWellFormedClassHierarchy _ _
        (findClass_name_known foundClass) (by cases excludedValid; assumption)).mpr
      rw [WellFormedClassHierarchy.typeContext_mro hwf.toWellFormedClassHierarchy foundClass computed]
      exact excluded

/-- No typed heap value can have type bottom. -/
theorem valueHasType_bottom_impossible (hwf : WellTypedClassHierarchy ct) (hheap : HeapWellFormed ct heap)
    (typed : ValueHasType hwf.toWellFormedClassHierarchy heap value .bottom) : False := by
  cases value with
  | objRef =>
      obtain ⟨obj, lookup⟩ := objRef_has_heap_entry typed
      exact objectTypeLowerBound_nonempty hwf.toWellFormedClassHierarchy obj.className _
        (valueHasType_lowerBound hwf hheap typed lookup)

/-- A type assigned to a heap value cannot be a subtype of bottom. -/
theorem valueHasType_nonempty (hwf : WellTypedClassHierarchy ct) (hheap : HeapWellFormed ct heap)
    (typed : ValueHasType hwf.toWellFormedClassHierarchy heap value T) :
    ¬ IsSubtype hwf.toWellFormedClassHierarchy T .bottom :=
  fun included => valueHasType_bottom_impossible hwf hheap (.sub typed included)

/-- The stored method's declared function type lies below every type assigned to this bound-method reference. -/
theorem valueHasType_declaredFunction_provenance
    (lookup : heap.lookup oid = some ⟨boundMethodClass, .boundMethod receiver method⟩)
    (typed : ValueHasType structural heap (.objRef oid) T)
    (methodValid : WellFormedTy ct (.callable method.paramTy method.returnTy)) :
    IsSubtype structural (.callable method.paramTy method.returnTy) T := by
  generalize equal : Value.objRef oid = value at typed
  induction typed generalizing oid with
  | objRef found included =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      exact .trans (.callableBoundMethod methodValid.callable_param methodValid.callable_return) included
  | objRefCallable found =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      exact .refl methodValid
  | sub _ included ih => exact .trans (ih lookup equal) included
  | interIntro _ _ _ ihLeft ihRight => exact .interIntro (ihLeft lookup equal) (ihRight lookup equal)
  | objRefNegClass found excludedValid foundClass computed excluded =>
      cases equal
      cases Option.some.inj (found.symm.trans lookup)
      exact .trans (.callableBoundMethod methodValid.callable_param methodValid.callable_return)
        (.sealedClassNegClass (by simp [sealedClasses]) foundClass computed excluded excludedValid.class_of_neg)

/-- In a well-typed class hierarchy and a well-formed heap, the exact object's class type lies below
a class type assigned to its reference. -/
theorem objRef_class_subtype (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap) (typed : ValueHasType hwf.toWellFormedClassHierarchy heap (.objRef oid) (.class_ C))
    (lookup : heap.lookup oid = some obj)
    (found : findClass ct obj.className = some declaration) (computed : ComputeMro ct declaration linearization) :
    IsSubtype hwf.toWellFormedClassHierarchy (.class_ obj.className) (.class_ C) :=
  .class_ found computed (objectTypeLowerBound_mem_mro hwf.toWellFormedClassHierarchy found computed
    (valueHasType_lowerBound hwf hheap typed lookup))

/-- A reference with either of two class types belongs to at least one of those classes. -/
theorem objRef_union_class_decompose (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (typed : ValueHasType hwf.toWellFormedClassHierarchy heap (.objRef oid) (.union (.class_ c1) (.class_ c2)))
    (lookup : heap.lookup oid = some obj)
    (found : findClass ct obj.className = some declaration) (computed : ComputeMro ct declaration linearization) :
    IsSubtype hwf.toWellFormedClassHierarchy (.class_ obj.className) (.class_ c1) ∨
    IsSubtype hwf.toWellFormedClassHierarchy (.class_ obj.className) (.class_ c2) := by
  have lower := valueHasType_lowerBound hwf hheap typed lookup
  have branches := (objectTypeLowerBound_union_iff hwf.toWellFormedClassHierarchy obj.className
    (findClass_name_known found) lower.targetWellFormed).mp lower
  refine branches.imp ?_ ?_
  all_goals
    exact fun included => .class_ found computed
      (objectTypeLowerBound_mem_mro hwf.toWellFormedClassHierarchy found computed included)

/-- A reference with a function type stores a method whose declared type is a subtype of that function type. -/
theorem objRef_callable_provenance (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap) (typed : ValueHasType hwf.toWellFormedClassHierarchy heap (.objRef oid) (.callable P R)) :
    ∃ receiver method recvObj,
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod receiver method⟩ ∧
      heap.lookup receiver = some recvObj ∧ MethodInReceiverMro ct recvObj.className method ∧
      IsSubtype hwf.toWellFormedClassHierarchy (.callable method.paramTy method.returnTy) (.callable P R) := by
  obtain ⟨obj, lookup⟩ := objRef_has_heap_entry typed
  have lower := valueHasType_lowerBound hwf hheap typed lookup
  have classMethod := (objectTypeLowerBound_callable_iff hwf.toWellFormedClassHierarchy obj.className
    _ lower.targetWellFormed).mp lower
  obtain ⟨receiver, method, payload⟩ := (hheap.boundMethodShape _ _ lookup).mp classMethod
  have objectEqual : obj = ⟨boundMethodClass, .boundMethod receiver method⟩ := by
    cases obj
    simp_all
  subst obj
  obtain ⟨recvObj, recvLookup, provenance⟩ := hheap.payloadReceiverValid _ _ _ _ lookup
  exact ⟨receiver, method, recvObj, lookup, recvLookup, provenance,
    valueHasType_declaredFunction_provenance lookup typed
      (methodInReceiverMro_wellFormed hwf provenance)⟩

/-- A value with a function type stores a method and receiver. The method occurs in the receiver's MRO. -/
theorem canonical_callable (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap) (typed : ValueHasType hwf.toWellFormedClassHierarchy heap value (.callable P R)) :
    ∃ oid receiver method recvObj,
      value = .objRef oid ∧ heap.lookup oid = some ⟨boundMethodClass, .boundMethod receiver method⟩ ∧
      heap.lookup receiver = some recvObj ∧ MethodInReceiverMro ct recvObj.className method := by
  cases value with
  | objRef oid =>
      obtain ⟨receiver, method, recvObj, lookup, recvLookup, provenance, _⟩ :=
        objRef_callable_provenance hwf hheap typed
      exact ⟨oid, receiver, method, recvObj, rfl, lookup, recvLookup, provenance⟩

/-- A value with a class type is an object reference with a heap entry. -/
theorem canonical_class (typed : ValueHasType structural heap value (.class_ cname)) :
    ∃ oid obj, value = .objRef oid ∧ heap.lookup oid = some obj :=
  let .objRef oid := value
  let ⟨obj, lookup⟩ := objRef_has_heap_entry typed
  ⟨oid, obj, rfl, lookup⟩

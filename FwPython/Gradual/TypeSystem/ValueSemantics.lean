import FwPython.Gradual.TypeSystem.CheckedTargetPrecision.Core
import FwPython.Gradual.TypeSystem.EnforcementClassification
import FwPython.Gradual.TypeSystem.ValueTyping
import FwPython.Gradual.Checked.Enforce

/-! # Semantic satisfaction for explicit checked targets -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

/-- The shallow runtime callable atom used by the checked-target semantics.
It matches the current enforcement precondition for callable success exactly:
the current value must be an object reference to a bound-method heap object. -/
inductive CheckedCallableAtom
    (heap : CheckedHeap) :
    CheckedValue → Prop where
  | objRefBoundMethod :
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid cm⟩ →
      CheckedCallableAtom heap (.objRef oid)

/-- Derived success condition for class negation boundaries. -/
def CheckedNegClassSuccess
    (gct : GClassTable) (heap : CheckedHeap) (v : CheckedValue)
    (cname : Identifier) : Prop :=
  EnforceValue gct heap v (compileBoundaryTarget (.negClass cname)) .ok

/-- Semantic satisfaction of a checked runtime value against an explicit checked
target. Callable satisfaction is intentionally shallow: the parameter and return
children are enforced later at call and return boundaries, not on the current
value itself. -/
def CheckedValueSatisfies
    (gct : GClassTable) (cct : CheckedClassTable)
    (heap : CheckedHeap) (v : CheckedValue) :
    CheckedTarget → Prop
  | .any => CheckedAnyShape gct cct heap v
  | .class_ cname => CheckedClassView gct cct heap v cname
  | .callable _ _ => CheckedCallableAtom heap v
  | .union left right =>
      CheckedValueSatisfies gct cct heap v left ∨
        CheckedValueSatisfies gct cct heap v right
  | .intersection left right =>
      CheckedValueSatisfies gct cct heap v left ∧
        CheckedValueSatisfies gct cct heap v right
  | .bottom => False
  | .negClass cname =>
      CheckedAnyShape gct cct heap v ∧
        CheckedNegClassSuccess gct heap v cname

theorem checkedCallableView_toAtom :
    CheckedCallableView gct cct heap v → CheckedCallableAtom heap v
  | .objRefBoundMethod hlook .. => .objRefBoundMethod hlook

theorem checkedValueSatisfies_toAnyShape
    (hsat : CheckedValueSatisfies gct cct heap v T) :
    CheckedAnyShape gct cct heap v := by
  induction T generalizing v with
  | any =>
      exact hsat
  | class_ _ =>
      exact checkedClassView_toShape hsat
  | callable _ _ =>
      let .objRefBoundMethod hlook := hsat
      exact .objRef hlook
  | union _ _ ihLeft ihRight =>
      rcases hsat with hsatLeft | hsatRight
      · exact ihLeft hsatLeft
      · exact ihRight hsatRight
  | intersection _ _ ihLeft _ =>
      exact ihLeft hsat.1
  | bottom =>
      cases hsat
  | negClass _ =>
      exact hsat.1

theorem callableAtom_matches_enforce_callable_ok
    {paramTy returnTy : CheckedTarget} :
    CheckedCallableAtom heap v ↔
      EnforceValue gct heap v
        (compileBoundaryTarget (.callable paramTy returnTy))
        .ok := by
  constructor
  · intro hatom
    let .objRefBoundMethod hlook := hatom
    simpa [compileBoundaryTarget] using
      (EnforceValue.callableObjRefTransparentOk
        (ct := gct)
        (heap := heap)
        (domC := compileBoundaryTarget paramTy)
        (codC := compileBoundaryTarget returnTy)
        hlook)
  · intro henf
    let .callableObjRefTransparentOk hlook := henf
    exact .objRefBoundMethod hlook

theorem checkedValueWitness_satisfies
    (w : CheckedValueWitness gct cct heap v (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v T := by
  induction T generalizing v with
  | any =>
      exact checkedValueWitness_toShape w
  | class_ _ =>
      exact checkedValueWitness_class_view w
  | callable _ _ =>
      exact checkedCallableView_toAtom (checkedValueWitness_callable_view w)
  | union left right ihLeft ihRight =>
      match w with
      | .mk _ (.unionLeft wLeft) => exact Or.inl (ihLeft wLeft)
      | .mk _ (.unionRight wRight) => exact Or.inr (ihRight wRight)
  | intersection left right ihLeft ihRight =>
      let .mk _ (.intersection wLeft wRight) := w
      exact ⟨ihLeft wLeft, ihRight wRight⟩
  | bottom =>
      let .mk _ data := w
      cases data
  | negClass _ =>
      let .mk _ (.negClass hshape hsuccess) := w
      exact ⟨hshape, by simpa [CheckedNegClassSuccess, compileBoundaryTarget] using hsuccess⟩

theorem checkedValueSatisfies_toWitness
    (hheapwf : CheckedHeapWellFormed gct cct heap)
    (hwf : WellFormedGTy gct (interpTarget T))
    (hsat : CheckedValueSatisfies gct cct heap v T) :
    CheckedValueWitness gct cct heap v (interpTarget T) := by
  induction T generalizing v with
  | any =>
      exact .mk hwf (.any hsat)
  | class_ _ =>
      exact .mk hwf (.class_ hsat)
  | callable _ _ =>
      let .callable hwfParam hwfReturn := hwf
      let .objRefBoundMethod hlook := hsat
      obtain ⟨recvObj, hrecv, hmro⟩ :=
        hheapwf.payloadReceiverValid _ _ _ _ hlook
      exact .mk (.callable hwfParam hwfReturn)
        (.callable (.objRefBoundMethod hlook hrecv hmro))
  | union _ _ ihLeft ihRight =>
      let .union hwfLeft hwfRight := hwf
      rcases hsat with hsatLeft | hsatRight
      · exact .mk (.union hwfLeft hwfRight) (.unionLeft (ihLeft hwfLeft hsatLeft))
      · exact .mk (.union hwfLeft hwfRight) (.unionRight (ihRight hwfRight hsatRight))
  | intersection _ _ ihLeft ihRight =>
      let .intersection hwfLeft hwfRight := hwf
      exact .mk (.intersection hwfLeft hwfRight)
        (.intersection (ihLeft hwfLeft hsat.1) (ihRight hwfRight hsat.2))
  | bottom =>
      cases hsat
  | negClass _ =>
      exact .mk hwf
        (.negClass hsat.1 (by simpa [CheckedNegClassSuccess, compileBoundaryTarget] using hsat.2))

theorem checkedValueSatisfies_iff_witness
    (hheapwf : CheckedHeapWellFormed gct cct heap)
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v T ↔
      CheckedValueWitness gct cct heap v (interpTarget T) :=
  ⟨checkedValueSatisfies_toWitness hheapwf hwf, checkedValueWitness_satisfies⟩

theorem checkedValueSatisfies_precision
    (hprec : CheckedTargetPrecision T₁ T₂)
    (hsat : CheckedValueSatisfies gct cct heap v T₁) :
    CheckedValueSatisfies gct cct heap v T₂ := by
  induction hprec generalizing v with
  | refl =>
      exact hsat
  | toAny =>
      exact checkedValueSatisfies_toAnyShape hsat
  | callable _ _ _ _ =>
      exact hsat
  | union _ _ ihLeft ihRight =>
      rcases hsat with hsatLeft | hsatRight
      · exact Or.inl (ihLeft hsatLeft)
      · exact Or.inr (ihRight hsatRight)
  | intersection _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat.1, ihRight hsat.2⟩

theorem enforce_ok_satisfies
    (henf : EnforceValue gct heap v (compileBoundaryTarget T) .ok)
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : Checked.AlignedCheckedClassTable gct structural cct)
    (htarget : CheckedTargetTy gct (interpTarget T))
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v T :=
  checkedValueWitness_satisfies <|
    Checked.enforce_ok_has_checkedTargetWitness
      henf hshape hheap hwfct halign htarget hwf

theorem checkedValueSatisfies_same_contract
    (hsat : CheckedValueSatisfies gct cct heap v T)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (htarget : CheckedTargetTy gct (interpTarget T))
    (hwf : WellFormedGTy gct (interpTarget T)) :
    EnforceValue gct heap v (compileBoundaryTarget T) .ok ∧
    (EnforceValue gct heap v (compileBoundaryTarget T) .blame → False) :=
  Checked.checkedValueWitness_same_checkedTarget
    (checkedValueSatisfies_toWitness hheap hwf hsat) htarget hheap

import FwPython.Gradual.TypeSystem.CheckedTargetPrecision
import FwPython.Gradual.TypeSystem.BoundaryCast
import FwPython.Gradual.TypeSystem.EnforcementClassification
import FwPython.Gradual.TypeSystem.ValueTyping
import FwPython.Gradual.Checked.Enforce

/-! # Semantic satisfaction for explicit checked targets -/

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
  ∀ labels : BoundaryLabels (compileBoundaryTarget (.negClass cname)),
    EnforceValue gct heap v (compileBoundaryTarget (.negClass cname)) labels (.ok v)

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

theorem checkedCallableView_toAtom
    (hview : CheckedCallableView gct cct heap v) :
    CheckedCallableAtom heap v := by
  cases hview with
  | objRefBoundMethod hlook _ _ =>
      exact .objRefBoundMethod hlook

theorem checkedValueSatisfies_toAnyShape
    (hsat : CheckedValueSatisfies gct cct heap v T) :
    CheckedAnyShape gct cct heap v := by
  induction T generalizing v with
  | any =>
      exact hsat
  | class_ _ =>
      exact checkedClassView_toShape hsat
  | callable _ _ =>
      cases hsat with
      | objRefBoundMethod hlook =>
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
    {paramTy returnTy : CheckedTarget}
    {labels : BoundaryLabels (compileBoundaryTarget (.callable paramTy returnTy))} :
    CheckedCallableAtom heap v ↔
      EnforceValue gct heap v
        (compileBoundaryTarget (.callable paramTy returnTy))
        labels
        (.ok v) := by
  constructor
  · intro hatom
    cases hatom with
    | objRefBoundMethod hlook =>
        simpa [compileBoundaryTarget] using
          (EnforceValue.callableObjRefTransparentOk
            (ct := gct)
            (heap := heap)
            (labels := labels)
            (domC := compileBoundaryTarget paramTy)
            (codC := compileBoundaryTarget returnTy)
            hlook)
  · intro henf
    cases henf with
    | callableObjRefTransparentOk hlook =>
        exact .objRefBoundMethod hlook

theorem checkedValueWitness_satisfies
    (w : CheckedValueWitness gct cct heap v (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v T := by
  induction T generalizing v with
  | any =>
      simpa using checkedValueWitness_toShape w
  | class_ _ =>
      simpa using checkedValueWitness_class_view w
  | callable _ _ =>
      exact checkedCallableView_toAtom (checkedValueWitness_callable_view w)
  | union left right ihLeft ihRight =>
      cases w with
      | mk _ data =>
          cases data with
          | unionLeft wLeft =>
              exact Or.inl (ihLeft wLeft)
          | unionRight wRight =>
              exact Or.inr (ihRight wRight)
  | intersection left right ihLeft ihRight =>
      cases w with
      | mk _ data =>
          cases data with
          | intersection wLeft wRight =>
              exact ⟨ihLeft wLeft, ihRight wRight⟩
  | bottom =>
      cases w with
      | mk _ data =>
          cases data
  | negClass _ =>
      cases w with
      | mk _ data =>
          cases data with
          | negClass hshape hsuccess =>
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
      cases hwf with
      | callable hwfParam hwfReturn =>
          cases hsat with
          | objRefBoundMethod hlook =>
              obtain ⟨recvObj, hrecv, hmro⟩ :=
                hheapwf.payloadReceiverValid _ _ _ _ hlook
              exact .mk (.callable hwfParam hwfReturn)
                (.callable (.objRefBoundMethod hlook hrecv hmro))
  | union _ _ ihLeft ihRight =>
      cases hwf with
      | union hwfLeft hwfRight =>
          rcases hsat with hsatLeft | hsatRight
          · exact .mk (.union hwfLeft hwfRight)
              (.unionLeft (ihLeft hwfLeft hsatLeft))
          · exact .mk (.union hwfLeft hwfRight)
              (.unionRight (ihRight hwfRight hsatRight))
  | intersection _ _ ihLeft ihRight =>
      cases hwf with
      | intersection hwfLeft hwfRight =>
          exact .mk (.intersection hwfLeft hwfRight)
            (.intersection
              (ihLeft hwfLeft hsat.1)
              (ihRight hwfRight hsat.2))
  | bottom =>
      cases hsat
  | negClass _ =>
      exact .mk hwf
        (.negClass hsat.1 (by simpa [CheckedNegClassSuccess, compileBoundaryTarget] using hsat.2))

theorem checkedValueSatisfies_iff_witness
    (hheapwf : CheckedHeapWellFormed gct cct heap)
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v T ↔
      CheckedValueWitness gct cct heap v (interpTarget T) := by
  constructor
  · intro hsat
    exact checkedValueSatisfies_toWitness hheapwf hwf hsat
  · intro hwit
    exact checkedValueWitness_satisfies hwit

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
      simpa [CheckedValueSatisfies] using hsat
  | union _ _ ihLeft ihRight =>
      rcases hsat with hsatLeft | hsatRight
      · exact Or.inl (ihLeft hsatLeft)
      · exact Or.inr (ihRight hsatRight)
  | intersection _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat.1, ihRight hsat.2⟩

theorem enforce_ok_satisfies
    {labels : BoundaryLabels (compileBoundaryTarget T)}
    (henf : EnforceValue gct heap v (compileBoundaryTarget T) labels (.ok v'))
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : Checked.AlignedCheckedClassTable gct cct)
    (htarget : RuntimePublicCheckedTarget gct T)
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueSatisfies gct cct heap v' T :=
  checkedValueWitness_satisfies <|
    Checked.enforce_ok_has_checkedTargetWitness
      henf hshape hheap hwfct halign htarget hwf

theorem checkedValueSatisfies_same_contract
    {labels : BoundaryLabels (compileBoundaryTarget T)}
    (hsat : CheckedValueSatisfies gct cct heap v T)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : Checked.AlignedCheckedClassTable gct cct)
    (htarget : RuntimePublicCheckedTarget gct T)
    (hwf : WellFormedGTy gct (interpTarget T)) :
    EnforceValue gct heap v (compileBoundaryTarget T) labels (.ok v) ∧
    (EnforceValue gct heap v (compileBoundaryTarget T) labels (.blame labels.direct) → False) := by
  let w := checkedValueSatisfies_toWitness hheap hwf hsat
  exact Checked.checkedValueWitness_same_checkedTarget
    w htarget hheap hwfct halign

theorem enforce_success_excludes_blame
    {labels : BoundaryLabels (compileBoundaryTarget T)}
    (hok : EnforceValue gct heap v (compileBoundaryTarget T) labels (.ok v'))
    (hbl : EnforceValue gct heap v (compileBoundaryTarget T) labels (.blame labels.direct)) :
    False :=
  enforce_outcomes_exclusive hok hbl

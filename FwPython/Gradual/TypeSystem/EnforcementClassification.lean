import FwPython.Gradual.TypeSystem.Safety
import FwPython.Gradual.Checked.Enforce
import FwPython.Gradual.Checked.HeapPreservation

/-! ## Enforcement classification helpers

These lemmas classify successful and failed enforcement on the exact target
fragment, and package the witness/no-blame facts used by preservation.
-/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

namespace Checked

/-- Extract well-formedness of method signature types from `CheckedMethodInReceiverMro`. -/
theorem checkedMethodInReceiverMro_wellFormed
    (halign : AlignedCheckedClassTable gct structural cct)
    (hmro : CheckedMethodInReceiverMro gct cct recvClassName cm) :
    WellFormedGTy gct cm.paramTy ∧ WellFormedGTy gct cm.returnTy := by
  obtain ⟨_, _, _, _, hfindCm⟩ := hmro
  obtain ⟨dname, dc, _, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
  exact halign.methodSignaturesWellFormed dname dc _ hdc hcm_in_dc

/-- Extract checked-target admissibility of method signature types from
`CheckedMethodInReceiverMro`. -/
theorem checkedMethodInReceiverMro_checkedTarget
    (halign : AlignedCheckedClassTable gct structural cct)
    (hmro : CheckedMethodInReceiverMro gct cct recvClassName cm) :
    CheckedTargetTy gct (interpTarget cm.paramTy) ∧
      CheckedTargetTy gct (interpTarget cm.returnTy) := by
  obtain ⟨_, _, _, _, hfindCm⟩ := hmro
  obtain ⟨dname, dc, _, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
  exact halign.methodSignaturesCheckedTarget dname dc _ hdc hcm_in_dc

/-- Successful callable enforcement recognizes a shallowly callable bound-method object reference. -/
theorem callable_enforce_ok_classification
    (henf : EnforceValue gct heap v (.callable domC codC) .ok)
    (_hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (_halign : AlignedCheckedClassTable gct structural cct) :
    CheckedCallableView gct cct heap v := by
  cases henf with
  | callableObjRefTransparentOk hlook =>
      obtain ⟨recvObj, hrecv, hmroMethod⟩ := hheap.payloadReceiverValid _ _ _ _ hlook
      exact .objRefBoundMethod hlook hrecv hmroMethod

/-- Formula enforcement success on a shaped value produces a witness. -/
theorem formula_enforce_ok_witness
    (henf : EnforceValue gct heap v (compileBoundaryRaw F) .ok)
    (hformula : FormulaGTy F)
    (hshape : CheckedAnyShape gct cct heap v)
    (_hheap : CheckedHeapWellFormed gct cct heap)
    (_hwfct : WellFormedGClassTableCore gct)
    (hwfF : WellFormedGTy gct F) :
    CheckedValueWitness gct cct heap v F := by
  induction hformula generalizing v with
  | any =>
      exact .mk .any (.any hshape)
  | class_ =>
      cases henf with | classObjRefOk hlook hfind hmro hmem =>
        exact .mk hwfF (.class_ (.objRef hlook hfind hmro hmem))
  | bottom => cases henf
  | union _ _ ihF ihG =>
      cases hwfF with
      | union hwfL hwfR =>
          cases henf with
          | unionLeft hF =>
              exact .mk (.union hwfL hwfR) (.unionLeft (ihF hF hshape hwfL))
          | unionRight _ hG =>
              exact .mk (.union hwfL hwfR) (.unionRight (ihG hG hshape hwfR))
  | intersection _ _ ihF ihG =>
      cases hwfF with
      | intersection hwfL hwfR =>
          cases henf with
          | intersectionOk hF hG =>
              exact .mk (.intersection hwfL hwfR)
                (.intersection (ihF hF hshape hwfL) (ihG hG hshape hwfR))
  | negClass =>
      cases henf with | negClassObjRefOk hlook hfind hmro hnmem =>
        exact .mk hwfF
          (.negClass hshape (.negClassObjRefOk hlook hfind hmro hnmem))

/-- Enforcement soundness for admissible target types. -/
theorem enforce_ok_has_witness
    (henf : EnforceValue gct heap v c .ok)
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct structural cct) :
    ∀ G, CompilesBoundary G c → CheckedTargetTy gct G → WellFormedGTy gct G →
      CheckedValueWitness gct cct heap v G := by
  intro G hcb hchecked hwfG
  subst hcb
  induction hchecked with
  | classFormula hcf =>
      exact formula_enforce_ok_witness henf hcf hshape hheap hwfct hwfG
  | callable =>
      cases hwfG with
      | callable hwfP hwfR =>
          have hview := callable_enforce_ok_classification henf hshape hheap halign
          exact .mk (.callable hwfP hwfR) (.callable hview)
  | union _ _ ihG ihH =>
      cases hwfG with
      | union hwfL hwfR =>
          cases henf with
          | unionLeft henfG =>
              exact .mk (.union hwfL hwfR) (.unionLeft (ihG hwfL henfG))
          | unionRight _ henfH =>
              exact .mk (.union hwfL hwfR) (.unionRight (ihH hwfR henfH))
  | @interCallableLeft P R _ _ _ hcompat _ _ =>
      cases hwfG with
      | intersection hwfCallable hwfF =>
          cases hwfCallable with
          | callable hwfP hwfR =>
              cases henf with
              | intersectionOk henfCallable henfFormula =>
                  have hformula := hcompat.toFormula
                  have hview :=
                    callable_enforce_ok_classification henfCallable hshape hheap halign
                  have wCallable : CheckedValueWitness gct cct heap v (.callable P R) :=
                    .mk (.callable hwfP hwfR) (.callable hview)
                  have wFormula :=
                    formula_enforce_ok_witness henfFormula hformula hshape hheap hwfct hwfF
                  exact .mk (.intersection (.callable hwfP hwfR) hwfF)
                    (.intersection wCallable wFormula)
  | @interCallableRight _ P R hcompat _ _ _ _ =>
      cases hwfG with
      | intersection hwfF hwfCallable =>
          cases hwfCallable with
          | callable hwfP hwfR =>
              cases henf with
              | intersectionOk henfFormula henfCallable =>
                  have hformula := hcompat.toFormula
                  have wFormula :=
                    formula_enforce_ok_witness henfFormula hformula hshape hheap hwfct hwfF
                  have hview :=
                    callable_enforce_ok_classification henfCallable hshape hheap halign
                  have wCallable : CheckedValueWitness gct cct heap v (.callable P R) :=
                    .mk (.callable hwfP hwfR) (.callable hview)
                  exact .mk (.intersection hwfF (.callable hwfP hwfR))
                    (.intersection wFormula wCallable)

/-- Checked-target wrapper around `enforce_ok_has_witness`. -/
theorem enforce_ok_has_checkedTargetWitness
    {T : CheckedTarget}
    (henf : EnforceValue gct heap v (compileBoundaryTarget T) .ok)
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct structural cct)
    (htarget : CheckedTargetTy gct (interpTarget T))
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueWitness gct cct heap v (interpTarget T) := by
  rw [compileBoundaryTarget_eq_compileBoundaryRaw_interp] at henf
  exact enforce_ok_has_witness henf hshape hheap hwfct halign
    (interpTarget T) rfl htarget hwf

/-- A formula witness can be re-enforced at the same formula contract and cannot blame there. -/
theorem formula_witness_same_contract
    (w : CheckedValueWitness gct cct heap v F)
    (hformula : FormulaGTy F)
    (hheap : CheckedHeapWellFormed gct cct heap) :
    EnforceValue gct heap v (compileBoundaryRaw F) .ok ∧
    (EnforceValue gct heap v (compileBoundaryRaw F) .blame → False) := by
  induction hformula generalizing v with
  | any => exact ⟨.unknown, fun h => by cases h⟩
  | class_ =>
      cases checkedValueWitness_class_view w with
      | objRef hlook hfind hmro hmem =>
          refine ⟨.classObjRefOk hlook hfind hmro hmem, fun h => ?_⟩
          cases h with
          | classObjRefBlame hlook' hfind' hmro' hnmem =>
              rw [hlook] at hlook'; cases hlook'
              rw [hfind] at hfind'; cases hfind'
              exact hnmem (gComputeMro_determinism hmro hmro' ▸ hmem)
  | bottom => match w with | .mk _ d => cases d
  | union _ _ ihL ihR =>
      simp only [compileBoundaryRaw]
      match w with
      | .mk (.union _ _) (.unionLeft wL) =>
          have ⟨henf, hnobl⟩ := ihL wL
          exact ⟨.unionLeft henf,
            fun h => by
              cases h with
              | unionBlame hbl _ => exact hnobl hbl⟩
      | .mk (.union _ _) (.unionRight wR) =>
          have ⟨henfH, hnoblH⟩ := ihR wR
          have hshape := checkedValueWitness_toShape wR
          have hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj :=
            fun oid hv => checkedAnyShape_objRef_lookup hshape hv
          rcases enforceValue_total hheap (compileBoundaryRaw _) v hvlook with
            henfL | hblameL
          · exact ⟨.unionLeft henfL,
              fun h => by
                cases h with
                | unionBlame hbl _ =>
                    exact absurd (enforceValue_deterministic henfL hbl) nofun⟩
          · exact ⟨.unionRight hblameL henfH,
              fun h => by
                cases h with
                | unionBlame _ hbl => exact hnoblH hbl⟩
  | intersection _ _ ihL ihR =>
      simp only [compileBoundaryRaw]
      match w with
      | .mk (.intersection _ _) (.intersection wL wR) =>
          have ⟨henfL, hnoblL⟩ := ihL wL
          have ⟨henfR, hnoblR⟩ := ihR wR
          exact ⟨.intersectionOk henfL henfR,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl => exact hnoblL hbl
              | intersectionBlameRight _ hbl => exact hnoblR hbl⟩
  | negClass =>
      match w with
      | .mk _ (.negClass _ hok) =>
          exact ⟨hok, fun hbl => absurd (enforceValue_deterministic hok hbl) nofun⟩

/-- A callable witness guarantees callable enforcement success and excludes callable blame. -/
private theorem callable_witness_same_contract_checkedTarget
    (w : CheckedValueWitness gct cct heap v (.callable P R)) :
    EnforceValue gct heap v (compileBoundaryRaw (.callable P R)) .ok ∧
    (EnforceValue gct heap v (compileBoundaryRaw (.callable P R)) .blame → False) := by
  cases checkedValueWitness_callable_view w with
  | objRefBoundMethod hlook _ _ =>
      refine ⟨.callableObjRefTransparentOk hlook, fun hbl => ?_⟩
      cases hbl with
      | callableObjRefBlame hlook' => rw [hlook] at hlook'; cases hlook'

/-- A witness at an admissible target can be re-enforced at the same contract and cannot blame there. -/
theorem checkedValueWitness_same_contract
    (w : CheckedValueWitness gct cct heap v G)
    (hchecked : CheckedTargetTy gct G)
    (hheap : CheckedHeapWellFormed gct cct heap) :
    EnforceValue gct heap v (compileBoundaryRaw G) .ok ∧
    (EnforceValue gct heap v (compileBoundaryRaw G) .blame → False) := by
  induction hchecked generalizing v with
  | classFormula hcf =>
      exact formula_witness_same_contract w hcf hheap
  | callable =>
      exact callable_witness_same_contract_checkedTarget w
  | union _ _ ihG ihH =>
      simp only [compileBoundaryRaw]
      match w with
      | .mk _ (.unionLeft wG) =>
          have ⟨henf, hnobl⟩ := ihG wG
          exact ⟨.unionLeft henf,
            fun h => by
              cases h with
              | unionBlame hbl _ => exact hnobl hbl⟩
      | .mk _ (.unionRight wH) =>
          have ⟨henfH, hnoblH⟩ := ihH wH
          have hshape := checkedValueWitness_toShape wH
          have hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj :=
            fun oid hv => checkedAnyShape_objRef_lookup hshape hv
          rcases enforceValue_total hheap (compileBoundaryRaw _) v hvlook with
            henfL | hblameL
          · exact ⟨.unionLeft henfL,
              fun h => by
                cases h with
                | unionBlame hbl _ =>
                    exact absurd (enforceValue_deterministic henfL hbl) nofun⟩
          · exact ⟨.unionRight hblameL henfH,
              fun h => by
                cases h with
                | unionBlame _ hbl => exact hnoblH hbl⟩
  | interCallableLeft _ _ hcompat _ _ =>
      simp only [compileBoundaryRaw]
      match w with
      | .mk _ (.intersection wCallable wFormula) =>
          have ⟨henfC, hnoblC⟩ :=
            callable_witness_same_contract_checkedTarget wCallable
          have hfF := hcompat.toFormula
          have ⟨henfF, hnoblF⟩ :=
            formula_witness_same_contract wFormula hfF hheap
          exact ⟨.intersectionOk henfC henfF,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl => exact hnoblC hbl
              | intersectionBlameRight _ hbl => exact hnoblF hbl⟩
  | interCallableRight hcompat _ _ _ _ =>
      simp only [compileBoundaryRaw]
      match w with
      | .mk _ (.intersection wFormula wCallable) =>
          have hfF := hcompat.toFormula
          have ⟨henfF, hnoblF⟩ :=
            formula_witness_same_contract wFormula hfF hheap
          have ⟨henfC, hnoblC⟩ :=
            callable_witness_same_contract_checkedTarget wCallable
          exact ⟨.intersectionOk henfF henfC,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl => exact hnoblF hbl
              | intersectionBlameRight _ hbl => exact hnoblC hbl⟩

/-- Checked-target wrapper around `checkedValueWitness_same_contract`. -/
theorem checkedValueWitness_same_checkedTarget
    {T : CheckedTarget}
    (w : CheckedValueWitness gct cct heap v (interpTarget T))
    (htarget : CheckedTargetTy gct (interpTarget T))
    (hheap : CheckedHeapWellFormed gct cct heap) :
    EnforceValue gct heap v (compileBoundaryTarget T) .ok ∧
    (EnforceValue gct heap v (compileBoundaryTarget T) .blame → False) := by
  simpa [compileBoundaryTarget_eq_compileBoundaryRaw_interp] using
    checkedValueWitness_same_contract w htarget hheap

end Checked

import FwPython.Gradual.TypeSystem.Safety
import FwPython.Gradual.TypeSystem.BoundaryCast
import FwPython.Gradual.TypeSystem.CheckedTargetSemantics
import FwPython.Gradual.Checked.Enforce
import FwPython.Gradual.Checked.HeapPreservation
import FwPython.Static.Subtyping.Inversion
import FwPython.Static.Subtyping.AbstractSemantics

/-! ## Enforcement classification helpers

These lemmas classify successful and failed enforcement on the exact
target fragment, and package the witness/no-blame facts used by
preservation. -/

namespace Checked

/-- Extract contract info from `CheckedMethodInReceiverMro`. -/
theorem checkedMethodInReceiverMro_contracts
    (halign : AlignedCheckedClassTable gct cct)
    (hmro : CheckedMethodInReceiverMro gct cct recvClassName cm) :
    cm.parameterContract = compileBoundaryRaw cm.paramTy ∧
    cm.returnContract = compileBoundaryRaw cm.returnTy := by
  obtain ⟨_recvCls, _mro, _hfind, _hmro, hfindCm⟩ := hmro
  obtain ⟨dname, dc, _, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
  exact halign.methodContractsCompiled dname dc _ hdc hcm_in_dc

/-- Extract well-formedness of method signature types from `CheckedMethodInReceiverMro`. -/
theorem checkedMethodInReceiverMro_wellFormed
    (halign : AlignedCheckedClassTable gct cct)
    (hmro : CheckedMethodInReceiverMro gct cct recvClassName cm) :
    WellFormedGTy gct cm.paramTy ∧ WellFormedGTy gct cm.returnTy := by
  obtain ⟨_recvCls, _mro, _hfind, _hmro, hfindCm⟩ := hmro
  obtain ⟨dname, dc, _, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
  exact halign.methodSignaturesWellFormed dname dc _ hdc hcm_in_dc

/-- Extract runtime/public admissibility of method signature types from
`CheckedMethodInReceiverMro`. -/
theorem checkedMethodInReceiverMro_runtimePublic
    (halign : AlignedCheckedClassTable gct cct)
    (hmro : CheckedMethodInReceiverMro gct cct recvClassName cm) :
    RuntimePublicCheckedTarget gct cm.paramTy ∧ RuntimePublicCheckedTarget gct cm.returnTy := by
  obtain ⟨_recvCls, _mro, _hfind, _hmro, hfindCm⟩ := hmro
  obtain ⟨dname, dc, _, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
  exact halign.methodSignaturesRuntimePublic dname dc _ hdc hcm_in_dc

/-- Successful callable enforcement is same-value success on a shallowly
    callable bound-method object reference. -/
theorem callable_enforce_ok_classification
    (henf : EnforceValue gct heap v (.callable domC codC) ℓ (.ok v'))
    (_hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (_halign : AlignedCheckedClassTable gct cct) :
    v' = v ∧ CheckedCallableView gct cct heap v := by
  cases henf with
  | callableObjRefTransparentOk hlook =>
      obtain ⟨recvObj, hrecv, hmroMethod⟩ := hheap.payloadReceiverValid _ _ _ _ hlook
      exact ⟨rfl, .objRefBoundMethod hlook hrecv hmroMethod⟩

/-- Formula enforcement success produces the same value. -/
theorem formula_enforce_ok_same_value
    (henf : EnforceValue gct heap v (compileBoundaryRaw F) ℓ (.ok v'))
    (hformula : FormulaGTy F) :
    v' = v := by
  induction hformula generalizing v v' with
  | any =>
      simp [compileBoundaryRaw] at henf
      cases henf; rfl
  | class_ =>
      simp [compileBoundaryRaw] at henf
      cases henf with | classObjRefOk => rfl
  | bottom => simp [compileBoundaryRaw] at henf; cases henf
  | union _ _ ihF ihG =>
      simp [compileBoundaryRaw] at henf
      cases henf with
      | unionLeft h =>
          exact ihF h
      | unionRight _ h =>
          exact ihG h
  | intersection _ _ ihF ihG =>
      simp [compileBoundaryRaw] at henf
      cases henf with
      | intersectionOk hF hG =>
          cases ihF hF
          exact ihG hG
  | negClass =>
      simp [compileBoundaryRaw] at henf
      cases henf with | negClassObjRefOk => rfl

/-- Formula enforcement success on a shaped value produces a witness. -/
theorem formula_enforce_ok_witness
    (henf : EnforceValue gct heap v (compileBoundaryRaw F) ℓ (.ok v'))
    (hformula : FormulaGTy F)
    (hsame : v' = v)
    (hshape : CheckedAnyShape gct cct heap v)
    (_hheap : CheckedHeapWellFormed gct cct heap)
    (_hwfct : WellFormedGClassTableCore gct)
    (hwfF : WellFormedGTy gct F) :
    CheckedValueWitness gct cct heap v' F := by
  subst v'
  induction hformula generalizing v with
  | any =>
      exact .mk .any (.any hshape)
  | @class_ cname =>
      simp [compileBoundaryRaw] at henf
      cases henf with | classObjRefOk hlook hfind hmro hmem =>
        exact .mk hwfF (.class_ (.objRef hlook hfind hmro hmem))
  | bottom => simp [compileBoundaryRaw] at henf; cases henf
  | union hcfF hcfG ihF ihG =>
      simp [compileBoundaryRaw] at henf
      cases hwfF with
      | union hwfL hwfR =>
          cases henf with
          | unionLeft hF =>
              exact .mk (.union hwfL hwfR) (.unionLeft (ihF hshape hwfL hF))
          | unionRight _ hG =>
              exact .mk (.union hwfL hwfR) (.unionRight (ihG hshape hwfR hG))
  | intersection hcfF hcfG ihF ihG =>
      simp [compileBoundaryRaw] at henf
      cases hwfF with
      | intersection hwfL hwfR =>
          cases henf with
          | intersectionOk hF hG =>
              cases formula_enforce_ok_same_value hF hcfF
              exact .mk (.intersection hwfL hwfR)
                (.intersection (ihF hshape hwfL hF) (ihG hshape hwfR hG))
  | @negClass cname =>
      simp [compileBoundaryRaw] at henf
      cases henf with | negClassObjRefOk hlook hfind hmro hnmem =>
        exact .mk hwfF
          (.negClass hshape (fun _ => .negClassObjRefOk hlook hfind hmro hnmem))

/-- Enforcement soundness for admissible target types, phrased over the
internal `CheckedTargetTy` admissibility predicate. -/
private theorem enforce_ok_has_witness_checkedTarget
    (henf : EnforceValue gct heap v c ℓ (.ok v'))
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct) :
    ∀ G, CompilesBoundary G c → CheckedTargetTy gct G → WellFormedGTy gct G →
      CheckedValueWitness gct cct heap v' G := by
  intro G hcb hchecked hwfG
  subst hcb
  induction hchecked with
  | classFormula hcf =>
      exact formula_enforce_ok_witness henf hcf
        (formula_enforce_ok_same_value henf hcf) hshape hheap hwfct hwfG
  | @callable P R _ _ _ _ =>
      simp [compileBoundaryRaw] at henf
      cases hwfG with
      | callable hwfP hwfR =>
          obtain ⟨rfl, hview⟩ := callable_enforce_ok_classification henf hshape hheap halign
          exact .mk (.callable hwfP hwfR) (.callable hview)
  | union hcheckedG hcheckedH ihG ihH =>
      simp [compileBoundaryRaw] at henf
      cases hwfG with
      | union hwfL hwfR =>
          cases henf with
          | unionLeft henfG =>
              exact .mk (.union hwfL hwfR) (.unionLeft (ihG hwfL henfG))
          | unionRight _ henfH =>
              exact .mk (.union hwfL hwfR) (.unionRight (ihH hwfR henfH))
  | @interCallableLeft P R _ _ _ hcompat _ _ =>
      simp [compileBoundaryRaw] at henf
      cases hwfG with
      | intersection hwfCallable hwfF =>
          cases hwfCallable with
          | callable hwfP hwfR =>
              cases henf with
              | intersectionOk henfCallable henfFormula =>
                  cases enforce_ok_same_value henfCallable
                  have hformula := hcompat.toFormula
                  cases formula_enforce_ok_same_value henfFormula hformula
                  have ⟨_, hview⟩ :=
                    callable_enforce_ok_classification henfCallable hshape hheap halign
                  have wCallable : CheckedValueWitness gct cct heap v (.callable P R) :=
                    .mk (.callable hwfP hwfR) (.callable hview)
                  have wFormula :=
                    formula_enforce_ok_witness henfFormula hformula rfl hshape hheap hwfct hwfF
                  exact .mk (.intersection (.callable hwfP hwfR) hwfF)
                    (.intersection wCallable wFormula)
  | @interCallableRight _ P R hcompat _ _ _ _ =>
      simp [compileBoundaryRaw] at henf
      cases hwfG with
      | intersection hwfF hwfCallable =>
          cases hwfCallable with
          | callable hwfP hwfR =>
              cases henf with
              | intersectionOk henfFormula henfCallable =>
                  have hformula := hcompat.toFormula
                  cases formula_enforce_ok_same_value henfFormula hformula
                  have ⟨hsameCallable, hview⟩ :=
                    callable_enforce_ok_classification henfCallable hshape hheap halign
                  cases hsameCallable
                  have wFormula :=
                    formula_enforce_ok_witness henfFormula hformula rfl hshape hheap hwfct hwfF
                  have wCallable : CheckedValueWitness gct cct heap v (.callable P R) :=
                    .mk (.callable hwfP hwfR) (.callable hview)
                  exact .mk (.intersection hwfF (.callable hwfP hwfR))
                    (.intersection wFormula wCallable)

/-- Enforcement soundness for admissible target types. -/
theorem enforce_ok_has_witness
    (henf : EnforceValue gct heap v c ℓ (.ok v'))
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct) :
    ∀ G, CompilesBoundary G c → RuntimePublicAnnotation gct G → WellFormedGTy gct G →
      CheckedValueWitness gct cct heap v' G := by
  intro G hcb hchecked hwfG
  exact enforce_ok_has_witness_checkedTarget henf hshape hheap hwfct halign
    G hcb (runtimePublicAnnotation_checked hchecked) hwfG

/-- Checked-target wrapper around `enforce_ok_has_witness`. -/
theorem enforce_ok_has_checkedTargetWitness
    {T : CheckedTarget}
    {labels : BoundaryLabels (compileBoundaryTarget T)}
    (henf : EnforceValue gct heap v (compileBoundaryTarget T) labels (.ok v'))
    (hshape : CheckedAnyShape gct cct heap v)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct)
    (htarget : RuntimePublicCheckedTarget gct T)
    (hwf : WellFormedGTy gct (interpTarget T)) :
    CheckedValueWitness gct cct heap v' (interpTarget T) := by
  let labels' : BoundaryLabels (compileBoundaryRaw (interpTarget T)) :=
    castBoundaryLabels (compileBoundaryTarget_eq_compileBoundaryRaw_interp T) labels
  have henf' :
      EnforceValue gct heap v (compileBoundaryRaw (interpTarget T)) labels' (.ok v') := by
    exact enforceValue_castBoundary_forward
      (compileBoundaryTarget_eq_compileBoundaryRaw_interp T)
      labels
      henf
  exact enforce_ok_has_witness henf' hshape hheap hwfct halign
    (interpTarget T) rfl (runtimePublicAnnotation_mk htarget.2) hwf

/-- A formula witness can be re-enforced at the same formula contract and
    cannot blame there. -/
theorem formula_witness_same_contract
    (w : CheckedValueWitness gct cct heap v F)
    (hformula : FormulaGTy F)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct) :
    (∃ v',
        EnforceValue gct heap v (compileBoundaryRaw F) ℓ (.ok v') ∧
        CheckedValueWitness gct cct heap v' F) ∧
    (EnforceValue gct heap v (compileBoundaryRaw F) ℓ (.blame ℓ.direct) → False) := by
  induction hformula generalizing v with
  | any =>
      simp [compileBoundaryRaw]
      exact ⟨⟨v, .unknown, w⟩, fun h => by cases h⟩
  | @class_ cname =>
      simp [compileBoundaryRaw]
      cases checkedValueWitness_class_view w with
      | objRef hlook hfind hmro hmem =>
          exact ⟨⟨_, .classObjRefOk hlook hfind hmro hmem, w⟩,
            fun h => by
              cases h with
              | classObjRefBlame hlook' hfind' hmro' hnmem =>
                  rw [hlook] at hlook'; cases hlook'
                  rw [hfind] at hfind'; cases hfind'
                  exact hnmem (gComputeMro_determinism hmro hmro' ▸ hmem)⟩
  | bottom =>
      simp [compileBoundaryRaw]
      match w with | .mk _ d => cases d
  | union hcfL hcfR ihL ihR =>
      simp [compileBoundaryRaw]
      match w with
      | .mk (.union hwfL hwfR) (.unionLeft wL) =>
          have ⟨⟨v', henf, wL'⟩, hnobl⟩ := ihL (ℓ := ℓ.subtree (.unionLeft .here)) wL
          exact ⟨⟨v', .unionLeft henf, .mk (.union hwfL hwfR) (.unionLeft wL')⟩,
            fun h => by
              cases h with
              | unionBlame hbl _ =>
                  exact hnobl hbl⟩
      | .mk (.union hwfL hwfR) (.unionRight wR) =>
          have ⟨⟨v', henf, wR'⟩, hnobl⟩ := ihR (ℓ := ℓ.subtree (.unionRight .here)) wR
          have hshape := checkedValueWitness_toShape wR
          have hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj :=
            fun oid hv => checkedAnyShape_objRef_lookup hshape hv
          rcases enforceValue_total hheap hwfct (compileBoundaryRaw _)
              (ℓ.subtree (.unionLeft .here)) v hvlook with
            ⟨vL, henfL⟩ | hblameL
          · have hsame := formula_enforce_ok_same_value henfL hcfL
            subst hsame
            exact ⟨⟨vL, .unionLeft henfL,
                .mk (.union hwfL hwfR)
                  (.unionLeft
                    (formula_enforce_ok_witness henfL hcfL rfl hshape hheap hwfct hwfL))⟩,
              fun h => by
                cases h with
                | unionBlame hbl _ =>
                    exact absurd (enforceValue_deterministic henfL hbl) nofun⟩
          · exact ⟨⟨v', .unionRight hblameL henf, .mk (.union hwfL hwfR) (.unionRight wR')⟩,
              fun h => by
                cases h with
                | unionBlame _ hbl =>
                    exact hnobl hbl⟩
  | intersection hcfL hcfR ihL ihR =>
      simp [compileBoundaryRaw]
      match w with
      | .mk (.intersection hwfL hwfR) (.intersection wL wR) =>
          have ⟨⟨vL, henfL, wL'⟩, hnoblL⟩ :=
            ihL (ℓ := ℓ.subtree (.intersectionLeft .here)) wL
          have hsame := formula_enforce_ok_same_value henfL hcfL
          subst hsame
          have ⟨⟨vR, henfR, wR'⟩, hnoblR⟩ :=
            ihR (ℓ := ℓ.subtree (.intersectionRight .here)) wR
          have hsame := formula_enforce_ok_same_value henfR hcfR
          subst hsame
          exact ⟨⟨vR, .intersectionOk henfL henfR,
              .mk (.intersection hwfL hwfR) (.intersection wL' wR')⟩,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl =>
                  exact hnoblL hbl
              | intersectionBlameRight hok hbl =>
                  cases formula_enforce_ok_same_value hok hcfL
                  exact hnoblR hbl⟩
  | @negClass cname =>
      match w with
      | .mk hwf (.negClass hshape hok) =>
          exact ⟨⟨v, hok ℓ, .mk hwf (.negClass hshape hok)⟩,
            fun hbl => absurd (enforceValue_deterministic (hok ℓ) hbl) nofun⟩

/-- A callable witness guarantees same-value callable enforcement success. -/
private theorem callable_witness_same_contract_checkedTarget
    (w : CheckedValueWitness gct cct heap v (.callable P R)) :
    EnforceValue gct heap v (compileBoundaryRaw (.callable P R)) ℓ (.ok v) ∧
    (EnforceValue gct heap v (compileBoundaryRaw (.callable P R)) ℓ (.blame ℓ.direct) → False) := by
  simp only [compileBoundaryRaw]
  cases checkedValueWitness_callable_view w with
  | objRefBoundMethod hlook _ _ =>
      exact ⟨.callableObjRefTransparentOk hlook,
        fun hbl => by
          cases hbl with
          | callableObjRefBlame hlook' =>
              rw [hlook] at hlook'; cases hlook'⟩

/-- A witness at an admissible target can be re-enforced at the same
    contract and cannot blame there, phrased over the internal
    `CheckedTargetTy` admissibility predicate. -/
private theorem checkedValueWitness_same_contract_checkedTarget
    (w : CheckedValueWitness gct cct heap v G)
    (hchecked : CheckedTargetTy gct G)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct) :
    (∃ v',
        EnforceValue gct heap v (compileBoundaryRaw G) ℓ (.ok v') ∧
        CheckedValueWitness gct cct heap v' G) ∧
    (EnforceValue gct heap v (compileBoundaryRaw G) ℓ (.blame ℓ.direct) → False) := by
  induction hchecked generalizing v with
  | classFormula hcf =>
      exact formula_witness_same_contract w hcf hheap hwfct
  | callable htP htR _ _ =>
      have ⟨henfOk, hnobl⟩ :=
        callable_witness_same_contract_checkedTarget w (ℓ := ℓ)
      exact ⟨⟨v, henfOk, w⟩, hnobl⟩
  | union hcheckedG hcheckedH ihG ihH =>
      simp [compileBoundaryRaw]
      obtain ⟨hwfG, hwfH⟩ : WellFormedGTy gct _ ∧ WellFormedGTy gct _ := by
        cases w.wf with | union h1 h2 => exact ⟨h1, h2⟩
      match w with
      | .mk _ (.unionLeft wG) =>
          have ⟨⟨v', henf, w'⟩, hnobl⟩ := ihG (ℓ := ℓ.subtree (.unionLeft .here)) wG
          exact ⟨⟨v', .unionLeft henf, .mk (.union hwfG hwfH) (.unionLeft w')⟩,
            fun h => by
              cases h with
              | unionBlame hbl _ =>
                  exact hnobl hbl⟩
      | .mk _ (.unionRight wH) =>
          have ⟨⟨v', henfH, wH'⟩, hnoblH⟩ := ihH (ℓ := ℓ.subtree (.unionRight .here)) wH
          have hshape := checkedValueWitness_toShape wH
          have hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj :=
            fun oid hv => checkedAnyShape_objRef_lookup hshape hv
          rcases enforceValue_total hheap hwfct (compileBoundaryRaw _)
              (ℓ.subtree (.unionLeft .here)) v hvlook with
            ⟨vL, henfL⟩ | hblameL
          · have wL :=
              enforce_ok_has_witness_checkedTarget henfL hshape hheap hwfct halign
                _ rfl hcheckedG hwfG
            exact ⟨⟨vL, .unionLeft henfL, .mk (.union hwfG hwfH) (.unionLeft wL)⟩,
              fun h => by
                cases h with
                | unionBlame hbl _ =>
                    exact absurd (enforceValue_deterministic henfL hbl) nofun⟩
          · exact ⟨⟨v', .unionRight hblameL henfH, .mk (.union hwfG hwfH) (.unionRight wH')⟩,
              fun h => by
                cases h with
                | unionBlame _ hbl =>
                    exact hnoblH hbl⟩
  | interCallableLeft htP htR hcompat _ _ =>
      simp [compileBoundaryRaw]
      obtain ⟨hwfCallable, hwfF⟩ : WellFormedGTy gct _ ∧ WellFormedGTy gct _ := by
        cases w.wf with | intersection h1 h2 => exact ⟨h1, h2⟩
      match w with
      | .mk _ (.intersection wCallable wFormula) =>
          have ⟨henfC, hnoblC⟩ :=
            callable_witness_same_contract_checkedTarget wCallable
              (ℓ := ℓ.subtree (.intersectionLeft .here))
          have hfF := hcompat.toFormula
          obtain ⟨⟨vF, henfF, _⟩, hnoblF⟩ :=
            formula_witness_same_contract wFormula hfF hheap hwfct
              (ℓ := ℓ.subtree (.intersectionRight .here))
          have hsameF := formula_enforce_ok_same_value henfF hfF
          subst hsameF
          exact ⟨⟨_, .intersectionOk henfC henfF,
              .mk (.intersection hwfCallable hwfF) (.intersection wCallable wFormula)⟩,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl =>
                  exact hnoblC hbl
              | intersectionBlameRight hok hbl =>
                  have hsame := enforce_ok_same_value hok
                  subst hsame
                  exact hnoblF hbl⟩
  | interCallableRight hcompat htP htR _ _ =>
      simp [compileBoundaryRaw]
      obtain ⟨hwfF, hwfCallable⟩ : WellFormedGTy gct _ ∧ WellFormedGTy gct _ := by
        cases w.wf with | intersection h1 h2 => exact ⟨h1, h2⟩
      match w with
      | .mk _ (.intersection wFormula wCallable) =>
          have hfF := hcompat.toFormula
          obtain ⟨⟨vF, henfF, _⟩, hnoblF⟩ :=
            formula_witness_same_contract wFormula hfF hheap hwfct
              (ℓ := ℓ.subtree (.intersectionLeft .here))
          have hsameF := formula_enforce_ok_same_value henfF hfF
          subst hsameF
          have ⟨henfC, hnoblC⟩ :=
            callable_witness_same_contract_checkedTarget wCallable
              (ℓ := ℓ.subtree (.intersectionRight .here))
          exact ⟨⟨_, .intersectionOk henfF henfC,
              .mk (.intersection hwfF hwfCallable) (.intersection wFormula wCallable)⟩,
            fun h => by
              cases h with
              | intersectionBlameLeft hbl =>
                  exact hnoblF hbl
              | intersectionBlameRight hok hbl =>
                  have hsame := formula_enforce_ok_same_value hok hfF
                  subst hsame
                  exact hnoblC hbl⟩

/-- A witness at an admissible target can be re-enforced at the same
    contract and cannot blame there. -/
theorem checkedValueWitness_same_contract
    (w : CheckedValueWitness gct cct heap v G)
    (hchecked : RuntimePublicAnnotation gct G)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct) :
    (∃ v',
        EnforceValue gct heap v (compileBoundaryRaw G) ℓ (.ok v') ∧
        CheckedValueWitness gct cct heap v' G) ∧
    (EnforceValue gct heap v (compileBoundaryRaw G) ℓ (.blame ℓ.direct) → False) := by
  exact checkedValueWitness_same_contract_checkedTarget
    w (runtimePublicAnnotation_checked hchecked) hheap hwfct halign

/-- Checked-target wrapper around `checkedValueWitness_same_contract`. -/
theorem checkedValueWitness_same_checkedTarget
    {T : CheckedTarget}
    {labels : BoundaryLabels (compileBoundaryTarget T)}
    (w : CheckedValueWitness gct cct heap v (interpTarget T))
    (htarget : RuntimePublicCheckedTarget gct T)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct) :
    EnforceValue gct heap v (compileBoundaryTarget T) labels (.ok v) ∧
    (EnforceValue gct heap v (compileBoundaryTarget T) labels (.blame labels.direct) → False) := by
  let labels' : BoundaryLabels (compileBoundaryRaw (interpTarget T)) :=
    castBoundaryLabels (compileBoundaryTarget_eq_compileBoundaryRaw_interp T) labels
  obtain ⟨⟨v', henf, _⟩, hnobl⟩ :=
    checkedValueWitness_same_contract
      (ℓ := labels')
      w
      (runtimePublicAnnotation_mk htarget.2)
      hheap
      hwfct
      halign
  have hsame : v' = v := enforce_ok_same_value henf
  constructor
  · simpa [hsame] using
      (enforceValue_castBoundary
        (compileBoundaryTarget_eq_compileBoundaryRaw_interp T)
        labels
        henf)
  · intro hbl
    have hbl'' :
        EnforceValue gct heap v
          (compileBoundaryRaw (interpTarget T))
          labels'
          (.blame labels.direct) := by
      exact enforceValue_castBoundary_forward
        (compileBoundaryTarget_eq_compileBoundaryRaw_interp T)
        labels
        hbl
    have hdir : labels'.direct = labels.direct := by
      exact castBoundaryLabels_direct
        (compileBoundaryTarget_eq_compileBoundaryRaw_interp T)
        labels
    have hbl' :
        EnforceValue gct heap v
          (compileBoundaryRaw (interpTarget T))
          labels'
          (.blame labels'.direct) := by
      simpa [hdir] using hbl''
    exact hnobl hbl'

end Checked

import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.ValueSemantics
import FwPython.Gradual.TypeSystem.ObligationExactness
import FwPython.Gradual.Checked.HeapPreservation

/-! # Source-level blame adequacy

Final checked-machine blame is adequate when the runtime cause carried by the
final `BlameInfo` payload falsifies the source obligation stored in that same
payload. The proof tracks exact source obligations through compiled checked
syntax and continuation frames, then uses local no-false-positive lemmas at the
three rules that create checked blame.
-/

namespace Checked

/-- A checked-runtime value satisfies the reported source obligation in the
current checked heap. Source sites identify reported locations; the semantic
truth of a type or attribute obligation depends on the gradual type or
attribute name, not on the source site itself. -/
def SourceObligationHolds
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (value : CheckedValue) :
    SourceObligation -> Prop
  | .hasType _ G =>
      CheckedValueSatisfies gct cct heap value (checkedTargetOfGTy G)
  | .hasAttribute _ attrName =>
      exists oid obj cls mro gm,
        value = .objRef oid /\
        heap.lookup oid = some obj /\
        findGClass gct obj.className = some cls /\
        GComputeMro gct cls mro /\
        findGMethodInMro gct mro attrName = some gm

/-- The runtime cause carried by final blame describes a false source
obligation in the current heap. Mismatched operation/obligation pairs, such as
boundary causes for attribute obligations or missing-attribute causes for type
obligations, are rejected. Source sites identify reported locations; boundary
causes report expression or method-return sites, while method-parameter causes
report method-parameter sites. -/
def CauseViolatesObligation
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    BlameCause -> SourceObligation -> Prop
  | .boundary value target, .hasType (.expression site) G =>
      target = checkedTargetOfGTy G /\
      Not (SourceObligationHolds gct cct heap value (.hasType (.expression site) G))
  | .boundary value target, .hasType (.methodReturn className methodName) G =>
      target = checkedTargetOfGTy G /\
      Not (SourceObligationHolds gct cct heap value
        (.hasType (.methodReturn className methodName) G))
  | .boundary _ _, .hasType (.methodParameter _ _) _ =>
      False
  | .missingAttribute receiver attrName, .hasAttribute site expectedName =>
      attrName = expectedName /\
      Not (SourceObligationHolds gct cct heap receiver (.hasAttribute site expectedName))
  | .methodParameter argument method, .hasType (.methodParameter className methodName) G =>
      method.parameterObligation = .hasType (.methodParameter className methodName) G /\
      method.paramTy = checkedTargetOfGTy G /\
      Not (SourceObligationHolds gct cct heap argument
        (.hasType (.methodParameter className methodName) G))
  | .methodParameter _ _, .hasType (.expression _) _ => False
  | .methodParameter _ _, .hasType (.methodReturn _ _) _ => False
  | _, _ =>
      False

/-- The runtime cause carried by a blame payload satisfies the reported source
obligation in the current heap. Matching cases mirror
`CauseViolatesObligation`; mismatched cause/obligation shapes are false. -/
def CauseSatisfiesObligation
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    BlameCause -> SourceObligation -> Prop
  | .boundary value target, .hasType (.expression site) G =>
      target = checkedTargetOfGTy G /\
      SourceObligationHolds gct cct heap value (.hasType (.expression site) G)
  | .boundary value target, .hasType (.methodReturn className methodName) G =>
      target = checkedTargetOfGTy G /\
      SourceObligationHolds gct cct heap value
        (.hasType (.methodReturn className methodName) G)
  | .boundary _ _, .hasType (.methodParameter _ _) _ =>
      False
  | .missingAttribute receiver attrName, .hasAttribute site expectedName =>
      attrName = expectedName /\
      SourceObligationHolds gct cct heap receiver (.hasAttribute site expectedName)
  | .methodParameter argument method, .hasType (.methodParameter className methodName) G =>
      method.parameterObligation = .hasType (.methodParameter className methodName) G /\
      method.paramTy = checkedTargetOfGTy G /\
      SourceObligationHolds gct cct heap argument
        (.hasType (.methodParameter className methodName) G)
  | .methodParameter _ _, .hasType (.expression _) _ =>
      False
  | .methodParameter _ _, .hasType (.methodReturn _ _) _ =>
      False
  | _, _ =>
      False

private theorem causeSatisfies_not_violates
    (hsat : CauseSatisfiesObligation gct cct heap cause obligation)
    (hviol : CauseViolatesObligation gct cct heap cause obligation) :
    False := by
  cases cause <;> cases obligation <;> (try rename_i site _; cases site) <;>
    simp [CauseSatisfiesObligation, CauseViolatesObligation] at hsat hviol <;>
    first
      | exact hviol.2 hsat.2
      | exact hviol.2.2 hsat.2.2

/-- Checked control is exact: expressions have exact stored obligations, values
and runtime errors carry no checked blame payload, and active blame already
records a violated source obligation in the current heap. -/
private def CheckedControlObligationsExact
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    Checked.Control -> Prop
  | .expr expr => CheckedExprObligationsExact gct expr
  | .val _ => True
  | .runtimeError _ => True
  | .blame info =>
      Checked.CauseViolatesObligation gct cct heap info.cause info.obligation

/-- Heap well-formedness plus exact source obligations for the active control
and continuation. The environment is intentionally absent: adequacy is
invariant under environment changes because blame payload exactness depends on
the heap, control, and pending frames only. -/
private structure CheckedBlameAdequacyState
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (state : Checked.State) : Prop where
  /-- The heap invariants needed by enforcement and method provenance. -/
  heap_well_formed : CheckedHeapWellFormed gct cct state.heap
  /-- Exactness of the current control component. -/
  control_exact :
    CheckedControlObligationsExact gct cct state.heap state.control
  /-- Exactness of all pending continuation frames. -/
  continuation_exact :
    CheckedContinuationObligationsExact gct state.continuation

private theorem boundary_blame_violates_obligation
    (hexact : BoundaryObligationExact gct target obligation)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (henforce :
      EnforceValue gct heap value
        (compileBoundaryTarget target)
        .blame) :
    Checked.CauseViolatesObligation gct cct heap
      (.boundary value target)
      obligation := by
  rcases hexact with ⟨site, gradualType, hobligation, hsite, htarget, hchecked, hwf⟩
  subst obligation
  subst target
  cases site
  case methodParameter => cases hsite
  all_goals
    exact ⟨rfl, fun hholds =>
      (checkedValueSatisfies_same_contract
        (T := checkedTargetOfGTy gradualType)
        hholds hheap (by simpa) (by simpa)).2
          (by simpa [compileBoundaryTarget_eq_compileBoundaryRaw_interp] using henforce)⟩

private theorem methodParameter_blame_violates_obligation
    (hexact : CheckedMethodObligationsExact gct method)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (henforce :
      EnforceValue gct heap argument
        (compileBoundaryTarget method.paramTy)
        .blame) :
    Checked.CauseViolatesObligation gct cct heap
      (.methodParameter argument method)
      method.parameterObligation := by
  obtain ⟨⟨_, _, gradualType, hobligation, htarget, hchecked, hwf⟩, _, _⟩ := hexact
  rw [htarget] at henforce
  rw [hobligation]
  exact ⟨hobligation, htarget, fun hholds =>
    (checkedValueSatisfies_same_contract (T := checkedTargetOfGTy gradualType)
      hholds hheap (by simpa) (by simpa)).2
        (by simpa [compileBoundaryTarget_eq_compileBoundaryRaw_interp] using henforce)⟩

private theorem missingAttribute_blame_violates_obligation
    (hcompiled : Checked.IsCompiledClassTable gct hwfct cct)
    (hexact : AttributeObligationExact attrName obligation)
    (hlookupObj : heap.lookup objOid = some obj)
    (hfindCls : findGClass gct obj.className = some cls)
    (hMro : GComputeMro gct cls mro)
    (hnotfound : findCheckedMethodInMro cct mro attrName = none) :
    Checked.CauseViolatesObligation gct cct heap
      (.missingAttribute (.objRef objOid) attrName)
      obligation := by
  rcases hexact with ⟨site, hobligation⟩
  subst obligation
  refine ⟨rfl, ?_⟩
  intro hholds
  rcases hholds with
    ⟨semanticOid, semanticObj, semanticCls, semanticMro, sourceMethod,
      hreceiver, hsemanticLookup, hsemanticClass, hsemanticMro, hsourceLookup⟩
  cases hreceiver
  rw [hlookupObj] at hsemanticLookup
  cases hsemanticLookup
  rw [hfindCls] at hsemanticClass
  cases hsemanticClass
  have hmroEq : semanticMro = mro :=
    gComputeMro_determinism hsemanticMro hMro
  have hsourceLookupMro : findGMethodInMro gct mro attrName = some sourceMethod := by
    simpa [hmroEq] using hsourceLookup
  let lookup := Checked.isCompiledClassTable_findMethodInMro hcompiled hsourceLookupMro
  have hfound : findCheckedMethodInMro cct mro attrName = some lookup.member2 :=
    lookup.found
  rw [hnotfound] at hfound
  cases hfound

private theorem initialState_blameAdequacyState
    (hcompiled : Checked.ElaboratesProgramAt gp P cp) :
    CheckedBlameAdequacyState
      gp.classes
      cp.classes
      (Checked.initialState cp) := by
  have programExact := obligationsExact_of_elaboration hcompiled
  refine ⟨Checked.checkedHeapInitial_wellFormed hcompiled.hwfct.raw, ?_, trivial⟩
  rw [Checked.initialState, Checked.expressionState]
  exact programExact.main_exact

private theorem step_preserves_blameAdequacyState
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hstate :
      CheckedBlameAdequacyState
        gp.classes cp.classes s)
    (hstep : Checked.Step gp.classes cp.classes s s') :
    CheckedBlameAdequacyState
      gp.classes cp.classes s' := by
  rcases hstate with ⟨hheap, hcontrol, hcontinuation⟩
  have hheap' :=
    Checked.step_preserves_checkedHeapWellFormed hstep
      hheap hcompiled.hwfct.raw
  cases hstep with
  | returnCallCalleeBound hlookup =>
      refine ⟨hheap', ?_, ?_⟩
      · exact hcontinuation.1.1
      · exact ⟨
          ⟨checkedMethodObligationsExact_of_boundMethod_lookup
              hcompiled.classes_elab hheap hlookup,
            hcontinuation.1.2⟩,
          hcontinuation.2⟩
  | returnAwaitArgumentOk _henforce =>
      refine ⟨hheap', ?_, ?_⟩
      · exact hcontinuation.1.1.2.2
      · exact ⟨hcontinuation.1.1.2.1,
          ⟨hcontinuation.1.2,
            ⟨trivial, hcontinuation.2⟩⟩⟩
  | returnEnforceBlame henforce =>
      refine ⟨hheap', ?_, hcontinuation.2⟩
      exact boundary_blame_violates_obligation
        hcontinuation.1 hheap henforce
  | returnDynAttrAccessNotFound hlookupObj hfindCls hMro hnotfound =>
      refine ⟨hheap', ?_, hcontinuation.2⟩
      exact missingAttribute_blame_violates_obligation
        hcompiled.classes_elab hcontinuation.1
        hlookupObj hfindCls hMro hnotfound
  | returnAwaitArgumentBlame henforce =>
      refine ⟨hheap', ?_, hcontinuation.2⟩
      exact methodParameter_blame_violates_obligation
        hcontinuation.1.1 hheap henforce
  | _ =>
      refine ⟨hheap', ?_, ?_⟩ <;>
        simp_all [CheckedControlObligationsExact, CheckedContinuationObligationsExact,
          CheckedFrameObligationsExact,
          CheckedExprObligationsExact]

private theorem steps_preserve_blameAdequacyState
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hsteps :
      Checked.Steps gp.classes cp.classes
        startState finalState)
    (hstate :
      CheckedBlameAdequacyState
        gp.classes cp.classes startState) :
    CheckedBlameAdequacyState
      gp.classes cp.classes finalState := by
  induction hsteps with
  | refl => exact hstate
  | step hstep _ ih =>
      exact ih (step_preserves_blameAdequacyState hcompiled hstate hstep)

/-- Final checked-machine blame is source-level adequate: the reported runtime
cause violates the reported source obligation in the final heap. -/
theorem blame_adequacy
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hsteps :
      Checked.Steps gp.classes cp.classes
        (Checked.initialState cp)
        finalState)
    (hfinal :
      Checked.finalResult? finalState =
        some (heap', CheckedResult.blame info)) :
    Checked.CauseViolatesObligation
      gp.classes
      cp.classes
      heap'
      info.cause
      info.obligation := by
  have hfinalState :=
    steps_preserve_blameAdequacyState hcompiled hsteps
      (initialState_blameAdequacyState hcompiled)
  obtain ⟨hheap, hcontrol, _hcontinuation⟩ :=
    Checked.finalResult_blame_control hfinal
  have hcontrolExact := hfinalState.control_exact
  rw [hcontrol] at hcontrolExact
  rw [← hheap]
  exact hcontrolExact

/-- A final blame whose cause satisfies its reported source obligation
contradicts blame adequacy, which proves that final blame violates the same
obligation. -/
theorem no_final_blame_of_causeSatisfies
    (hcompiled : Checked.ElaboratesProgramAt gp P cp)
    (hsteps :
      Checked.Steps gp.classes cp.classes
        (Checked.initialState cp)
        finalState)
    (hfinal :
      Checked.finalResult? finalState =
        some (heap', CheckedResult.blame info))
    (hsat :
      Checked.CauseSatisfiesObligation
        gp.classes cp.classes heap' info.cause info.obligation) :
    False :=
  causeSatisfies_not_violates hsat
    (Checked.blame_adequacy hcompiled hsteps hfinal)

end Checked

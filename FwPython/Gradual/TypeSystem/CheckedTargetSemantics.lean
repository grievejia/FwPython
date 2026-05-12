import FwPython.Gradual.TypeSystem.CheckedTargetSyntax
import FwPython.Gradual.TypeSystem.Checked.Typing
import FwPython.Gradual.TypeSystem.TargetAdmissibility

/-! # Semantic bridges for explicit checked targets -/

theorem checkedTargetTy_checkedTargetOfGTy_iff
    (gct : GClassTable) (G : GTy) :
    CheckedTargetTy gct (interpTarget (checkedTargetOfGTy G)) ↔
      CheckedTargetTy gct G := by
  rw [interpTarget_checkedTargetOfGTy]

theorem checkedTargetTy_checkedTargetOfBoundaryContract_iff
    (gct : GClassTable) (c : BoundaryContract) :
    CheckedTargetTy gct (interpTarget (checkedTargetOfBoundaryContract c)) ↔
      CheckedTargetTy gct (boundaryMeaning c) := by
  rw [interpTarget_checkedTargetOfBoundaryContract]

theorem checkedTargetOfRuntimePublicTy_runtimePublic
    (hchecked : CheckedTargetTy gct (runtimePublicTy G)) :
    RuntimePublicCheckedTarget gct (checkedTargetOfRuntimePublicTy G) := by
  refine ⟨checkedTargetOfRuntimePublicTy_runtimePublic_shape G, ?_⟩
  simpa using hchecked

theorem checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
    (hchecked : CheckedTargetTy gct G) :
    RuntimePublicCheckedTarget gct (checkedTargetOfRuntimePublicTy G) := by
  apply checkedTargetOfRuntimePublicTy_runtimePublic
  simpa [runtimePublicTy_id] using checkedTargetTy_runtimePublicTy hchecked

theorem checkedTargetOfGTy_runtimePublic_of_checked
    (hchecked : CheckedTargetTy gct G) :
    RuntimePublicCheckedTarget gct (checkedTargetOfGTy G) := by
  simpa [checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
    checkedTargetOfRuntimePublicTy_runtimePublic_of_checked (gct := gct) hchecked

theorem checkedTargetOfBoundaryContract_runtimePublic
    (hcompiled : CompilesBoundary G c)
    (hchecked : CheckedTargetTy gct G) :
    RuntimePublicCheckedTarget gct (checkedTargetOfBoundaryContract c) := by
  cases hcompiled
  simpa using
    checkedTargetOfGTy_runtimePublic_of_checked (gct := gct) hchecked

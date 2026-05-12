import FwPython.Gradual.TypeSystem.BoundaryPrecision
import FwPython.Gradual.TypeSystem.CheckedTargetSyntax

/-! # Precision for explicit checked targets -/

/-- Structural precision on explicit checked targets. Runtime/checked precision
relations compare stored `CheckedTarget` annotations through this judgment. -/
inductive CheckedTargetPrecision : CheckedTarget → CheckedTarget → Prop where
  | refl :
      CheckedTargetPrecision T T
  | toAny :
      CheckedTargetPrecision T .any
  | callable :
      CheckedTargetPrecision paramTy₁ paramTy₂ →
      CheckedTargetPrecision returnTy₁ returnTy₂ →
      CheckedTargetPrecision
        (.callable paramTy₁ returnTy₁)
        (.callable paramTy₂ returnTy₂)
  | union :
      CheckedTargetPrecision left₁ left₂ →
      CheckedTargetPrecision right₁ right₂ →
      CheckedTargetPrecision
        (.union left₁ right₁)
        (.union left₂ right₂)
  | intersection :
      CheckedTargetPrecision left₁ left₂ →
      CheckedTargetPrecision right₁ right₂ →
      CheckedTargetPrecision
        (.intersection left₁ right₁)
        (.intersection left₂ right₂)

theorem checkedTargetPrecision_refl
    (T : CheckedTarget) :
    CheckedTargetPrecision T T :=
  .refl

theorem checkedTargetPrecision_trans
    (h₁ : CheckedTargetPrecision T₁ T₂)
    (h₂ : CheckedTargetPrecision T₂ T₃) :
    CheckedTargetPrecision T₁ T₃ := by
  induction h₁ generalizing T₃ with
  | refl =>
      exact h₂
  | toAny =>
      cases h₂ <;> exact .toAny
  | callable hParam hReturn ihParam ihReturn =>
      cases h₂ with
      | refl =>
          exact .callable hParam hReturn
      | toAny =>
          exact .toAny
      | callable hParam' hReturn' =>
          exact .callable (ihParam hParam') (ihReturn hReturn')
  | union hLeft hRight ihLeft ihRight =>
      cases h₂ with
      | refl =>
          exact .union hLeft hRight
      | toAny =>
          exact .toAny
      | union hLeft' hRight' =>
          exact .union (ihLeft hLeft') (ihRight hRight')
  | intersection hLeft hRight ihLeft ihRight =>
      cases h₂ with
      | refl =>
          exact .intersection hLeft hRight
      | toAny =>
          exact .toAny
      | intersection hLeft' hRight' =>
          exact .intersection (ihLeft hLeft') (ihRight hRight')

/-- Structural precision on compile-generated checked targets. This extends
`CheckedTargetPrecision` with the source-side bottom escape and the two
intersection-to-branch absorption rules used by normalized call-parameter
targets. -/
inductive CompileTargetPrecision : CheckedTarget → CheckedTarget → Prop where
  | refl :
      CompileTargetPrecision T T
  | toAny :
      CompileTargetPrecision T .any
  | callable :
      CompileTargetPrecision paramTy₁ paramTy₂ →
      CompileTargetPrecision returnTy₁ returnTy₂ →
      CompileTargetPrecision
        (.callable paramTy₁ returnTy₁)
        (.callable paramTy₂ returnTy₂)
  | union :
      CompileTargetPrecision left₁ left₂ →
      CompileTargetPrecision right₁ right₂ →
      CompileTargetPrecision
        (.union left₁ right₁)
        (.union left₂ right₂)
  | intersection :
      CompileTargetPrecision left₁ left₂ →
      CompileTargetPrecision right₁ right₂ →
      CompileTargetPrecision
        (.intersection left₁ right₁)
        (.intersection left₂ right₂)
  | fromBottom :
      CompileTargetPrecision .bottom target
  | intersection_left_toAny :
      CompileTargetPrecision left .any →
      CompileTargetPrecision right target →
      CompileTargetPrecision
        (.intersection left right)
        target
  | intersection_right_toAny :
      CompileTargetPrecision left target →
      CompileTargetPrecision right .any →
      CompileTargetPrecision
        (.intersection left right)
        target
  | meet :
      CompileTargetPrecision target left →
      CompileTargetPrecision target right →
      CompileTargetPrecision
        target
        (.intersection left right)

theorem compileTargetPrecision_refl
    (T : CheckedTarget) :
    CompileTargetPrecision T T :=
  .refl

theorem compileTargetPrecision_trans
    (h₁ : CompileTargetPrecision T₁ T₂)
    (h₂ : CompileTargetPrecision T₂ T₃) :
    CompileTargetPrecision T₁ T₃ := by
  match h₂ with
  | .refl =>
      exact h₁
  | .toAny =>
      exact .toAny
  | .meet hLeft hRight =>
      exact .meet
        (compileTargetPrecision_trans h₁ hLeft)
        (compileTargetPrecision_trans h₁ hRight)
  | .callable hParam' hReturn' =>
      cases h₁ with
      | refl =>
          exact .callable hParam' hReturn'
      | callable hParam hReturn =>
          exact .callable
            (compileTargetPrecision_trans hParam hParam')
            (compileTargetPrecision_trans hReturn hReturn')
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight (.callable hParam' hReturn'))
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft (.callable hParam' hReturn'))
            hRight
  | .union hLeft' hRight' =>
      cases h₁ with
      | refl =>
          exact .union hLeft' hRight'
      | union hLeft hRight =>
          exact .union
            (compileTargetPrecision_trans hLeft hLeft')
            (compileTargetPrecision_trans hRight hRight')
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight (.union hLeft' hRight'))
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft (.union hLeft' hRight'))
            hRight
  | .intersection hLeft' hRight' =>
      cases h₁ with
      | refl =>
          exact .intersection hLeft' hRight'
      | intersection hLeft hRight =>
          exact .intersection
            (compileTargetPrecision_trans hLeft hLeft')
            (compileTargetPrecision_trans hRight hRight')
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight (.intersection hLeft' hRight'))
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft (.intersection hLeft' hRight'))
            hRight
      | meet hLeft hRight =>
          exact .meet
            (compileTargetPrecision_trans hLeft hLeft')
            (compileTargetPrecision_trans hRight hRight')
  | .fromBottom =>
      cases h₁ with
      | refl =>
          exact .fromBottom
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight .fromBottom)
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft .fromBottom)
            hRight
  | .intersection_left_toAny hLeft' hRight' =>
      cases h₁ with
      | refl =>
          exact .intersection_left_toAny hLeft' hRight'
      | intersection hLeft hRight =>
          exact .intersection_left_toAny
            (compileTargetPrecision_trans hLeft hLeft')
            (compileTargetPrecision_trans hRight hRight')
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight (.intersection_left_toAny hLeft' hRight'))
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft (.intersection_left_toAny hLeft' hRight'))
            hRight
      | meet _ hRight =>
          exact compileTargetPrecision_trans hRight hRight'
  | .intersection_right_toAny hLeft' hRight' =>
      cases h₁ with
      | refl =>
          exact .intersection_right_toAny hLeft' hRight'
      | intersection hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft hLeft')
            (compileTargetPrecision_trans hRight hRight')
      | fromBottom =>
          exact .fromBottom
      | intersection_left_toAny hLeft hRight =>
          exact .intersection_left_toAny hLeft
            (compileTargetPrecision_trans hRight (.intersection_right_toAny hLeft' hRight'))
      | intersection_right_toAny hLeft hRight =>
          exact .intersection_right_toAny
            (compileTargetPrecision_trans hLeft (.intersection_right_toAny hLeft' hRight'))
            hRight
      | meet hLeft _ =>
          exact compileTargetPrecision_trans hLeft hLeft'
termination_by sizeOf T₁ + sizeOf T₂ + sizeOf T₃
decreasing_by
  all_goals
    simp_wf
  all_goals
    try subst_vars
  all_goals
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at *
  all_goals
    try omega
    try simp_all

theorem compileTargetPrecision_of_checkedTargetPrecision
    (h : CheckedTargetPrecision T₁ T₂) :
    CompileTargetPrecision T₁ T₂ := by
  induction h with
  | refl =>
      exact .refl
  | toAny =>
      exact .toAny
  | callable _ _ ihParam ihReturn =>
      exact .callable ihParam ihReturn
  | union _ _ ihLeft ihRight =>
      exact .union ihLeft ihRight
  | intersection _ _ ihLeft ihRight =>
      exact .intersection ihLeft ihRight

/-- Structural precision on raw gradual annotations, phrased directly through
their explicit checked-target images. -/
abbrev AnnotationTargetPrecision (G₁ G₂ : GTy) : Prop :=
  CheckedTargetPrecision (checkedTargetOfGTy G₁) (checkedTargetOfGTy G₂)

theorem annotationTargetPrecision_refl
    (G : GTy) :
    AnnotationTargetPrecision G G :=
  checkedTargetPrecision_refl _

theorem annotationTargetPrecision_trans
    (h₁ : AnnotationTargetPrecision G₁ G₂)
    (h₂ : AnnotationTargetPrecision G₂ G₃) :
    AnnotationTargetPrecision G₁ G₃ :=
  checkedTargetPrecision_trans h₁ h₂

theorem checkedTargetPrecision_sound
    (h : CheckedTargetPrecision T₁ T₂) :
    MoreStatic gct (interpTarget T₁) (interpTarget T₂) := by
  induction h with
  | refl =>
      exact moreStatic_refl gct _
  | toAny =>
      exact ⟨.bottom, .objectTop⟩
  | callable _ _ ihParam ihReturn =>
      exact moreStatic_callable ihParam ihReturn
  | union _ _ ihLeft ihRight =>
      exact moreStatic_union ihLeft ihRight
  | intersection _ _ ihLeft ihRight =>
      exact moreStatic_intersection ihLeft ihRight

theorem annotationTargetPrecision_sound
    (h : AnnotationTargetPrecision G₁ G₂) :
    MoreStatic gct G₁ G₂ := by
  simpa [AnnotationTargetPrecision, checkedTargetOfGTy_interpTarget] using
    (checkedTargetPrecision_sound (gct := gct) h)

/-- Contract-level precision induced by explicit checked-target precision. -/
def CompiledBoundaryPrecision (_gct : GClassTable)
    (c₁ c₂ : BoundaryContract) : Prop :=
  CheckedTargetPrecision
    (checkedTargetOfBoundaryContract c₁)
    (checkedTargetOfBoundaryContract c₂)

theorem compiledBoundaryPrecision_of_checkedTargetPrecision
    (h : CheckedTargetPrecision T₁ T₂) :
    CompiledBoundaryPrecision gct
      (compileBoundaryTarget T₁)
      (compileBoundaryTarget T₂) := by
  simpa [CompiledBoundaryPrecision] using h

theorem compiledBoundaryPrecision_sound
    (h : CompiledBoundaryPrecision gct c₁ c₂) :
    BoundaryPrecision gct c₁ c₂ := by
  have hMore :
      MoreStatic gct
        (interpTarget (checkedTargetOfBoundaryContract c₁))
        (interpTarget (checkedTargetOfBoundaryContract c₂)) :=
    checkedTargetPrecision_sound (gct := gct) h
  simpa [BoundaryPrecision] using hMore

/-- Stable root-only structural premise for the elaboration parameter carried
by the public static/DGG interfaces. -/
abbrev ProgramRootTargetInputPrecision (G₁ G₂ : GTy) : Prop :=
  CheckedTargetPrecision
    (checkedTargetOfRuntimePublicTy G₁)
    (checkedTargetOfRuntimePublicTy G₂)

theorem programRootTargetInputPrecision_sound
    (h : ProgramRootTargetInputPrecision G₁ G₂) :
    MoreStatic gct G₁ G₂ := by
  simpa [ProgramRootTargetInputPrecision, checkedTargetOfRuntimePublicTy,
    checkedTargetOfGTy_interpTarget, runtimePublicTy_id] using
    (checkedTargetPrecision_sound (gct := gct) h)

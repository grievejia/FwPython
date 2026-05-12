import FwPython.Gradual.TypeSystem.Source.Typing
import FwPython.Gradual.TypeSystem.ClassTable.Transport
import FwPython.Gradual.TypeSystem.ProgramTargetPrecision
import FwPython.Gradual.TypeSystem.MoreStaticLemmas
import FwPython.Gradual.TypeSystem.Source.Compile.Approx
import FwPython.Static.Subtyping.Inversion

/-! # Source-environment precision for the single-type pipeline -/

structure SBindingPrecision (b₁ b₂ : SBinding) : Prop where
  name_eq : b₁.name = b₂.name
  source_prec : AnnotationTargetPrecision b₁.sourceTy b₂.sourceTy
  source_callParam_prec :
    CompileTargetPrecision
      (callParamCheckedTarget ([] : GClassTable) b₁.sourceTy)
      (callParamCheckedTarget ([] : GClassTable) b₂.sourceTy)

abbrev SBindingEnvPrecision := Forall₂ SBindingPrecision

structure SemanticSBindingPrecision (gct : GClassTable) (b₁ b₂ : SBinding) : Prop where
  name_eq : b₁.name = b₂.name
  source_moreStatic : MoreStatic gct b₁.sourceTy b₂.sourceTy

abbrev SemanticSourceEnvPrecision (gct : GClassTable) :=
  Forall₂ (SemanticSBindingPrecision gct)

structure CompileCheckEnvAlignmentPackage (gct : GClassTable)
    (Γ₁ Γ₂ : SBindingEnv) (Δ₁ Δ₂ : GTyEnv) : Prop where
  semanticEnvAlignment : SemanticSourceEnvPrecision gct Γ₁ Γ₂
  leftSourceEnvOk : SourceEnvOk gct Γ₁
  rightSourceEnvOk : SourceEnvOk gct Γ₂
  deltaAlignment : TyEnvAnnotationPrecision gct Δ₁ Δ₂
  leftElabEnvOk : ElabEnvOk gct Γ₁ Δ₁
  rightElabEnvOk : ElabEnvOk gct Γ₂ Δ₂

inductive CheckedBranchDecision where
  | refined
  | unchanged
  deriving DecidableEq, Repr

structure BranchRefineCompilePackage (gct : GClassTable) where
  leftSourceEnv : SBindingEnv
  rightSourceEnv : SBindingEnv
  leftCheckedEnv : GTyEnv
  rightCheckedEnv : GTyEnv
  leftTarget : GTy
  rightTarget : GTy
  targetPrecision : MoreStatic gct leftTarget rightTarget
  leftTargetChecked : RuntimePublicAnnotation gct leftTarget
  rightTargetChecked : RuntimePublicAnnotation gct rightTarget
  leftTargetWellFormed : WellFormedGTy gct leftTarget
  rightTargetWellFormed : WellFormedGTy gct rightTarget
  envAlignment :
    CompileCheckEnvAlignmentPackage
      gct leftSourceEnv rightSourceEnv leftCheckedEnv rightCheckedEnv

structure CheckedBranchRefineTransportPackage (gct : GClassTable) where
  thenPackage : BranchRefineCompilePackage gct
  elsePackage : BranchRefineCompilePackage gct
  leftDecision : CheckedBranchDecision
  rightDecision : CheckedBranchDecision

inductive CheckedBranchRefineTransportCases
    (gct : GClassTable) (T₁ T₂ : GTy) (C : Identifier) : Type where
  | sharedRefined
      (pack : CheckedBranchRefineTransportPackage gct)
      (leftDecision : pack.leftDecision = .refined)
      (rightDecision : pack.rightDecision = .refined)
      (leftRefined : CheckedBranchRefineOk gct T₁ C)
      (rightRefined : CheckedBranchRefineOk gct T₂ C) :
      CheckedBranchRefineTransportCases gct T₁ T₂ C
  | sharedUnchanged
      (pack : CheckedBranchRefineTransportPackage gct)
      (leftDecision : pack.leftDecision = .unchanged)
      (rightDecision : pack.rightDecision = .unchanged)
      (leftUnchanged : ¬ CheckedBranchRefineOk gct T₁ C)
      (rightUnchanged : ¬ CheckedBranchRefineOk gct T₂ C) :
      CheckedBranchRefineTransportCases gct T₁ T₂ C
  | leftOnly
      (leftRefined : CheckedBranchRefineOk gct T₁ C)
      (rightUnchanged : ¬ CheckedBranchRefineOk gct T₂ C) :
      CheckedBranchRefineTransportCases gct T₁ T₂ C
  | rightOnly
      (leftUnchanged : ¬ CheckedBranchRefineOk gct T₁ C)
      (rightRefined : CheckedBranchRefineOk gct T₂ C) :
      CheckedBranchRefineTransportCases gct T₁ T₂ C

theorem sBindingPrecision_refl (b : SBinding) :
    SBindingPrecision b b :=
  ⟨rfl, annotationTargetPrecision_refl _, compileTargetPrecision_refl _⟩

theorem sBindingEnvPrecision_refl (Γ : SBindingEnv) :
    SBindingEnvPrecision Γ Γ :=
  forall₂_refl sBindingPrecision_refl Γ

theorem semanticSBindingPrecision_refl (gct : GClassTable) (b : SBinding) :
    SemanticSBindingPrecision gct b b :=
  ⟨rfl, moreStatic_refl gct b.sourceTy⟩

theorem semanticSourceEnvPrecision_refl (gct : GClassTable) (Γ : SBindingEnv) :
    SemanticSourceEnvPrecision gct Γ Γ :=
  forall₂_refl (semanticSBindingPrecision_refl gct) Γ

theorem semanticSBindingPrecision_of_sBindingPrecision
    (gct : GClassTable)
    (h : SBindingPrecision b₁ b₂) :
    SemanticSBindingPrecision gct b₁ b₂ :=
  ⟨h.name_eq, annotationTargetPrecision_sound (gct := gct) h.source_prec⟩

theorem semanticSourceEnvPrecision_of_sBindingEnvPrecision
    (gct : GClassTable)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂) :
    SemanticSourceEnvPrecision gct Γ₁ Γ₂ :=
  forall₂_imp (fun _ _ hb => semanticSBindingPrecision_of_sBindingPrecision gct hb) hΓ

theorem compileCheckEnvAlignmentPackage_of_structural
    (gct : GClassTable)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (henv₁ : SourceEnvOk gct Γ₁)
    (henv₂ : SourceEnvOk gct Γ₂)
    (hΔ : TyEnvAnnotationPrecision gct Δ₁ Δ₂)
    (helab₁ : ElabEnvOk gct Γ₁ Δ₁)
    (helab₂ : ElabEnvOk gct Γ₂ Δ₂) :
    CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂ where
  semanticEnvAlignment := semanticSourceEnvPrecision_of_sBindingEnvPrecision gct hΓ
  leftSourceEnvOk := henv₁
  rightSourceEnvOk := henv₂
  deltaAlignment := hΔ
  leftElabEnvOk := helab₁
  rightElabEnvOk := helab₂

theorem callParamTarget_eq_any_of_compileTargetPrecision_left_any
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂))
    (hany : callParamTarget gct₁ G₁ = .any) :
    callParamTarget gct₂ G₂ = .any := by
  have hchecked₁ : callParamCheckedTarget gct₁ G₁ = .any := by
    simp [callParamCheckedTarget, hany]
  have hchecked₂ : callParamCheckedTarget gct₂ G₂ = .any := by
    exact compileTargetPrecision_any_left_inversion
      (by simpa [hchecked₁] using h)
      (callParamCheckedTarget_normalForm gct₂ G₂)
  have hInterp := congrArg interpTarget hchecked₂
  simpa [interpTarget_callParamCheckedTarget] using hInterp

private theorem compileTargetPrecision_normalizeIntersection_left_toAny
    (hLeft : CompileTargetPrecision T .any)
    (hRight : CompileTargetPrecision U V) :
    CompileTargetPrecision
      (Checked.normalizeCallParamAnnotationIntersection T U)
      V := by
  by_cases hEq : T = U
  · subst hEq
    simpa [Checked.normalizeCallParamAnnotationIntersection] using hRight
  · by_cases hOrd :
      Checked.checkedTargetCmp T U = .gt
    · unfold Checked.normalizeCallParamAnnotationIntersection
      simpa [hEq, hOrd] using
        (CompileTargetPrecision.intersection_right_toAny hRight hLeft)
    · unfold Checked.normalizeCallParamAnnotationIntersection
      simpa [hEq, hOrd] using
        (CompileTargetPrecision.intersection_left_toAny hLeft hRight)

private theorem compileTargetPrecision_normalizeIntersection_right_toAny
    (hLeft : CompileTargetPrecision T V)
    (hRight : CompileTargetPrecision U .any) :
    CompileTargetPrecision
      (Checked.normalizeCallParamAnnotationIntersection T U)
      V := by
  by_cases hEq : T = U
  · subst hEq
    simpa [Checked.normalizeCallParamAnnotationIntersection] using hLeft
  · by_cases hOrd :
      Checked.checkedTargetCmp T U = .gt
    · unfold Checked.normalizeCallParamAnnotationIntersection
      simpa [hEq, hOrd] using
        (CompileTargetPrecision.intersection_left_toAny hRight hLeft)
    · unfold Checked.normalizeCallParamAnnotationIntersection
      simpa [hEq, hOrd] using
        (CompileTargetPrecision.intersection_right_toAny hLeft hRight)

private theorem compileTargetPrecision_normalizeIntersection
    (hLeft : CompileTargetPrecision T₁ T₂)
    (hRight : CompileTargetPrecision U₁ U₂)
    (hNe : T₂ ≠ U₂) :
    CompileTargetPrecision
      (Checked.normalizeCallParamAnnotationIntersection T₁ U₁)
      (Checked.normalizeCallParamAnnotationIntersection T₂ U₂) := by
  have hLeftAny : CompileTargetPrecision T₁ .any :=
    compileTargetPrecision_trans hLeft (CompileTargetPrecision.toAny (T := T₂))
  have hRightAny : CompileTargetPrecision U₁ .any :=
    compileTargetPrecision_trans hRight (CompileTargetPrecision.toAny (T := U₂))
  have hToLeft :
      CompileTargetPrecision
        (Checked.normalizeCallParamAnnotationIntersection T₁ U₁)
        T₂ :=
    compileTargetPrecision_normalizeIntersection_right_toAny hLeft hRightAny
  have hToRight :
      CompileTargetPrecision
        (Checked.normalizeCallParamAnnotationIntersection T₁ U₁)
        U₂ :=
    compileTargetPrecision_normalizeIntersection_left_toAny hLeftAny hRight
  by_cases hOrd :
      Checked.checkedTargetCmp T₂ U₂ = .gt
  · unfold Checked.normalizeCallParamAnnotationIntersection
    simpa [hNe, hOrd] using
      (CompileTargetPrecision.meet hToRight hToLeft)
  · unfold Checked.normalizeCallParamAnnotationIntersection
    simpa [hNe, hOrd] using
      (CompileTargetPrecision.meet hToLeft hToRight)

private theorem compileTargetPrecision_class_right_inversion
    (h : CompileTargetPrecision (.class_ C) T)
    (hnf : CallParamCheckedTargetNormalForm T)
    (hnotAny : T ≠ .any) :
    T = .class_ C := by
  cases h with
  | refl =>
      rfl
  | toAny =>
      contradiction
  | meet hLeft hRight =>
      rcases hnf with ⟨hLeftNf, hRightNf, hLeftNotAny, hRightNotAny, _, _, hNe, _⟩
      have hLeftEq : _ = CheckedTarget.class_ C :=
        compileTargetPrecision_class_right_inversion hLeft hLeftNf hLeftNotAny
      have hRightEq : _ = CheckedTarget.class_ C :=
        compileTargetPrecision_class_right_inversion hRight hRightNf hRightNotAny
      subst hLeftEq
      subst hRightEq
      contradiction

private theorem compileTargetPrecision_negClass_right_inversion
    (h : CompileTargetPrecision (.negClass C) T)
    (hnf : CallParamCheckedTargetNormalForm T)
    (hnotAny : T ≠ .any) :
    T = .negClass C := by
  cases h with
  | refl => rfl
  | toAny => contradiction
  | meet hLeft hRight =>
      rcases hnf with ⟨hLeftNf, hRightNf, hLeftNotAny, hRightNotAny, _, _, hNe, _⟩
      have hLeftEq : _ = CheckedTarget.negClass C :=
        compileTargetPrecision_negClass_right_inversion hLeft hLeftNf hLeftNotAny
      have hRightEq : _ = CheckedTarget.negClass C :=
        compileTargetPrecision_negClass_right_inversion hRight hRightNf hRightNotAny
      subst hLeftEq
      subst hRightEq
      contradiction

private theorem callParamTarget_eq_class_of_compileTargetPrecision_from_class
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ (.class_ C))
        (callParamCheckedTarget gct₂ G₂))
    (hnotAny : callParamTarget gct₂ G₂ ≠ .any) :
    callParamTarget gct₂ G₂ = .class_ C := by
  have hChecked :
      CompileTargetPrecision
        (.class_ C)
        (callParamCheckedTarget gct₂ G₂) := by
    simpa [callParamCheckedTarget, callParamTarget] using h
  have hnotAnyChecked : callParamCheckedTarget gct₂ G₂ ≠ .any := by
    intro hEq
    apply hnotAny
    have hInterp := congrArg interpTarget hEq
    simpa [interpTarget_callParamCheckedTarget] using hInterp
  have hEqChecked : callParamCheckedTarget gct₂ G₂ = .class_ C := by
    exact compileTargetPrecision_class_right_inversion
      hChecked
      (callParamCheckedTarget_normalForm gct₂ G₂)
      hnotAnyChecked
  have hInterp := congrArg interpTarget hEqChecked
  simpa [interpTarget_callParamCheckedTarget] using hInterp

private theorem callParamTarget_eq_negClass_of_compileTargetPrecision_from_negClass
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ (.negClass C))
        (callParamCheckedTarget gct₂ G₂))
    (hnotAny : callParamTarget gct₂ G₂ ≠ .any) :
    callParamTarget gct₂ G₂ = .negClass C := by
  have hChecked :
      CompileTargetPrecision
        (.negClass C)
        (callParamCheckedTarget gct₂ G₂) := by
    simpa [callParamCheckedTarget, callParamTarget] using h
  have hnotAnyChecked : callParamCheckedTarget gct₂ G₂ ≠ .any := by
    intro hEq
    apply hnotAny
    have hInterp := congrArg interpTarget hEq
    simpa [interpTarget_callParamCheckedTarget] using hInterp
  have hEqChecked : callParamCheckedTarget gct₂ G₂ = .negClass C := by
    exact compileTargetPrecision_negClass_right_inversion
      hChecked
      (callParamCheckedTarget_normalForm gct₂ G₂)
      hnotAnyChecked
  have hInterp := congrArg interpTarget hEqChecked
  simpa [interpTarget_callParamCheckedTarget] using hInterp

theorem callParamCheckedTarget_intersection_class_right_congr
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂)) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ (.intersection G₁ (.class_ C)))
      (callParamCheckedTarget gct₂ (.intersection G₂ (.class_ C))) := by
  have hClass :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ (.class_ C))
        (callParamCheckedTarget gct₂ (.class_ C)) := by
    simpa [callParamCheckedTarget, callParamTarget] using
      (CompileTargetPrecision.refl
        (T := checkedTargetOfRuntimePublicTy (.class_ C : GTy)))
  by_cases hG₁Any : callParamTarget gct₁ G₁ = .any
  · have hG₂Any := callParamTarget_eq_any_of_compileTargetPrecision_left_any h hG₁Any
    rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
      (gct := gct₁) (G := G₁) (H := .class_ C) hG₁Any]
    rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
      (gct := gct₂) (G := G₂) (H := .class_ C) hG₂Any]
    exact hClass
  · by_cases hG₁Bottom : callParamTarget gct₁ G₁ = .bottom
    · have hsrc :
          callParamCheckedTarget gct₁ (.intersection G₁ (.class_ C)) = .bottom := by
        have hraw :
            callParamTarget gct₁ (.intersection G₁ (.class_ C)) = .bottom := by
          rw [show callParamTarget gct₁ (.intersection G₁ (.class_ C)) =
              callParamTarget gct₁ (.intersection .bottom (.class_ C)) by
                simp [callParamTarget, hG₁Bottom]]
          simpa using
            (callParamTarget_intersection_bottom_left
              (gct := gct₁) (G := (.class_ C)))
        simp [callParamCheckedTarget, hraw]
      rw [hsrc]
      exact .fromBottom
    · have hClassNotAny : callParamTarget gct₁ (.class_ C) ≠ .any := by
        simp [callParamTarget]
      have hClassNotBottom : callParamTarget gct₁ (.class_ C) ≠ .bottom := by
        simp [callParamTarget]
      have hClass₂NotAny : callParamTarget gct₂ (.class_ C) ≠ .any := by
        simp [callParamTarget]
      have hClass₂NotBottom : callParamTarget gct₂ (.class_ C) ≠ .bottom := by
        simp [callParamTarget]
      by_cases hG₂Any : callParamTarget gct₂ G₂ = .any
      · have hToAny :
            CompileTargetPrecision
              (callParamCheckedTarget gct₁ G₁)
              .any :=
          by simpa [callParamCheckedTarget, hG₂Any] using h
        by_cases hEq₁ : callParamTarget gct₁ G₁ = .class_ C
        · rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
            (gct := gct₁) (G := G₁) (H := .class_ C) hEq₁]
          rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
            (gct := gct₂) (G := G₂) (H := .class_ C) hG₂Any]
          simpa [callParamCheckedTarget, hEq₁] using hClass
        · rw [callParamCheckedTarget_intersection_of_uncollapsed
          (gct := gct₁) (G := G₁) (H := .class_ C)
          hG₁Any hClassNotAny hG₁Bottom hClassNotBottom hEq₁]
          rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
            (gct := gct₂) (G := G₂) (H := .class_ C) hG₂Any]
          exact compileTargetPrecision_normalizeIntersection_left_toAny hToAny hClass
      · by_cases hG₂Bottom : callParamTarget gct₂ G₂ = .bottom
        · have : callParamTarget gct₁ G₁ = .bottom :=
            callParamTarget_eq_bottom_of_compileTargetPrecision_right h hG₂Bottom
          contradiction
        · by_cases hEq₂ : callParamTarget gct₂ G₂ = .class_ C
          · have hToAny :
                CompileTargetPrecision
                  (callParamCheckedTarget gct₁ G₁)
                  .any :=
              compileTargetPrecision_trans h
                (CompileTargetPrecision.toAny
                  (T := callParamCheckedTarget gct₂ G₂))
            by_cases hEq₁ : callParamTarget gct₁ G₁ = .class_ C
            · rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₁) (G := G₁) (H := .class_ C) hEq₁]
              rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₂) (G := G₂) (H := .class_ C) hEq₂]
              simpa [callParamCheckedTarget, hEq₁, hEq₂] using hClass
            · rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₁) (G := G₁) (H := .class_ C)
              hG₁Any hClassNotAny hG₁Bottom hClassNotBottom hEq₁]
              rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₂) (G := G₂) (H := .class_ C) hEq₂]
              simpa [callParamCheckedTarget, hEq₂] using
                (compileTargetPrecision_normalizeIntersection_left_toAny hToAny hClass)
          · by_cases hEq₁ : callParamTarget gct₁ G₁ = .class_ C
            · have hClassSource :
                  callParamCheckedTarget gct₁ G₁ =
                    callParamCheckedTarget gct₁ (.class_ C) := by
                simp [callParamCheckedTarget, callParamTarget, hEq₁]
              have hClassPrec :
                  CompileTargetPrecision
                    (callParamCheckedTarget gct₁ (.class_ C))
                    (callParamCheckedTarget gct₂ G₂) := by
                simpa [callParamCheckedTarget, callParamTarget, hEq₁] using h
              have hImpossible :
                  callParamTarget gct₂ G₂ = .class_ C :=
                callParamTarget_eq_class_of_compileTargetPrecision_from_class
                  hClassPrec hG₂Any
              contradiction
            · rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₁) (G := G₁) (H := .class_ C)
              hG₁Any hClassNotAny hG₁Bottom hClassNotBottom hEq₁]
              rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₂) (G := G₂) (H := .class_ C)
              hG₂Any hClass₂NotAny hG₂Bottom hClass₂NotBottom hEq₂]
              have hNeChecked :
                  callParamCheckedTarget gct₂ G₂ ≠
                    callParamCheckedTarget gct₂ (.class_ C) := by
                intro hEq
                apply hEq₂
                have hInterp := congrArg interpTarget hEq
                simpa [interpTarget_callParamCheckedTarget] using hInterp
              exact compileTargetPrecision_normalizeIntersection h hClass hNeChecked

theorem callParamCheckedTarget_intersection_negClass_right_congr
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂)) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ (.intersection G₁ (.negClass C)))
      (callParamCheckedTarget gct₂ (.intersection G₂ (.negClass C))) := by
  have hNeg :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ (.negClass C))
        (callParamCheckedTarget gct₂ (.negClass C)) := by
    simpa [callParamCheckedTarget, callParamTarget] using
      (CompileTargetPrecision.refl
        (T := checkedTargetOfRuntimePublicTy (.negClass C : GTy)))
  by_cases hG₁Any : callParamTarget gct₁ G₁ = .any
  · have hG₂Any := callParamTarget_eq_any_of_compileTargetPrecision_left_any h hG₁Any
    rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
      (gct := gct₁) (G := G₁) (H := .negClass C) hG₁Any]
    rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
      (gct := gct₂) (G := G₂) (H := .negClass C) hG₂Any]
    exact hNeg
  · by_cases hG₁Bottom : callParamTarget gct₁ G₁ = .bottom
    · have hsrc :
          callParamCheckedTarget gct₁ (.intersection G₁ (.negClass C)) = .bottom := by
        have hraw :
            callParamTarget gct₁ (.intersection G₁ (.negClass C)) = .bottom := by
          rw [show callParamTarget gct₁ (.intersection G₁ (.negClass C)) =
              callParamTarget gct₁ (.intersection .bottom (.negClass C)) by
                simp [callParamTarget, hG₁Bottom]]
          simpa using
            (callParamTarget_intersection_bottom_left
              (gct := gct₁) (G := (.negClass C)))
        simp [callParamCheckedTarget, hraw]
      rw [hsrc]
      exact .fromBottom
    · have hNegNotAny : callParamTarget gct₁ (.negClass C) ≠ .any := by
        simp [callParamTarget]
      have hNegNotBottom : callParamTarget gct₁ (.negClass C) ≠ .bottom := by
        simp [callParamTarget]
      have hNeg₂NotAny : callParamTarget gct₂ (.negClass C) ≠ .any := by
        simp [callParamTarget]
      have hNeg₂NotBottom : callParamTarget gct₂ (.negClass C) ≠ .bottom := by
        simp [callParamTarget]
      by_cases hG₂Any : callParamTarget gct₂ G₂ = .any
      · have hToAny :
            CompileTargetPrecision
              (callParamCheckedTarget gct₁ G₁)
              .any :=
          by simpa [callParamCheckedTarget, hG₂Any] using h
        by_cases hEq₁ : callParamTarget gct₁ G₁ = .negClass C
        · rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
            (gct := gct₁) (G := G₁) (H := .negClass C) hEq₁]
          rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
            (gct := gct₂) (G := G₂) (H := .negClass C) hG₂Any]
          simpa [callParamCheckedTarget, hEq₁] using hNeg
        · rw [callParamCheckedTarget_intersection_of_uncollapsed
          (gct := gct₁) (G := G₁) (H := .negClass C)
          hG₁Any hNegNotAny hG₁Bottom hNegNotBottom hEq₁]
          rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
            (gct := gct₂) (G := G₂) (H := .negClass C) hG₂Any]
          exact compileTargetPrecision_normalizeIntersection_left_toAny hToAny hNeg
      · by_cases hG₂Bottom : callParamTarget gct₂ G₂ = .bottom
        · have : callParamTarget gct₁ G₁ = .bottom :=
            callParamTarget_eq_bottom_of_compileTargetPrecision_right h hG₂Bottom
          contradiction
        · by_cases hEq₂ : callParamTarget gct₂ G₂ = .negClass C
          · have hToAny :
                CompileTargetPrecision
                  (callParamCheckedTarget gct₁ G₁)
                  .any :=
              compileTargetPrecision_trans h
                (CompileTargetPrecision.toAny
                  (T := callParamCheckedTarget gct₂ G₂))
            by_cases hEq₁ : callParamTarget gct₁ G₁ = .negClass C
            · rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₁) (G := G₁) (H := .negClass C) hEq₁]
              rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₂) (G := G₂) (H := .negClass C) hEq₂]
              simpa [callParamCheckedTarget, hEq₁, hEq₂] using hNeg
            · rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₁) (G := G₁) (H := .negClass C)
              hG₁Any hNegNotAny hG₁Bottom hNegNotBottom hEq₁]
              rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                (gct := gct₂) (G := G₂) (H := .negClass C) hEq₂]
              simpa [callParamCheckedTarget, hEq₂] using
                (compileTargetPrecision_normalizeIntersection_left_toAny hToAny hNeg)
          · by_cases hEq₁ : callParamTarget gct₁ G₁ = .negClass C
            · have hNegSource :
                  callParamCheckedTarget gct₁ G₁ =
                    callParamCheckedTarget gct₁ (.negClass C) := by
                simp [callParamCheckedTarget, callParamTarget, hEq₁]
              have hNegPrec :
                  CompileTargetPrecision
                    (callParamCheckedTarget gct₁ (.negClass C))
                    (callParamCheckedTarget gct₂ G₂) := by
                simpa [callParamCheckedTarget, callParamTarget, hEq₁] using h
              have hImpossible :
                  callParamTarget gct₂ G₂ = .negClass C :=
                callParamTarget_eq_negClass_of_compileTargetPrecision_from_negClass
                  hNegPrec hG₂Any
              contradiction
            · rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₁) (G := G₁) (H := .negClass C)
              hG₁Any hNegNotAny hG₁Bottom hNegNotBottom hEq₁]
              rw [callParamCheckedTarget_intersection_of_uncollapsed
              (gct := gct₂) (G := G₂) (H := .negClass C)
              hG₂Any hNeg₂NotAny hG₂Bottom hNeg₂NotBottom hEq₂]
              have hNeChecked :
                  callParamCheckedTarget gct₂ G₂ ≠
                    callParamCheckedTarget gct₂ (.negClass C) := by
                intro hEq
                apply hEq₂
                have hInterp := congrArg interpTarget hEq
                simpa [interpTarget_callParamCheckedTarget] using hInterp
              exact compileTargetPrecision_normalizeIntersection h hNeg hNeChecked

theorem sBindingEnvPrecision_lookup
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (hlook : SBindingEnv.lookupBinding Γ₁ x = some b₁) :
    ∃ b₂, SBindingEnv.lookupBinding Γ₂ x = some b₂ ∧ SBindingPrecision b₁ b₂ := by
  induction hΓ generalizing x b₁ with
  | nil => simp [SBindingEnv.lookupBinding] at hlook
  | @cons b₁' b₂' Γ₁ Γ₂ hb _ ih =>
      by_cases hname : b₁'.name = x
      · simp [SBindingEnv.lookupBinding, hname] at hlook
        cases hlook
        have hname₂ : b₂'.name = x := hb.name_eq.symm.trans hname
        exact ⟨b₂', by simp [SBindingEnv.lookupBinding, hname₂], hb⟩
      · simp [SBindingEnv.lookupBinding, hname] at hlook
        obtain ⟨b₂, hlook₂, hb₂⟩ := ih hlook
        have hname₂ : b₂'.name ≠ x := fun hEq => hname (hb.name_eq.trans hEq)
        exact ⟨b₂, by simp [SBindingEnv.lookupBinding, hname₂, hlook₂], hb₂⟩

theorem semanticSourceEnvPrecision_lookup
    (hΓ : SemanticSourceEnvPrecision gct Γ₁ Γ₂)
    (hlook : SBindingEnv.lookupBinding Γ₁ x = some b₁) :
    ∃ b₂,
      SBindingEnv.lookupBinding Γ₂ x = some b₂ ∧
      SemanticSBindingPrecision gct b₁ b₂ := by
  induction hΓ generalizing x b₁ with
  | nil =>
      simp [SBindingEnv.lookupBinding] at hlook
  | @cons b₁' b₂' Γ₁ Γ₂ hb _ ih =>
      by_cases hname : b₁'.name = x
      · simp [SBindingEnv.lookupBinding, hname] at hlook
        cases hlook
        have hname₂ : b₂'.name = x := hb.name_eq.symm.trans hname
        exact ⟨b₂', by simp [SBindingEnv.lookupBinding, hname₂], hb⟩
      · simp [SBindingEnv.lookupBinding, hname] at hlook
        obtain ⟨b₂, hlook₂, hb₂⟩ := ih hlook
        have hname₂ : b₂'.name ≠ x := fun hEq => hname (hb.name_eq.trans hEq)
        exact ⟨b₂, by simp [SBindingEnv.lookupBinding, hname₂, hlook₂], hb₂⟩

theorem sBindingEnvPrecision_updateSource
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (hprec : AnnotationTargetPrecision S₁ S₂)
    (hcallPrec :
      CompileTargetPrecision
        (callParamCheckedTarget ([] : GClassTable) S₁)
        (callParamCheckedTarget ([] : GClassTable) S₂)) :
    SBindingEnvPrecision
      (SBindingEnv.updateSource Γ₁ x S₁)
      (SBindingEnv.updateSource Γ₂ x S₂) := by
  induction hΓ generalizing x S₁ S₂ with
  | nil => exact .nil
  | @cons b₁ b₂ _ _ hb hΓ ih =>
      by_cases hname : b₁.name = x
      · have hname₂ : b₂.name = x := hb.name_eq.symm.trans hname
        simp [SBindingEnv.updateSource, hname, hname₂]
        exact .cons ⟨by simp, hprec, hcallPrec⟩ hΓ
      · have hname₂ : b₂.name ≠ x := fun hEq => hname (hb.name_eq.trans hEq)
        simp [SBindingEnv.updateSource, hname, hname₂]
        exact .cons hb (ih hprec hcallPrec)

theorem semanticSourceEnvPrecision_updateSource
    (hΓ : SemanticSourceEnvPrecision gct Γ₁ Γ₂)
    (hmore : MoreStatic gct S₁ S₂) :
    SemanticSourceEnvPrecision gct
      (SBindingEnv.updateSource Γ₁ x S₁)
      (SBindingEnv.updateSource Γ₂ x S₂) := by
  induction hΓ generalizing x S₁ S₂ with
  | nil =>
      exact .nil
  | @cons b₁ b₂ _ _ hb hΓ ih =>
      by_cases hname : b₁.name = x
      · have hname₂ : b₂.name = x := hb.name_eq.symm.trans hname
        simp [SBindingEnv.updateSource, hname, hname₂]
        exact .cons ⟨by simp, hmore⟩ hΓ
      · have hname₂ : b₂.name ≠ x := fun hEq => hname (hb.name_eq.trans hEq)
        simp [SBindingEnv.updateSource, hname, hname₂]
        exact .cons hb (ih hmore)

theorem compileCheckEnvAlignmentPackage_updateSource
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hsrcPrec : MoreStatic gct newSrc₁ newSrc₂)
    (hsrc₁ : SourceCallableTy gct newSrc₁)
    (hwf₁ : WellFormedGTy gct newSrc₁)
    (hsrc₂ : SourceCallableTy gct newSrc₂)
    (hwf₂ : WellFormedGTy gct newSrc₂)
    (hsub₁ : GradualSubtype gct newSrc₁ T₁)
    (hsub₂ : GradualSubtype gct newSrc₂ T₂) :
    CompileCheckEnvAlignmentPackage gct
      (Γ₁.updateSource x newSrc₁)
      (Γ₂.updateSource x newSrc₂)
      Δ₁
      Δ₂ where
  semanticEnvAlignment :=
    semanticSourceEnvPrecision_updateSource hpack.semanticEnvAlignment hsrcPrec
  leftSourceEnvOk :=
    sourceEnvOk_updateSource hpack.leftSourceEnvOk hlookΓ₁ hsrc₁ hwf₁
  rightSourceEnvOk :=
    sourceEnvOk_updateSource hpack.rightSourceEnvOk hlookΓ₂ hsrc₂ hwf₂
  deltaAlignment := hpack.deltaAlignment
  leftElabEnvOk :=
    elabEnvOk_updateSource hpack.leftElabEnvOk hlookΓ₁ hlookΔ₁ hsub₁
  rightElabEnvOk :=
    elabEnvOk_updateSource hpack.rightElabEnvOk hlookΓ₂ hlookΔ₂ hsub₂

theorem compileCheckEnvAlignmentPackage_updateBoth
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hsrcPrec : MoreStatic gct newSrc₁ newSrc₂)
    (hsrc₁ : SourceCallableTy gct newSrc₁)
    (hwfSrc₁ : WellFormedGTy gct newSrc₁)
    (hsrc₂ : SourceCallableTy gct newSrc₂)
    (hwfSrc₂ : WellFormedGTy gct newSrc₂)
    (hcheckedPrec : MoreStatic gct newChecked₁ newChecked₂)
    (hchecked₁ : RuntimePublicAnnotation gct newChecked₁)
    (hwfChecked₁ : WellFormedGTy gct newChecked₁)
    (hchecked₂ : RuntimePublicAnnotation gct newChecked₂)
    (hwfChecked₂ : WellFormedGTy gct newChecked₂)
    (hsub₁ : GradualSubtype gct newSrc₁ newChecked₁)
    (hsub₂ : GradualSubtype gct newSrc₂ newChecked₂) :
    CompileCheckEnvAlignmentPackage gct
      (Γ₁.updateSource x newSrc₁)
      (Γ₂.updateSource x newSrc₂)
      (Δ₁.update x newChecked₁)
      (Δ₂.update x newChecked₂) where
  semanticEnvAlignment :=
    semanticSourceEnvPrecision_updateSource hpack.semanticEnvAlignment hsrcPrec
  leftSourceEnvOk :=
    sourceEnvOk_updateSource hpack.leftSourceEnvOk hlookΓ₁ hsrc₁ hwfSrc₁
  rightSourceEnvOk :=
    sourceEnvOk_updateSource hpack.rightSourceEnvOk hlookΓ₂ hsrc₂ hwfSrc₂
  deltaAlignment :=
    tyEnvAnnotationPrecision_update hpack.deltaAlignment hcheckedPrec
  leftElabEnvOk :=
    elabEnvOk_updateBoth
      hpack.leftElabEnvOk hlookΓ₁ hlookΔ₁ hchecked₁ hwfChecked₁ hsub₁
  rightElabEnvOk :=
    elabEnvOk_updateBoth
      hpack.rightElabEnvOk hlookΓ₂ hlookΔ₂ hchecked₂ hwfChecked₂ hsub₂

theorem compileCheckEnvAlignmentPackage_intersection_sourceOnly
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hRsrc : SourceCallableTy gct R)
    (hRwf : WellFormedGTy gct R) :
    CompileCheckEnvAlignmentPackage gct
      (Γ₁.updateSource x (.intersection b₁.sourceTy R))
      (Γ₂.updateSource x (.intersection b₂.sourceTy R))
      Δ₁
      Δ₂ := by
  obtain ⟨b₂', hlookΓ₂', hbPrec⟩ :=
    semanticSourceEnvPrecision_lookup hpack.semanticEnvAlignment hlookΓ₁
  rw [hlookΓ₂] at hlookΓ₂'
  cases hlookΓ₂'
  have hb₁ := sourceEnvOk_lookup hpack.leftSourceEnvOk hlookΓ₁
  have hb₂ := sourceEnvOk_lookup hpack.rightSourceEnvOk hlookΓ₂
  obtain ⟨T₁', hlookΔ₁', _, _, hsub₁_orig⟩ :=
    elabEnvOk_lookup hpack.leftElabEnvOk hlookΓ₁
  rw [hlookΔ₁] at hlookΔ₁'
  cases hlookΔ₁'
  obtain ⟨T₂', hlookΔ₂', _, _, hsub₂_orig⟩ :=
    elabEnvOk_lookup hpack.rightElabEnvOk hlookΓ₂
  rw [hlookΔ₂] at hlookΔ₂'
  cases hlookΔ₂'
  refine compileCheckEnvAlignmentPackage_updateSource
      hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂
      (moreStatic_intersection hbPrec.source_moreStatic (moreStatic_refl gct R))
      (.intersection hb₁.1 hRsrc)
      (.intersection hb₁.2 hRwf)
      (.intersection hb₂.1 hRsrc)
      (.intersection hb₂.2 hRwf)
      ?_ ?_
  · exact gradualSubtype_trans
      (gradualSubtype_intersection_left gct b₁.sourceTy R)
      hsub₁_orig
  · exact gradualSubtype_trans
      (gradualSubtype_intersection_left gct b₂.sourceTy R)
      hsub₂_orig

theorem compileCheckEnvAlignmentPackage_intersection_updateBoth
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hRsrc : SourceCallableTy gct R)
    (hRwf : WellFormedGTy gct R)
    (hchecked₁ : RuntimePublicAnnotation gct (.intersection T₁ R))
    (hwfChecked₁ : WellFormedGTy gct (.intersection T₁ R))
    (hchecked₂ : RuntimePublicAnnotation gct (.intersection T₂ R))
    (hwfChecked₂ : WellFormedGTy gct (.intersection T₂ R)) :
    CompileCheckEnvAlignmentPackage gct
      (Γ₁.updateSource x (.intersection b₁.sourceTy R))
      (Γ₂.updateSource x (.intersection b₂.sourceTy R))
      (Δ₁.update x (.intersection T₁ R))
      (Δ₂.update x (.intersection T₂ R)) := by
  obtain ⟨b₂', hlookΓ₂', hbPrec⟩ :=
    semanticSourceEnvPrecision_lookup hpack.semanticEnvAlignment hlookΓ₁
  rw [hlookΓ₂] at hlookΓ₂'
  cases hlookΓ₂'
  obtain ⟨T₂', hlookΔ₂', hTPrec⟩ :=
    tyEnvAnnotationPrecision_lookup hpack.deltaAlignment hlookΔ₁
  rw [hlookΔ₂] at hlookΔ₂'
  cases hlookΔ₂'
  have hb₁ := sourceEnvOk_lookup hpack.leftSourceEnvOk hlookΓ₁
  have hb₂ := sourceEnvOk_lookup hpack.rightSourceEnvOk hlookΓ₂
  obtain ⟨T₁', hlookΔ₁', _, _, hsub₁_orig⟩ :=
    elabEnvOk_lookup hpack.leftElabEnvOk hlookΓ₁
  rw [hlookΔ₁] at hlookΔ₁'
  cases hlookΔ₁'
  obtain ⟨T₂'', hlookΔ₂'', _, _, hsub₂_orig⟩ :=
    elabEnvOk_lookup hpack.rightElabEnvOk hlookΓ₂
  rw [hlookΔ₂] at hlookΔ₂''
  cases hlookΔ₂''
  refine compileCheckEnvAlignmentPackage_updateBoth
      hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂
      (moreStatic_intersection hbPrec.source_moreStatic (moreStatic_refl gct R))
      (.intersection hb₁.1 hRsrc)
      (.intersection hb₁.2 hRwf)
      (.intersection hb₂.1 hRsrc)
      (.intersection hb₂.2 hRwf)
      (moreStatic_intersection hTPrec (moreStatic_refl gct R))
      hchecked₁ hwfChecked₁ hchecked₂ hwfChecked₂
      ?_ ?_
  · exact gradualSubtype_intersection_mono hsub₁_orig (gradualSubtype_refl gct R)
  · exact gradualSubtype_intersection_mono hsub₂_orig (gradualSubtype_refl gct R)

def branchRefineCompilePackage_intersection_sourceOnly
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hRsrc : SourceCallableTy gct R)
    (hRwf : WellFormedGTy gct R) :
    BranchRefineCompilePackage gct where
  leftSourceEnv := Γ₁.updateSource x (.intersection b₁.sourceTy R)
  rightSourceEnv := Γ₂.updateSource x (.intersection b₂.sourceTy R)
  leftCheckedEnv := Δ₁
  rightCheckedEnv := Δ₂
  leftTarget := T₁
  rightTarget := T₂
  targetPrecision := by
    obtain ⟨T₂', hlookΔ₂', hTPrec⟩ :=
      tyEnvAnnotationPrecision_lookup hpack.deltaAlignment hlookΔ₁
    rw [hlookΔ₂] at hlookΔ₂'
    cases hlookΔ₂'
    exact hTPrec
  leftTargetChecked := by
    obtain ⟨T₁', hlookΔ₁', hchecked, _, _⟩ :=
      elabEnvOk_lookup hpack.leftElabEnvOk hlookΓ₁
    rw [hlookΔ₁] at hlookΔ₁'
    cases hlookΔ₁'
    simpa using hchecked
  rightTargetChecked := by
    obtain ⟨T₂', hlookΔ₂', hchecked, _, _⟩ :=
      elabEnvOk_lookup hpack.rightElabEnvOk hlookΓ₂
    rw [hlookΔ₂] at hlookΔ₂'
    cases hlookΔ₂'
    simpa using hchecked
  leftTargetWellFormed := by
    obtain ⟨T₁', hlookΔ₁', _, hwf, _⟩ :=
      elabEnvOk_lookup hpack.leftElabEnvOk hlookΓ₁
    rw [hlookΔ₁] at hlookΔ₁'
    cases hlookΔ₁'
    simpa using hwf
  rightTargetWellFormed := by
    obtain ⟨T₂', hlookΔ₂', _, hwf, _⟩ :=
      elabEnvOk_lookup hpack.rightElabEnvOk hlookΓ₂
    rw [hlookΔ₂] at hlookΔ₂'
    cases hlookΔ₂'
    simpa using hwf
  envAlignment :=
    compileCheckEnvAlignmentPackage_intersection_sourceOnly
      hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ hRsrc hRwf

def branchRefineCompilePackage_intersection_updateBoth
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hRsrc : SourceCallableTy gct R)
    (hRwf : WellFormedGTy gct R)
    (hchecked₁ : RuntimePublicAnnotation gct (.intersection T₁ R))
    (hwfChecked₁ : WellFormedGTy gct (.intersection T₁ R))
    (hchecked₂ : RuntimePublicAnnotation gct (.intersection T₂ R))
    (hwfChecked₂ : WellFormedGTy gct (.intersection T₂ R)) :
    BranchRefineCompilePackage gct where
  leftSourceEnv := Γ₁.updateSource x (.intersection b₁.sourceTy R)
  rightSourceEnv := Γ₂.updateSource x (.intersection b₂.sourceTy R)
  leftCheckedEnv := Δ₁.update x (.intersection T₁ R)
  rightCheckedEnv := Δ₂.update x (.intersection T₂ R)
  leftTarget := .intersection T₁ R
  rightTarget := .intersection T₂ R
  targetPrecision := by
    obtain ⟨T₂', hlookΔ₂', hTPrec⟩ :=
      tyEnvAnnotationPrecision_lookup hpack.deltaAlignment hlookΔ₁
    rw [hlookΔ₂] at hlookΔ₂'
    cases hlookΔ₂'
    exact moreStatic_intersection hTPrec (moreStatic_refl gct R)
  leftTargetChecked := hchecked₁
  rightTargetChecked := hchecked₂
  leftTargetWellFormed := hwfChecked₁
  rightTargetWellFormed := hwfChecked₂
  envAlignment :=
    compileCheckEnvAlignmentPackage_intersection_updateBoth
      hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂
      hRsrc hRwf hchecked₁ hwfChecked₁ hchecked₂ hwfChecked₂

def checkedBranchRefineTransportPackage_sharedUnchanged
    (hwfct : WellFormedGClassTableCore gct)
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hfind : findGClass gct C = some cls) :
    CheckedBranchRefineTransportPackage gct := by
  have hclassWf : WellFormedGTy gct (.class_ C) :=
    classTy_wellFormed_of_findGClass hwfct hfind
  have hnegWf : WellFormedGTy gct (.negClass C) :=
    negClassTy_wellFormed_of_findGClass hwfct hfind
  exact
    { thenPackage :=
        branchRefineCompilePackage_intersection_sourceOnly
          hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ .class_ hclassWf
      elsePackage :=
        branchRefineCompilePackage_intersection_sourceOnly
          hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ .negClass hnegWf
      leftDecision := .unchanged
      rightDecision := .unchanged }

def checkedBranchRefineTransportPackage_sharedRefined
    (hwfct : WellFormedGClassTableCore gct)
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hfind : findGClass gct C = some cls)
    (href₁ : CheckedBranchRefineOk gct T₁ C)
    (href₂ : CheckedBranchRefineOk gct T₂ C) :
    CheckedBranchRefineTransportPackage gct := by
  have hclassWf : WellFormedGTy gct (.class_ C) :=
    classTy_wellFormed_of_findGClass hwfct hfind
  have hnegWf : WellFormedGTy gct (.negClass C) :=
    negClassTy_wellFormed_of_findGClass hwfct hfind
  have hT₁wf : WellFormedGTy gct T₁ :=
    elabEnvOk_lookup_wellFormed hpack.leftElabEnvOk hlookΓ₁ hlookΔ₁
  have hT₂wf : WellFormedGTy gct T₂ :=
    elabEnvOk_lookup_wellFormed hpack.rightElabEnvOk hlookΓ₂ hlookΔ₂
  exact
    { thenPackage :=
        branchRefineCompilePackage_intersection_updateBoth
          hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂
          .class_ hclassWf
          href₁.1 (.intersection hT₁wf hclassWf)
          href₂.1 (.intersection hT₂wf hclassWf)
      elsePackage :=
        branchRefineCompilePackage_intersection_updateBoth
          hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂
          .negClass hnegWf
          href₁.2 (.intersection hT₁wf hnegWf)
          href₂.2 (.intersection hT₂wf hnegWf)
      leftDecision := .refined
      rightDecision := .refined }

def checkedBranchRefine_transport_cases
    (hwfct : WellFormedGClassTableCore gct)
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hfind : findGClass gct C = some cls) :
    CheckedBranchRefineTransportCases gct T₁ T₂ C := by
  by_cases href₁ : CheckedBranchRefineOk gct T₁ C
  · by_cases href₂ : CheckedBranchRefineOk gct T₂ C
    · refine .sharedRefined
        (checkedBranchRefineTransportPackage_sharedRefined
          hwfct hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ hfind href₁ href₂)
        rfl rfl href₁ href₂
    · exact .leftOnly href₁ href₂
  · by_cases href₂ : CheckedBranchRefineOk gct T₂ C
    · exact .rightOnly href₁ href₂
    · refine .sharedUnchanged
        (checkedBranchRefineTransportPackage_sharedUnchanged
          hwfct hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ hfind)
        rfl rfl href₁ href₂

private theorem checkedBranchRefine_left_only_impossible_of_annotationTargetPrecision
    (hprec : AnnotationTargetPrecision T₁ T₂)
    (href₁ : CheckedBranchRefineOk gct T₁ C)
    (href₂ : ¬ CheckedBranchRefineOk gct T₂ C) :
    False :=
  href₂ (checkedBranchRefineOk_gPrecision hprec href₁)

private def checkedBranchRefine_transport_cases_of_annotationTargetPrecision
    (hwfct : WellFormedGClassTableCore gct)
    (hpack : CompileCheckEnvAlignmentPackage gct Γ₁ Γ₂ Δ₁ Δ₂)
    (hlookΓ₁ : Γ₁.lookupBinding x = some b₁)
    (hlookΓ₂ : Γ₂.lookupBinding x = some b₂)
    (hlookΔ₁ : Δ₁.lookup x = some T₁)
    (hlookΔ₂ : Δ₂.lookup x = some T₂)
    (hfind : findGClass gct C = some cls)
    (hprec : AnnotationTargetPrecision T₁ T₂) :
    CheckedBranchRefineTransportCases gct T₁ T₂ C := by
  match checkedBranchRefine_transport_cases
      hwfct hpack hlookΓ₁ hlookΓ₂ hlookΔ₁ hlookΔ₂ hfind with
  | .sharedRefined pack hleft hright href₁ href₂ =>
      exact .sharedRefined pack hleft hright href₁ href₂
  | .sharedUnchanged pack hleft hright href₁ href₂ =>
      exact .sharedUnchanged pack hleft hright href₁ href₂
  | .leftOnly href₁ href₂ =>
      exact False.elim
        (checkedBranchRefine_left_only_impossible_of_annotationTargetPrecision
          hprec href₁ href₂)
  | .rightOnly href₁ href₂ =>
      exact .rightOnly href₁ href₂

private theorem checkedBranchRefineOk_any_boolClass
    (gct : GClassTable) :
    CheckedBranchRefineOk gct .any boolClass := by
  constructor
  · exact runtimePublicAnnotation_mk (.classFormula (.intersection .any .class_))
  · exact runtimePublicAnnotation_mk (.classFormula (.intersection .any .negClass))

private theorem not_bmCompatibleFormula_boolClass
    (hwfct : WellFormedGClassTableCore gct) :
    ¬ BMCompatibleFormula gct (.class_ boolClass) := by
  intro hcompat
  have hmem : boolClass ∈ hwfct.raw.boundMethodExists.mro := by
    simpa [FormulaHoldsForMro] using
      hcompat.2 hwfct.raw.boundMethodExists.cls hwfct.raw.boundMethodExists.mro
        hwfct.raw.boundMethodExists.hfind hwfct.raw.boundMethodExists.hmro
  have hEq : boundMethodClass = boolClass :=
    hwfct.raw.boolLeaf boundMethodClass hwfct.raw.boundMethodExists.cls
      hwfct.raw.boundMethodExists.mro hwfct.raw.boundMethodExists.hfind
      hwfct.raw.boundMethodExists.hmro hmem
  have hneq : boundMethodClass ≠ boolClass := by
    decide
  exact hneq hEq

private theorem not_checkedBranchRefineOk_callable_any_boolClass
    (hwfct : WellFormedGClassTableCore gct) :
    ¬ CheckedBranchRefineOk gct (.callable .any .any) boolClass := by
  intro href
  have hclass :
      CheckedTargetTy gct (.intersection (.callable .any .any) (.class_ boolClass)) :=
    runtimePublicAnnotation_checked href.1
  cases hclass with
  | classFormula hformula =>
      cases hformula with
      | intersection hleft hright =>
          cases hleft
  | interCallableLeft hP hR hbm =>
      exact not_bmCompatibleFormula_boolClass hwfct hbm

theorem checkedBranchRefine_right_refined_counterexample
    (hwfct : WellFormedGClassTableCore gct) :
    ∃ T₁ T₂ C,
      MoreStatic gct T₁ T₂ ∧
      CheckedBranchRefineOk gct T₂ C ∧
      ¬ CheckedBranchRefineOk gct T₁ C := by
  refine ⟨.callable .any .any, .any, boolClass, ?_, ?_, ?_⟩
  · exact annotationTargetPrecision_sound (gct := gct) <| by
      simpa [AnnotationTargetPrecision, checkedTargetOfGTy] using
        (CheckedTargetPrecision.toAny
          (T := CheckedTarget.callable .any .any))
  · exact checkedBranchRefineOk_any_boolClass gct
  · exact not_checkedBranchRefineOk_callable_any_boolClass hwfct

private theorem not_moreStatic_callable_any_then_refined_bool
    (hwfct : WellFormedGClassTableCore gct) :
    ¬ MoreStatic gct (.callable .any .any) (.intersection .any (.class_ boolClass)) := by
  intro hmore
  let hwfErase : WellFormedClassTable (eraseClassTable gct) :=
    eraseClassTable_wellFormed hwfct.raw hwfct.allMethodNamesDistinct
  have hsubClass :
      IsSubtype (eraseClassTable gct)
        (upperBound (.callable .any .any))
        (.class_ boolClass) := by
    have hsubInter :
        IsSubtype (eraseClassTable gct)
          (upperBound (.callable .any .any))
          (upperBound (.intersection .any (.class_ boolClass))) :=
      hmore.2
    simpa [upperBound] using
      IsSubtype.trans hsubInter
        (IsSubtype.interRight
          (T := staticTop)
          (U := (.class_ boolClass))
          (V := (.class_ boolClass))
          IsSubtype.refl)
  have hboolNotInBM : boolClass ∉ hwfErase.boundMethodExists.mro := by
    intro hmem
    have hEq : boundMethodClass = boolClass :=
      hwfErase.builtinsLeaf
        boundMethodClass
        hwfErase.boundMethodExists.cls
        hwfErase.boundMethodExists.mro
        hwfErase.boundMethodExists.hfind
        hwfErase.boundMethodExists.hmro
        hmem
    exact (by decide : boundMethodClass ≠ boolClass) hEq
  let bm : BoundMethodOrd (eraseClassTable gct) :=
    { actualParam := lowerBound (.any)
      actualReturn := upperBound (.any)
      cls := hwfErase.boundMethodExists.cls
      mro := hwfErase.boundMethodExists.mro
      hfind := hwfErase.boundMethodExists.hfind
      hmro := hwfErase.boundMethodExists.hmro }
  have hcall :
      Ty.semDenotes (eraseClassTable gct)
        (upperBound (.callable .any .any))
        (.boundMethod bm) := by
    simpa [upperBound] using boundMethod_denotes_callable_self bm
  have hclass :
      Ty.semDenotes (eraseClassTable gct)
        (.class_ boolClass)
        (.boundMethod bm) :=
    semDenotes_at_obj_sound (obj := .boundMethod bm) hsubClass hcall
  exact
    (callable_obj_not_denotes_class_of_not_mem
      (ct := eraseClassTable gct)
      (P := lowerBound (.any))
      (R := upperBound (.any))
      (D := boolClass)
      hwfErase hboolNotInBM hcall)
      hclass

private theorem not_tyEnvAnnotationPrecision_singleton_of_not_moreStatic
    (x : Identifier)
    (hnot : ¬ MoreStatic gct T₁ T₂) :
    ¬ TyEnvAnnotationPrecision gct [(x, T₁)] [(x, T₂)] := by
  intro hprec
  cases hprec with
  | cons hmore htail =>
      cases htail
      exact hnot hmore

private inductive OperatorExtraEnvelope : GTy → Prop where
  | any :
      OperatorExtraEnvelope .any
  | union_left :
      OperatorExtraEnvelope E →
      OperatorExtraEnvelope (.union E X)
  | union_right :
      OperatorExtraEnvelope E →
      OperatorExtraEnvelope (.union X E)
  | intersection :
      OperatorExtraEnvelope E →
      OperatorExtraEnvelope F →
      OperatorExtraEnvelope (.intersection E F)

private theorem operatorExtraEnvelope_staticTop_subtype_upper
    (hE : OperatorExtraEnvelope E) :
    IsSubtype (eraseClassTable gct) staticTop (upperBound E) := by
  induction hE with
  | any =>
      simpa [upperBound] using (IsSubtype.refl (ct := eraseClassTable gct) (T := staticTop))
  | @union_left E X _ ihE =>
      simpa [upperBound] using
        (IsSubtype.unionLeft
          (T := staticTop)
          (U := upperBound E)
          (V := upperBound X)
          ihE)
  | @union_right X E _ ihE =>
      simpa [upperBound] using
        (IsSubtype.unionRight
          (T := staticTop)
          (U := upperBound E)
          (V := upperBound X)
          ihE)
  | intersection _ _ ihE ihF =>
      simpa [upperBound] using IsSubtype.interIntro ihE ihF

private theorem operatorExtraEnvelope_callParamTarget_any
    (hE : OperatorExtraEnvelope E) :
    callParamTarget gct E = .any := by
  induction hE with
  | any =>
      rfl
  | @union_left E X _ ihE =>
      simpa [callParamTarget, ihE] using
        (callParamTarget_union_any_left (gct := gct) (G := X))
  | @union_right X E _ ihE =>
      simpa [callParamTarget, ihE] using
        (callParamTarget_union_any_right (gct := gct) (G := E))
  | intersection _ _ ihE ihF =>
      simp [callParamTarget, ihE, ihF]
      rfl

private inductive OperatorCompareInput : GTy → GTy → Prop where
  | any :
      OperatorCompareInput .any .any
  | toAny :
      OperatorCompareInput G .any
  | class_ :
      OperatorCompareInput (.class_ C) (.class_ C)
  | callable :
      OperatorCompareInput P₁ P₂ →
      OperatorCompareInput R₁ R₂ →
      OperatorCompareInput (.callable P₁ R₁) (.callable P₂ R₂)
  | union :
      OperatorCompareInput G₁ G₂ →
      OperatorCompareInput H₁ H₂ →
      OperatorCompareInput (.union G₁ H₁) (.union G₂ H₂)
  | intersection :
      OperatorCompareInput G₁ G₂ →
      OperatorCompareInput H₁ H₂ →
      OperatorCompareInput (.intersection G₁ H₁) (.intersection G₂ H₂)
  | bottom :
      OperatorCompareInput .bottom .bottom
  | negClass :
      OperatorCompareInput (.negClass C) (.negClass C)
  | intersection_extra_left :
      OperatorCompareInput X X' →
      OperatorExtraEnvelope E →
      OperatorCompareInput X (.intersection X' E)
  | intersection_extra_right :
      OperatorCompareInput X X' →
      OperatorExtraEnvelope E →
      OperatorCompareInput X (.intersection E X')
  | intersection_duplicate :
      OperatorCompareInput X X' →
      OperatorCompareInput X (.intersection X' X')

private theorem operatorCompareInput_of_skeleton
    (h : SourceOperatorInputAlignment G₁ G₂) :
    OperatorCompareInput G₁ G₂ := by
  induction h with
  | any =>
      exact .any
  | toAny =>
      exact .toAny
  | class_ =>
      exact .class_
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass

private theorem operatorCompareInput_refl
    (G : GTy) :
    OperatorCompareInput G G := by
  induction G with
  | any =>
      exact .any
  | class_ =>
      exact .class_
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass

private theorem operatorCompareInput_of_annotationTargetPrecision
    (h : AnnotationTargetPrecision G₁ G₂) :
    OperatorCompareInput G₁ G₂ :=
  operatorCompareInput_of_skeleton
    (sourceOperatorInputAlignment_of_annotationTargetPrecision h)

private theorem operatorCompareInput_moreStatic
    (hoci : OperatorCompareInput G₁ G₂) :
    MoreStatic gct G₁ G₂ := by
  induction hoci with
  | any =>
      exact moreStatic_refl gct .any
  | toAny =>
      rename_i G
      exact moreStatic_toAny gct G
  | class_ =>
      rename_i C
      exact moreStatic_refl gct (.class_ C)
  | callable hP hR ihP ihR =>
      exact moreStatic_callable ihP ihR
  | union hG hH ihG ihH =>
      exact moreStatic_union ihG ihH
  | intersection hG hH ihG ihH =>
      exact moreStatic_intersection ihG ihH
  | bottom =>
      exact moreStatic_refl gct .bottom
  | negClass =>
      rename_i C
      exact moreStatic_refl gct (.negClass C)
  | intersection_extra_left hX hE ihX =>
      exact
        moreStatic_intersection_left_of_upper ihX
          (IsSubtype.trans IsSubtype.objectTop
            (operatorExtraEnvelope_staticTop_subtype_upper (gct := gct) hE))
  | intersection_extra_right hX hE ihX =>
      exact
        moreStatic_intersection_right_of_upper ihX
          (IsSubtype.trans IsSubtype.objectTop
            (operatorExtraEnvelope_staticTop_subtype_upper (gct := gct) hE))
  | intersection_duplicate hX ihX =>
      exact moreStatic_intersection_intro ihX ihX

private theorem lookupMethodTy?_find
    (hlookup : lookupMethodTy? gct C attr = some (P, R)) :
    FindGMethodType gct C attr P R := by
  unfold lookupMethodTy? at hlookup
  cases hfc : findGClass gct C with
  | none =>
      simp [hfc] at hlookup
  | some c =>
      cases hcomp : computeGMro? gct C with
      | none =>
          simp [hfc, hcomp] at hlookup
      | some mro =>
          cases hfm : findGMethodInMro gct mro attr with
          | none =>
              simp [hfc, hcomp, hfm] at hlookup
          | some m =>
              simp [hfc, hcomp, hfm] at hlookup
              obtain ⟨cls, hfc', hmro⟩ := computeGMro?_sound hcomp
              rw [hfc] at hfc'
              cases hfc'
              rcases hlookup with ⟨hparam, hreturn⟩
              exact ⟨c, mro, m, hfc, hmro, hfm, hparam, hreturn⟩

private theorem findGClass_none_of_targetPrecision
    (hct : Checked.ClassTableTargetPrecision gcs₁ gcs₂)
    (h : findGClass gcs₁ cname = none) :
    findGClass gcs₂ cname = none :=
  findByName_none_of_forall₂ (fun hc => hc.name_eq) hct h

private theorem findGMethodInList_none_of_targetPrecision
    (hms : Forall₂ Checked.MethodTargetPrecision ms₁ ms₂)
    (h : findGMethodInList ms₁ mname = none) :
    findGMethodInList ms₂ mname = none :=
  findByName_none_of_forall₂ (fun hm => hm.name_eq) hms h

private theorem findGClass_targetPrecision
    (hct : Checked.ClassTableTargetPrecision gcs₁ gcs₂)
    (hfind : findGClass gcs₁ cname = some gc₁) :
    ∃ gc₂,
      findGClass gcs₂ cname = some gc₂ ∧
      Checked.ClassTargetPrecision gc₁ gc₂ :=
  findByName_some_of_forall₂ (fun hc => hc.name_eq) hct hfind

private theorem findGMethodInMro_none_of_targetPrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hfind : findGMethodInMro gct₁ mro attr = none) :
    findGMethodInMro gct₂ mro attr = none :=
  findMemberInHierarchy_none_transport
    (findGClass_none_of_targetPrecision hct)
    (findGClass_targetPrecision hct)
    (fun hgc => findGMethodInList_none_of_targetPrecision hgc.methods_prec)
    hfind

private theorem lookupMethodTy?_none_of_targetPrecision
    (hwfct₁ : WellFormedGClassTableCore gct₁)
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hlookup : lookupMethodTy? gct₁ C attr = none) :
    lookupMethodTy? gct₂ C attr = none := by
  unfold lookupMethodTy? at hlookup ⊢
  cases hfc : findGClass gct₁ C with
  | none =>
      have hfc₂ : findGClass gct₂ C = none :=
        findGClass_none_of_targetPrecision hct hfc
      simp [hfc₂]
  | some gc₁ =>
      let mro := (hwfct₁.raw.allMrosExist _ _ hfc).mro
      let hmro := (hwfct₁.raw.allMrosExist _ _ hfc).hmro
      have hcomp : computeGMro? gct₁ C = some mro :=
        computeGMro?_complete hfc hmro
      rw [hcomp] at hlookup
      cases hfind : findGMethodInMro gct₁ mro attr with
      | none =>
          obtain ⟨gc₂, hfc₂, hclassPrec⟩ := findGClass_targetPrecision hct hfc
          have hmro₂ : GComputeMro gct₂ gc₂ mro :=
            gComputeMro_transport
              (Checked.classTableTargetPrecision_to_classTableAnnotationPrecision hct)
              (Checked.classTargetPrecision_to_classAnnotationPrecision gct₁ hclassPrec)
              hmro
          have hcomp₂ : computeGMro? gct₂ C = some mro :=
            computeGMro?_complete hfc₂ hmro₂
          have hfind₂ : findGMethodInMro gct₂ mro attr = none :=
            findGMethodInMro_none_of_targetPrecision hct hfind
          simp [hfc₂, hcomp₂, hfind₂]
      | some _ =>
          have : False := by
            simp [hfc, hfind] at hlookup
          exact False.elim this

private theorem methodTy_targetPrecision_of_find
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hfind : FindGMethodType gct₁ C attr P₁ R₁) :
    ∃ P₂ R₂,
      FindGMethodType gct₂ C attr P₂ R₂ ∧
      AnnotationTargetPrecision P₁ P₂ ∧
      AnnotationTargetPrecision R₁ R₂ ∧
      CompileTargetPrecision
        (Checked.callParamAnnotationTarget R₁)
        (Checked.callParamAnnotationTarget R₂) :=
  Checked.findGMethodType_targetPrecision hct hfind

private theorem methodTy_callable_targetPrecision_of_find
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hfind : FindGMethodType gct₁ C attr P₁ R₁) :
    ∃ P₂ R₂,
      FindGMethodType gct₂ C attr P₂ R₂ ∧
      AnnotationTargetPrecision (.callable P₁ R₁) (.callable P₂ R₂) := by
  obtain ⟨P₂, R₂, hfind₂, hparam, hreturn, _⟩ :=
    methodTy_targetPrecision_of_find hct hfind
  exact ⟨P₂, R₂, hfind₂, CheckedTargetPrecision.callable hparam hreturn⟩

private theorem attrSourceTy?_witness_result_eq
    (hw₁ : AttrResultWitness gct attr G result₁)
    (hw₂ : AttrResultWitness gct attr G result₂) :
    result₁ = result₂ := by
  rw [← attrSourceTy?_of_witness hw₁]
  rw [← attrSourceTy?_of_witness hw₂]

private theorem moreStatic_callable_inv
    (hwfct : WellFormedGClassTableCore gct)
    (hmore : MoreStatic gct (.callable P₁ R₁) (.callable P₂ R₂)) :
    MoreStatic gct P₁ P₂ ∧ MoreStatic gct R₁ R₂ := by
  have hLower :
      IsSubtype (eraseClassTable gct) (upperBound P₁) (upperBound P₂) ∧
      IsSubtype (eraseClassTable gct) (lowerBound R₂) (lowerBound R₁) := by
    simpa [lowerBound] using
      (callable_subtype_inv
        (findClass_eraseClassTable hwfct.raw.boundMethodExists.hfind)
        (gComputeMro_eraseClassTable hwfct.raw.boundMethodExists.hmro)
        hmore.1)
  have hUpper :
      IsSubtype (eraseClassTable gct) (lowerBound P₂) (lowerBound P₁) ∧
      IsSubtype (eraseClassTable gct) (upperBound R₁) (upperBound R₂) := by
    simpa [upperBound] using
      (callable_subtype_inv
        (findClass_eraseClassTable hwfct.raw.boundMethodExists.hfind)
        (gComputeMro_eraseClassTable hwfct.raw.boundMethodExists.hmro)
        hmore.2)
  exact ⟨⟨hUpper.1, hLower.1⟩, ⟨hLower.2, hUpper.2⟩⟩

private theorem attrSourceTy?_preserves_operatorExtraEnvelope
    (hE : OperatorExtraEnvelope G)
    (hw : AttrResultWitness gct attr G (some R)) :
    OperatorExtraEnvelope R := by
  induction hE generalizing attr R with
  | any =>
      cases hw with
      | any =>
          exact .any
  | union_left hE ihE =>
      rename_i E X
      cases hw with
      | union_some hleft hright =>
          exact .union_left (ihE hleft)
  | union_right hE ihE =>
      rename_i X E
      cases hw with
      | union_some hleft hright =>
          exact .union_right (ihE hright)
  | intersection hE hF ihE ihF =>
      cases hw with
      | inter_left hleft _ =>
          exact ihE hleft
      | inter_right _ hright =>
          exact ihF hright
      | inter_both hleft hright =>
          exact .intersection (ihE hleft) (ihF hright)

private theorem attrCompare
    (hwfct₁ : WellFormedGClassTableCore gct₁)
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hoci : OperatorCompareInput G₁ G₂) :
    (∀ {attr R₁},
        AttrResultWitness gct₁ attr G₁ (some R₁) →
        ∃ R₂, AttrResultWitness gct₂ attr G₂ (some R₂) ∧ OperatorCompareInput R₁ R₂) ∧
    (∀ {attr R₂},
        AttrResultWitness gct₁ attr G₁ none →
        AttrResultWitness gct₂ attr G₂ (some R₂) →
        OperatorExtraEnvelope R₂) := by
  induction hoci with
  | any =>
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw
        cases hw with
        | any =>
            exact ⟨.any, .any, .any⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₁
  | toAny =>
      rename_i G
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        exact ⟨.any, .any, .toAny⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₂ with
        | any =>
            exact .any
  | class_ =>
      rename_i C
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁ with
        | class_some hlookup =>
            obtain ⟨P₂, R₂, hfind₂, hprecCall⟩ :=
              methodTy_callable_targetPrecision_of_find hct (lookupMethodTy?_find hlookup)
            exact
              ⟨.callable P₂ R₂,
                .class_some (lookupMethodTy?_of_find hfind₂),
                operatorCompareInput_of_annotationTargetPrecision hprecCall⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₁ with
        | class_none hlookup =>
            cases hw₂ with
            | class_some hlookup₂ =>
                have hnone₂ := lookupMethodTy?_none_of_targetPrecision hwfct₁ hct hlookup
                rw [hlookup₂] at hnone₂
                cases hnone₂
  | callable hP hR ihP ihR =>
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁ with
        | callable_some hlookup =>
            obtain ⟨P₂, R₂, hfind₂, hprecCall⟩ :=
              methodTy_callable_targetPrecision_of_find hct (lookupMethodTy?_find hlookup)
            exact
              ⟨.callable P₂ R₂,
                .callable_some (lookupMethodTy?_of_find hfind₂),
                operatorCompareInput_of_annotationTargetPrecision hprecCall⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₁ with
        | callable_none hlookup =>
            cases hw₂ with
            | callable_some hlookup₂ =>
                have hnone₂ :=
                  lookupMethodTy?_none_of_targetPrecision hwfct₁ hct hlookup
                rw [hlookup₂] at hnone₂
                cases hnone₂
  | union hG hH ihG ihH =>
      rcases ihG with ⟨ihGSome, ihGNone⟩
      rcases ihH with ⟨ihHSome, ihHNone⟩
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁ with
        | union_some hleft hright =>
            obtain ⟨RG₂, hwG₂, hcompG⟩ := ihGSome hleft
            obtain ⟨RH₂, hwH₂, hcompH⟩ := ihHSome hright
            exact
              ⟨.union RG₂ RH₂,
                .union_some hwG₂ hwH₂,
                .union hcompG hcompH⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₂ with
        | union_some hwG₂ hwH₂ =>
            cases hw₁ with
            | union_none_left hleft hright =>
                exact .union_left (ihGNone hleft hwG₂)
            | union_none_right hleft hright =>
                exact .union_right (ihHNone hright hwH₂)
  | intersection hG hH ihG ihH =>
      rename_i left₁ left₂ right₁ right₂
      rcases ihG with ⟨ihGSome, ihGNone⟩
      rcases ihH with ⟨ihHSome, ihHNone⟩
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁ with
        | inter_left hleft hright =>
            obtain ⟨RG₂, hwG₂, hcompG⟩ := ihGSome hleft
            cases hright₂ : attrSourceTy? gct₂ right₂ attr with
            | none =>
                exact ⟨RG₂, .inter_left hwG₂ (attrSourceTy?_witness_of hright₂), hcompG⟩
            | some RH₂ =>
                have hwH₂ : AttrResultWitness gct₂ attr right₂ (some RH₂) :=
                  attrSourceTy?_witness_of hright₂
                have henvH : OperatorExtraEnvelope RH₂ := ihHNone hright hwH₂
                exact
                  ⟨.intersection RG₂ RH₂,
                    .inter_both hwG₂ hwH₂,
                    .intersection_extra_left hcompG henvH⟩
        | inter_right hleft hright =>
            obtain ⟨RH₂, hwH₂, hcompH⟩ := ihHSome hright
            cases hleft₂ : attrSourceTy? gct₂ left₂ attr with
            | none =>
                exact ⟨RH₂, .inter_right (attrSourceTy?_witness_of hleft₂) hwH₂, hcompH⟩
            | some RG₂ =>
                have hwG₂ : AttrResultWitness gct₂ attr left₂ (some RG₂) :=
                  attrSourceTy?_witness_of hleft₂
                have henvG : OperatorExtraEnvelope RG₂ := ihGNone hleft hwG₂
                exact
                  ⟨.intersection RG₂ RH₂,
                    .inter_both hwG₂ hwH₂,
                    .intersection_extra_right hcompH henvG⟩
        | inter_both hleft hright =>
            obtain ⟨RG₂, hwG₂, hcompG⟩ := ihGSome hleft
            obtain ⟨RH₂, hwH₂, hcompH⟩ := ihHSome hright
            exact
              ⟨.intersection RG₂ RH₂,
                .inter_both hwG₂ hwH₂,
                .intersection hcompG hcompH⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₁ with
        | inter_none hleft hright =>
            cases hw₂ with
            | inter_left hwG₂ hwH₂ =>
                exact ihGNone hleft hwG₂
            | inter_right hwG₂ hwH₂ =>
                exact ihHNone hright hwH₂
            | inter_both hwG₂ hwH₂ =>
                exact .intersection (ihGNone hleft hwG₂) (ihHNone hright hwH₂)
  | bottom =>
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁ with
        | bottom =>
            exact ⟨.bottom, .bottom, .bottom⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₁
  | negClass =>
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        cases hw₁
      · intro attr R₂ hw₁ hw₂
        cases hw₂
  | intersection_extra_left hX hE ihX =>
      rename_i X X' E
      rcases ihX with ⟨ihXSome, ihXNone⟩
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        obtain ⟨RX₂, hwX₂, hcompX⟩ := ihXSome hw₁
        cases hE₂ : attrSourceTy? gct₂ E attr with
        | none =>
            exact ⟨RX₂, .inter_left hwX₂ (attrSourceTy?_witness_of hE₂), hcompX⟩
        | some RE₂ =>
            have hwE₂ : AttrResultWitness gct₂ attr E (some RE₂) :=
              attrSourceTy?_witness_of hE₂
            have henvE : OperatorExtraEnvelope RE₂ :=
              attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂
            exact
              ⟨.intersection RX₂ RE₂,
                .inter_both hwX₂ hwE₂,
                .intersection_extra_left hcompX henvE⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₂ with
        | inter_left hwX₂ hwE₂ =>
            exact ihXNone hw₁ hwX₂
        | inter_right hwX₂ hwE₂ =>
            exact attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂
        | inter_both hwX₂ hwE₂ =>
            exact .intersection
              (ihXNone hw₁ hwX₂)
              (attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂)
  | intersection_extra_right hX hE ihX =>
      rename_i X X' E
      rcases ihX with ⟨ihXSome, ihXNone⟩
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        obtain ⟨RX₂, hwX₂, hcompX⟩ := ihXSome hw₁
        cases hE₂ : attrSourceTy? gct₂ E attr with
        | none =>
            exact ⟨RX₂, .inter_right (attrSourceTy?_witness_of hE₂) hwX₂, hcompX⟩
        | some RE₂ =>
            have hwE₂ : AttrResultWitness gct₂ attr E (some RE₂) :=
              attrSourceTy?_witness_of hE₂
            have henvE : OperatorExtraEnvelope RE₂ :=
              attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂
            exact
              ⟨.intersection RE₂ RX₂,
                .inter_both hwE₂ hwX₂,
                .intersection_extra_right hcompX henvE⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₂ with
        | inter_left hwE₂ hwX₂ =>
            exact attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂
        | inter_right hwE₂ hwX₂ =>
            exact ihXNone hw₁ hwX₂
        | inter_both hwE₂ hwX₂ =>
            exact .intersection
              (attrSourceTy?_preserves_operatorExtraEnvelope hE hwE₂)
              (ihXNone hw₁ hwX₂)
  | intersection_duplicate hX ihX =>
      rcases ihX with ⟨ihXSome, ihXNone⟩
      refine ⟨?_, ?_⟩
      · intro attr R₁ hw₁
        obtain ⟨RX₂, hwX₂, hcompX⟩ := ihXSome hw₁
        exact
          ⟨.intersection RX₂ RX₂,
            .inter_both hwX₂ hwX₂,
            .intersection_duplicate hcompX⟩
      · intro attr R₂ hw₁ hw₂
        cases hw₂ with
        | inter_left hwX₂ _ =>
            exact ihXNone hw₁ hwX₂
        | inter_right _ hwX₂ =>
            exact ihXNone hw₁ hwX₂
        | inter_both hwX₂₁ hwX₂₂ =>
            exact .intersection (ihXNone hw₁ hwX₂₁) (ihXNone hw₁ hwX₂₂)

private theorem attrSourceTy?_some_of_compare
    (hwfct₁ : WellFormedGClassTableCore gct₁)
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hoci : OperatorCompareInput G₁ G₂)
    (hw₁ : AttrResultWitness gct₁ attr G₁ (some R₁)) :
    ∃ R₂, AttrResultWitness gct₂ attr G₂ (some R₂) ∧ OperatorCompareInput R₁ R₂ :=
  (attrCompare hwfct₁ hct hoci).1 hw₁

private theorem callSourceTy?_some_of_compare
    (_hwfct₁ : WellFormedGClassTableCore gct₁)
    (hwfct₂ : WellFormedGClassTableCore gct₂)
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hcallee : OperatorCompareInput G₁ G₂)
    (harg : OperatorCompareInput argTy₁ argTy₂)
    (hsrc₁ : SourceCallableTy gct₁ G₁)
    (hwfG₁ : WellFormedGTy gct₁ G₁)
    (hsrc₂ : SourceCallableTy gct₂ G₂)
    (hwfG₂ : WellFormedGTy gct₂ G₂)
    (hwfArg₁ : WellFormedGTy gct₁ argTy₁)
    (hwfArg₂ : WellFormedGTy gct₂ argTy₂)
    (hw₁ : CallResultWitness gct₁ argTy₁ (calleeSummarySrc gct₁ G₁) (some R₁)) :
    ∃ R₂,
      CallResultWitness gct₂ argTy₂ (calleeSummarySrc gct₂ G₂) (some R₂) ∧
      OperatorCompareInput R₁ R₂ := by
  let hctAnn : ClassTableAnnotationPrecision gct₁ gct₂ :=
    Checked.classTableTargetPrecision_to_classTableAnnotationPrecision hct
  induction hcallee generalizing argTy₁ argTy₂ R₁ with
  | any =>
      cases hw₁ with
      | tainted =>
          exact ⟨.any, .tainted, .any⟩
  | toAny =>
      rename_i G
      exact ⟨.any, .tainted, .toAny⟩
  | class_ =>
      cases hw₁
  | callable hP hR ihP ihR =>
      rename_i P₁ P₂ R₁' R₂'
      cases hsrc₁ with
      | callable hsrcP₁ hcheckedR₁ =>
          cases hwfG₁ with
          | callable hwfP₁ hwfR₁ =>
              cases hsrc₂ with
              | callable hsrcP₂ hcheckedR₂ =>
                  cases hwfG₂ with
                  | callable hwfP₂ hwfR₂ =>
                      cases hw₁ with
                      | leaf_hit happ =>
                          have hmoreCall :
                              MoreStatic gct₂
                                (.callable P₁ R₁')
                                (.callable P₂ R₂') :=
                            operatorCompareInput_moreStatic (.callable hP hR)
                          obtain ⟨hparamMore, hreturnMore⟩ :=
                            moreStatic_callable_inv hwfct₂ hmoreCall
                          have happ₂₁ : AssignableTo gct₂ argTy₁ P₁ := by
                            exact (assignableTo_transport hctAnn).mp happ
                          have happ₂₂ : AssignableTo gct₂ argTy₂ P₁ :=
                            assignableTo_moreDynamic_arg
                              (operatorCompareInput_moreStatic harg) happ₂₁
                          have happ₂ : AssignableTo gct₂ argTy₂ P₂ :=
                            assignableTo_moreDynamic_param hparamMore happ₂₂
                          exact ⟨R₂', .leaf_hit happ₂, hR⟩
  | union hG hH ihG ihH =>
      rename_i G₁ G₂ H₁ H₂
      cases hsrc₁ with
      | union hsrcG₁ hsrcH₁ =>
          cases hwfG₁ with
          | union hwfGG₁ hwfGH₁ =>
              cases hsrc₂ with
              | union hsrcG₂ hsrcH₂ =>
                  cases hwfG₂ with
                  | union hwfGG₂ hwfGH₂ =>
                      cases hw₁ with
                      | union_some hwG₁ hwH₁ =>
                          obtain ⟨RG₂, hwG₂, hcompG⟩ :=
                            ihG harg
                              hsrcG₁ hwfGG₁ hsrcG₂ hwfGG₂ hwfArg₁ hwfArg₂ hwG₁
                          obtain ⟨RH₂, hwH₂, hcompH⟩ :=
                            ihH harg
                              hsrcH₁ hwfGH₁ hsrcH₂ hwfGH₂ hwfArg₁ hwfArg₂ hwH₁
                          exact
                            ⟨.union RG₂ RH₂,
                              .union_some hwG₂ hwH₂,
                              .union hcompG hcompH⟩
  | intersection hG hH ihG ihH =>
      rename_i G₁ G₂ H₁ H₂
      cases hsrc₁ with
      | intersection hsrcG₁ hsrcH₁ =>
          cases hwfG₁ with
          | intersection hwfGG₁ hwfGH₁ =>
              cases hsrc₂ with
              | intersection hsrcG₂ hsrcH₂ =>
                  cases hwfG₂ with
                  | intersection hwfGG₂ hwfGH₂ =>
                      cases hw₁ with
                      | inter_left hwG₁ hwH₁none =>
                          obtain ⟨RG₂, hwG₂, hcompG⟩ :=
                            ihG harg
                              hsrcG₁ hwfGG₁ hsrcG₂ hwfGG₂ hwfArg₁ hwfArg₂ hwG₁
                          let resultH₂ :=
                            callSourceTy?
                              (gct := gct₂)
                              (s := calleeSummarySrc gct₂ H₂)
                              (argTy := argTy₂)
                              hwfct₂
                              (callableSummaryOk_calleeSummarySrc hsrcH₂ hwfGH₂)
                              hwfArg₂
                          cases hresultH₂ : resultH₂ with
                          | none =>
                              exact
                                ⟨RG₂,
                                  .inter_left hwG₂
                                    (callSourceTy?_witness_of
                                      (hwfct := hwfct₂)
                                      (hsum := callableSummaryOk_calleeSummarySrc hsrcH₂ hwfGH₂)
                                      (hwfArg := hwfArg₂)
                                      hresultH₂),
                                  hcompG⟩
                          | some RH₂ =>
                              exact
                                ⟨.any,
                                  .inter_both hwG₂
                                    (callSourceTy?_witness_of
                                      (hwfct := hwfct₂)
                                      (hsum := callableSummaryOk_calleeSummarySrc hsrcH₂ hwfGH₂)
                                      (hwfArg := hwfArg₂)
                                      hresultH₂),
                                  .toAny⟩
                      | inter_right hwG₁none hwH₁ =>
                          obtain ⟨RH₂, hwH₂, hcompH⟩ :=
                            ihH harg
                              hsrcH₁ hwfGH₁ hsrcH₂ hwfGH₂ hwfArg₁ hwfArg₂ hwH₁
                          let resultG₂ :=
                            callSourceTy?
                              (gct := gct₂)
                              (s := calleeSummarySrc gct₂ G₂)
                              (argTy := argTy₂)
                              hwfct₂
                              (callableSummaryOk_calleeSummarySrc hsrcG₂ hwfGG₂)
                              hwfArg₂
                          cases hresultG₂ : resultG₂ with
                          | none =>
                              exact
                                ⟨RH₂,
                                  .inter_right
                                    (callSourceTy?_witness_of
                                      (hwfct := hwfct₂)
                                      (hsum := callableSummaryOk_calleeSummarySrc hsrcG₂ hwfGG₂)
                                      (hwfArg := hwfArg₂)
                                      hresultG₂)
                                    hwH₂,
                                  hcompH⟩
                          | some RG₂ =>
                              exact
                                ⟨.any,
                                  .inter_both
                                    (callSourceTy?_witness_of
                                      (hwfct := hwfct₂)
                                      (hsum := callableSummaryOk_calleeSummarySrc hsrcG₂ hwfGG₂)
                                      (hwfArg := hwfArg₂)
                                      hresultG₂)
                                    hwH₂,
                                  .toAny⟩
                      | inter_both hwG₁ hwH₁ =>
                          obtain ⟨RG₂, hwG₂, hcompG⟩ :=
                            ihG harg
                              hsrcG₁ hwfGG₁ hsrcG₂ hwfGG₂ hwfArg₁ hwfArg₂ hwG₁
                          obtain ⟨RH₂, hwH₂, hcompH⟩ :=
                            ihH harg
                              hsrcH₁ hwfGH₁ hsrcH₂ hwfGH₂ hwfArg₁ hwfArg₂ hwH₁
                          exact ⟨.any, .inter_both hwG₂ hwH₂, .any⟩
  | bottom =>
      cases hw₁
  | negClass =>
      cases hw₁
  | intersection_extra_left hX hE ihX =>
      rename_i X X' E
      cases hsrc₂ with
      | intersection hsrcX₂ hsrcE₂ =>
          cases hwfG₂ with
          | intersection hwfX₂ hwfE₂ =>
              obtain ⟨RX₂, hwX₂, hcompX⟩ :=
                ihX harg
                  hsrc₁ hwfG₁ hsrcX₂ hwfX₂ hwfArg₁ hwfArg₂ hw₁
              let resultE₂ :=
                callSourceTy?
                  (gct := gct₂)
                  (s := calleeSummarySrc gct₂ E)
                  (argTy := argTy₂)
                  hwfct₂
                  (callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                  hwfArg₂
              cases hresultE₂ : resultE₂ with
              | none =>
                  exact
                    ⟨RX₂,
                      .inter_left hwX₂
                        (callSourceTy?_witness_of
                          (hwfct := hwfct₂)
                          (hsum := callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                          (hwfArg := hwfArg₂)
                          hresultE₂),
                      hcompX⟩
              | some RE₂ =>
                  exact
                    ⟨.any,
                      .inter_both hwX₂
                        (callSourceTy?_witness_of
                          (hwfct := hwfct₂)
                          (hsum := callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                          (hwfArg := hwfArg₂)
                          hresultE₂),
                      .toAny⟩
  | intersection_extra_right hX hE ihX =>
      rename_i X X' E
      cases hsrc₂ with
      | intersection hsrcE₂ hsrcX₂ =>
          cases hwfG₂ with
          | intersection hwfE₂ hwfX₂ =>
              obtain ⟨RX₂, hwX₂, hcompX⟩ :=
                ihX harg
                  hsrc₁ hwfG₁ hsrcX₂ hwfX₂ hwfArg₁ hwfArg₂ hw₁
              let resultE₂ :=
                callSourceTy?
                  (gct := gct₂)
                  (s := calleeSummarySrc gct₂ E)
                  (argTy := argTy₂)
                  hwfct₂
                  (callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                  hwfArg₂
              cases hresultE₂ : resultE₂ with
              | none =>
                  exact
                    ⟨RX₂,
                      .inter_right
                        (callSourceTy?_witness_of
                          (hwfct := hwfct₂)
                          (hsum := callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                          (hwfArg := hwfArg₂)
                          hresultE₂)
                        hwX₂,
                      hcompX⟩
              | some RE₂ =>
                  exact
                    ⟨.any,
                      .inter_both
                        (callSourceTy?_witness_of
                          (hwfct := hwfct₂)
                          (hsum := callableSummaryOk_calleeSummarySrc hsrcE₂ hwfE₂)
                          (hwfArg := hwfArg₂)
                          hresultE₂)
                        hwX₂,
                      .toAny⟩
  | intersection_duplicate hX ihX =>
      rename_i X X'
      cases hsrc₂ with
      | intersection hsrcX₂ _ =>
          cases hwfG₂ with
          | intersection hwfX₂ _ =>
              obtain ⟨RX₂, hwX₂, hcompX⟩ :=
                ihX harg
                  hsrc₁ hwfG₁ hsrcX₂ hwfX₂ hwfArg₁ hwfArg₂ hw₁
              exact ⟨.any, .inter_both hwX₂ hwX₂, .toAny⟩

private theorem operatorExtraEnvelope_callParamCheckedTarget_intersection_left
    (hE : OperatorExtraEnvelope E) :
    callParamCheckedTarget gct (.intersection E X) =
      callParamCheckedTarget gct X := by
  have hEAny := operatorExtraEnvelope_callParamTarget_any (gct := gct) hE
  unfold callParamCheckedTarget
  rw [show callParamTarget gct (.intersection E X) =
      callParamTarget gct (.intersection .any X) by
        simp [callParamTarget, hEAny]]
  exact congrArg checkedTargetOfRuntimePublicTy
    (callParamTarget_intersection_any_left (gct := gct) (G := X))

private theorem operatorExtraEnvelope_callParamCheckedTarget_intersection_right
    (hE : OperatorExtraEnvelope E) :
    callParamCheckedTarget gct (.intersection X E) =
      callParamCheckedTarget gct X := by
  have hEAny := operatorExtraEnvelope_callParamTarget_any (gct := gct) hE
  unfold callParamCheckedTarget
  rw [show callParamTarget gct (.intersection X E) =
      callParamTarget gct (.intersection X .any) by
        simp [callParamTarget, hEAny]]
  exact congrArg checkedTargetOfRuntimePublicTy
    (callParamTarget_intersection_any_right (gct := gct) (G := X))

private theorem operatorCompareInput_equalSource_into_uncollapsed_intersection
    (ihG :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂))
    (ihH :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ H₁)
        (callParamCheckedTarget gct₂ H₂))
    (hEq₁ : callParamTarget gct₁ G₁ = callParamTarget gct₁ H₁)
    (_hG₁Any : callParamTarget gct₁ G₁ ≠ .any)
    (_hG₁Bottom : callParamTarget gct₁ G₁ ≠ .bottom)
    (hG₂Any : callParamTarget gct₂ G₂ ≠ .any)
    (hH₂Any : callParamTarget gct₂ H₂ ≠ .any)
    (hG₂Bottom : callParamTarget gct₂ G₂ ≠ .bottom)
    (hH₂Bottom : callParamTarget gct₂ H₂ ≠ .bottom)
    (hEq₂ : callParamTarget gct₂ G₂ ≠ callParamTarget gct₂ H₂) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ G₁)
      (callParamCheckedTarget gct₂ (.intersection G₂ H₂)) := by
  have hsrcEq :
      callParamCheckedTarget gct₁ G₁ =
        callParamCheckedTarget gct₁ H₁ := by
    simp [callParamCheckedTarget, hEq₁]
  have ihH' :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ H₂) := by
    simpa [hsrcEq] using ihH
  rw [callParamCheckedTarget_intersection_of_uncollapsed
    (gct := gct₂) (G := G₂) (H := H₂)
    hG₂Any hH₂Any hG₂Bottom hH₂Bottom hEq₂]
  have hEqChecked :
      callParamCheckedTarget gct₂ G₂ ≠ callParamCheckedTarget gct₂ H₂ := by
    intro hEq
    apply hEq₂
    have hInterp := congrArg interpTarget hEq
    simpa [interpTarget_callParamCheckedTarget] using hInterp
  by_cases hOrd :
      Checked.checkedTargetCmp
          (callParamCheckedTarget gct₂ G₂)
          (callParamCheckedTarget gct₂ H₂) = .gt
  · unfold Checked.normalizeCallParamAnnotationIntersection
    rw [if_neg hEqChecked, if_pos hOrd]
    exact .meet ihH' ihG
  · unfold Checked.normalizeCallParamAnnotationIntersection
    rw [if_neg hEqChecked, if_neg hOrd]
    exact .meet ihG ihH'

private theorem operatorCompareInput_callParamCheckedTargetPrecision
    (hoci : OperatorCompareInput G₁ G₂) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ G₁)
      (callParamCheckedTarget gct₂ G₂) := by
  induction hoci with
  | any =>
      exact .refl
  | toAny =>
      rename_i G
      simpa [callParamCheckedTarget] using
        (callParamCheckedTarget_toAny gct₁ G)
  | class_ =>
      rename_i C
      simpa [callParamCheckedTarget, callParamTarget] using
        (CompileTargetPrecision.refl
          (T := checkedTargetOfRuntimePublicTy (.class_ C : GTy)))
  | callable hP hR ihP ihR =>
      simpa [callParamCheckedTarget, callParamTarget] using
        (CompileTargetPrecision.refl (T := CheckedTarget.any))
  | union hG hH ihG ihH =>
      exact callParamCheckedTarget_union_congr ihG ihH
  | intersection hG hH ihG ihH =>
      rename_i G₁ G₂ H₁ H₂
      by_cases hG₁Any : callParamTarget gct₁ G₁ = .any
      · have hG₂Any :=
          callParamTarget_eq_any_of_compileTargetPrecision_left_any
            (gct₁ := gct₁) (gct₂ := gct₂) ihG hG₁Any
        rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
          (gct := gct₁) (G := G₁) (H := H₁) hG₁Any]
        rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
          (gct := gct₂) (G := G₂) (H := H₂) hG₂Any]
        exact ihH
      · by_cases hH₁Any : callParamTarget gct₁ H₁ = .any
        · have hH₂Any :=
            callParamTarget_eq_any_of_compileTargetPrecision_left_any
              (gct₁ := gct₁) (gct₂ := gct₂) ihH hH₁Any
          rw [callParamCheckedTarget_intersection_right_of_callParamTarget_any
            (gct := gct₁) (G := G₁) (H := H₁) hH₁Any]
          rw [callParamCheckedTarget_intersection_right_of_callParamTarget_any
            (gct := gct₂) (G := G₂) (H := H₂) hH₂Any]
          exact ihG
        · by_cases hG₁Bottom : callParamTarget gct₁ G₁ = .bottom
          · have hsrc :
                callParamCheckedTarget gct₁ (.intersection G₁ H₁) = .bottom := by
              unfold callParamCheckedTarget
              rw [show callParamTarget gct₁ (.intersection G₁ H₁) =
                  callParamTarget gct₁ (.intersection .bottom H₁) by
                    simp [callParamTarget, hG₁Bottom]]
              simpa using
                (callParamCheckedTarget_intersection_bottom_left
                  (gct := gct₁) (G := H₁))
            rw [hsrc]
            exact .fromBottom
          · by_cases hH₁Bottom : callParamTarget gct₁ H₁ = .bottom
            · have hsrc :
                  callParamCheckedTarget gct₁ (.intersection G₁ H₁) = .bottom := by
                unfold callParamCheckedTarget
                rw [show callParamTarget gct₁ (.intersection G₁ H₁) =
                    callParamTarget gct₁ (.intersection G₁ .bottom) by
                      simp [callParamTarget, hH₁Bottom]]
                simpa using
                  (callParamCheckedTarget_intersection_bottom_right
                    (gct := gct₁) (G := G₁))
              rw [hsrc]
              exact .fromBottom
            · by_cases hEq₁ : callParamTarget gct₁ G₁ = callParamTarget gct₁ H₁
              · have hsrcEq :
                    callParamCheckedTarget gct₁ G₁ =
                      callParamCheckedTarget gct₁ H₁ := by
                  simp [callParamCheckedTarget, hEq₁]
                rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                  (gct := gct₁) (G := G₁) (H := H₁) hEq₁]
                by_cases hG₂Any : callParamTarget gct₂ G₂ = .any
                · rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
                    (gct := gct₂) (G := G₂) (H := H₂) hG₂Any]
                  simpa [hsrcEq] using ihH
                · by_cases hH₂Any : callParamTarget gct₂ H₂ = .any
                  · rw [callParamCheckedTarget_intersection_right_of_callParamTarget_any
                      (gct := gct₂) (G := G₂) (H := H₂) hH₂Any]
                    exact ihG
                  · by_cases hG₂Bottom : callParamTarget gct₂ G₂ = .bottom
                    · have : callParamTarget gct₁ G₁ = .bottom :=
                        callParamTarget_eq_bottom_of_compileTargetPrecision_right
                          ihG hG₂Bottom
                      contradiction
                    · by_cases hH₂Bottom : callParamTarget gct₂ H₂ = .bottom
                      · have : callParamTarget gct₁ H₁ = .bottom :=
                          callParamTarget_eq_bottom_of_compileTargetPrecision_right
                            ihH hH₂Bottom
                        have : callParamTarget gct₁ G₁ = .bottom :=
                          hEq₁.trans this
                        contradiction
                      · by_cases hEq₂ : callParamTarget gct₂ G₂ = callParamTarget gct₂ H₂
                        · rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                            (gct := gct₂) (G := G₂) (H := H₂) hEq₂]
                          exact ihG
                        · exact
                            operatorCompareInput_equalSource_into_uncollapsed_intersection
                              (gct₁ := gct₁) (gct₂ := gct₂)
                              ihG ihH hEq₁ hG₁Any hG₁Bottom
                              hG₂Any hH₂Any hG₂Bottom hH₂Bottom hEq₂
              · by_cases hG₂Any : callParamTarget gct₂ G₂ = .any
                · rw [callParamCheckedTarget_intersection_of_uncollapsed
                    (gct := gct₁) (G := G₁) (H := H₁)
                    hG₁Any hH₁Any hG₁Bottom hH₁Bottom hEq₁]
                  rw [callParamCheckedTarget_intersection_left_of_callParamTarget_any
                    (gct := gct₂) (G := G₂) (H := H₂) hG₂Any]
                  exact compileTargetPrecision_normalizeIntersection_left_toAny
                    (compileTargetPrecision_trans ihG
                      (by simpa [callParamCheckedTarget, hG₂Any] using
                        (callParamCheckedTarget_toAny gct₂ G₂)))
                    ihH
                · by_cases hH₂Any : callParamTarget gct₂ H₂ = .any
                  · rw [callParamCheckedTarget_intersection_of_uncollapsed
                      (gct := gct₁) (G := G₁) (H := H₁)
                      hG₁Any hH₁Any hG₁Bottom hH₁Bottom hEq₁]
                    rw [callParamCheckedTarget_intersection_right_of_callParamTarget_any
                      (gct := gct₂) (G := G₂) (H := H₂) hH₂Any]
                    exact compileTargetPrecision_normalizeIntersection_right_toAny
                      ihG
                      (compileTargetPrecision_trans ihH
                        (by
                          simpa [callParamCheckedTarget, hH₂Any] using
                            (callParamCheckedTarget_toAny gct₂ H₂)))
                  · by_cases hG₂Bottom : callParamTarget gct₂ G₂ = .bottom
                    · have : callParamTarget gct₁ G₁ = .bottom :=
                        callParamTarget_eq_bottom_of_compileTargetPrecision_right
                          ihG hG₂Bottom
                      contradiction
                    · by_cases hH₂Bottom : callParamTarget gct₂ H₂ = .bottom
                      · have : callParamTarget gct₁ H₁ = .bottom :=
                          callParamTarget_eq_bottom_of_compileTargetPrecision_right
                            ihH hH₂Bottom
                        contradiction
                      · by_cases hEq₂ : callParamTarget gct₂ G₂ = callParamTarget gct₂ H₂
                        · rw [callParamCheckedTarget_intersection_of_uncollapsed
                            (gct := gct₁) (G := G₁) (H := H₁)
                            hG₁Any hH₁Any hG₁Bottom hH₁Bottom hEq₁]
                          rw [callParamCheckedTarget_intersection_of_callParamTarget_eq
                            (gct := gct₂) (G := G₂) (H := H₂) hEq₂]
                          exact compileTargetPrecision_normalizeIntersection_right_toAny
                            ihG
                            (CompileTargetPrecision.toAny
                              (T := callParamCheckedTarget gct₁ H₁))
                        · rw [callParamCheckedTarget_intersection_of_uncollapsed
                            (gct := gct₁) (G := G₁) (H := H₁)
                            hG₁Any hH₁Any hG₁Bottom hH₁Bottom hEq₁]
                          rw [callParamCheckedTarget_intersection_of_uncollapsed
                            (gct := gct₂) (G := G₂) (H := H₂)
                            hG₂Any hH₂Any hG₂Bottom hH₂Bottom hEq₂]
                          have hNeChecked :
                              callParamCheckedTarget gct₂ G₂ ≠
                                callParamCheckedTarget gct₂ H₂ := by
                            intro hEq
                            apply hEq₂
                            have hInterp := congrArg interpTarget hEq
                            simpa [interpTarget_callParamCheckedTarget] using hInterp
                          exact compileTargetPrecision_normalizeIntersection
                            ihG ihH hNeChecked
  | bottom =>
      simpa [callParamCheckedTarget, callParamTarget] using
        (CompileTargetPrecision.refl (T := CheckedTarget.bottom))
  | negClass =>
      rename_i C
      simpa [callParamCheckedTarget, callParamTarget] using
        (CompileTargetPrecision.refl
          (T := checkedTargetOfRuntimePublicTy (.negClass C : GTy)))
  | intersection_extra_left hX hE ihX =>
      rw [operatorExtraEnvelope_callParamCheckedTarget_intersection_right
        (gct := gct₂) (hE := hE) (X := _)]
      exact ihX
  | intersection_extra_right hX hE ihX =>
      rw [operatorExtraEnvelope_callParamCheckedTarget_intersection_left
        (gct := gct₂) (hE := hE) (X := _)]
      exact ihX
  | intersection_duplicate hX ihX =>
      rw [callParamCheckedTarget_intersection_diag gct₂ _]
      exact ihX

private theorem gSrcInfer_operatorCompareInput
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (h₁ : GSrcInfer gct₁ hwfct₁ Γ₁ e srcTy₁)
    (h₂ : GSrcInfer gct₂ hwfct₂ Γ₂ e srcTy₂) :
    OperatorCompareInput srcTy₁ srcTy₂ := by
  induction h₁ generalizing Γ₂ srcTy₂ with
  | var hlook₁ =>
      cases h₂ with
      | var hlook₂ =>
          obtain ⟨b₂, hlook₂', hb⟩ := sBindingEnvPrecision_lookup hΓ hlook₁
          rw [hlook₂] at hlook₂'
          cases hlook₂'
          exact operatorCompareInput_of_annotationTargetPrecision hb.source_prec
  | constNone =>
      cases h₂
      exact .class_
  | constTrue =>
      cases h₂
      exact .class_
  | constFalse =>
      cases h₂
      exact .class_
  | new hfind₁ hbool₁ hnone₁ hbm₁ =>
      cases h₂ with
      | new hfind₂ hbool₂ hnone₂ hbm₂ =>
          exact .class_
  | attrAccess hbase₁ hattr₁ ihBase =>
      cases h₂ with
      | attrAccess hbase₂ hattr₂ =>
          have hbaseCompare := ihBase hΓ hbase₂
          have hw₁ := attrSourceTy?_witness_of hattr₁
          obtain ⟨R₂', hw₂', hcomp⟩ :=
            attrSourceTy?_some_of_compare hwfct₁ hct hbaseCompare hw₁
          have hw₂ := attrSourceTy?_witness_of hattr₂
          have hEq : (some R₂') = (some srcTy₂) :=
            attrSourceTy?_witness_result_eq hw₂' hw₂
          cases hEq
          exact hcomp
  | call hcallee₁ harg₁ hcallee_callable₁ hcallee_wf₁ harg_wf₁ hcall₁ ihCallee ihArg =>
      cases h₂ with
      | call hcallee₂ harg₂ hcallee_callable₂ hcallee_wf₂ harg_wf₂ hcall₂ =>
          have hcalleeCompare := ihCallee hΓ hcallee₂
          have hargCompare := ihArg hΓ harg₂
          have hw₁ := by
            exact
              callSourceTy?_witness_of
                (hwfct := hwfct₁)
                (hsum := callableSummaryOk_calleeSummarySrc hcallee_callable₁ hcallee_wf₁)
                (hwfArg := harg_wf₁)
                hcall₁
          obtain ⟨R₂', hw₂', hcomp⟩ :=
            callSourceTy?_some_of_compare
              hwfct₁ hwfct₂ hct
              hcalleeCompare hargCompare
              hcallee_callable₁ hcallee_wf₁
              hcallee_callable₂ hcallee_wf₂
              harg_wf₁ harg_wf₂ hw₁
          have hw₂ := by
            exact
              callSourceTy?_witness_of
                (hwfct := hwfct₂)
                (hsum := callableSummaryOk_calleeSummarySrc hcallee_callable₂ hcallee_wf₂)
                (hwfArg := harg_wf₂)
                hcall₂
          have hEq : (some R₂') = (some srcTy₂) :=
            callSourceTy?_witness_result_eq
              (hwfct := hwfct₂)
              (hsum := callableSummaryOk_calleeSummarySrc hcallee_callable₂ hcallee_wf₂)
              (hwfArg := harg_wf₂)
              hw₂' hw₂
          cases hEq
          exact hcomp
  | cond hni₁ htest₁ hbool₁ hthen₁ helse₁ ihTest ihThen ihElse =>
      cases h₂ with
      | cond hni₂ htest₂ hbool₂ hthen₂ helse₂ =>
          exact .union (ihThen hΓ hthen₂) (ihElse hΓ helse₂)
      | condIsInstance =>
          cases hni₁
  | isInstance hlook₁ hfind₁ =>
      cases h₂
      exact .class_
  | condIsInstance hlook₁ hfind₁ hthen₁ helse₁ ihThen ihElse =>
      rename_i b₁ C cls₁ thenBranch thenSrcTy₁ elseBranch elseSrcTy₁ Γ₁ x
      cases h₂ with
      | cond hni₂ htest₂ hbool₂ hthen₂ helse₂ =>
          cases hni₂
      | condIsInstance hlook₂ hfind₂ hthen₂ helse₂ =>
          rename_i b₂ cls₂ thenSrcTy₂ elseSrcTy₂
          obtain ⟨b₂', hlook₂', hb⟩ := sBindingEnvPrecision_lookup hΓ hlook₁
          rw [hlook₂] at hlook₂'
          cases hlook₂'
          have hprecThen :
              AnnotationTargetPrecision
                (.intersection b₁.sourceTy (.class_ C))
                (.intersection b₂.sourceTy (.class_ C)) :=
            .intersection hb.source_prec .refl
          have hcallPrecThen :
              CompileTargetPrecision
                (callParamCheckedTarget ([] : GClassTable)
                  (.intersection b₁.sourceTy (.class_ C)))
                (callParamCheckedTarget ([] : GClassTable)
                  (.intersection b₂.sourceTy (.class_ C))) := by
            exact callParamCheckedTarget_intersection_class_right_congr
              (gct₁ := ([] : GClassTable))
              (gct₂ := ([] : GClassTable))
              (C := C)
              hb.source_callParam_prec
          have hprecElse :
              AnnotationTargetPrecision
                (.intersection b₁.sourceTy (.negClass C))
                (.intersection b₂.sourceTy (.negClass C)) :=
            .intersection hb.source_prec .refl
          have hcallPrecElse :
              CompileTargetPrecision
                (callParamCheckedTarget ([] : GClassTable)
                  (.intersection b₁.sourceTy (.negClass C)))
                (callParamCheckedTarget ([] : GClassTable)
                  (.intersection b₂.sourceTy (.negClass C))) := by
            exact callParamCheckedTarget_intersection_negClass_right_congr
              (gct₁ := ([] : GClassTable))
              (gct₂ := ([] : GClassTable))
              (C := C)
              hb.source_callParam_prec
          exact
            .union
              (ihThen (sBindingEnvPrecision_updateSource hΓ hprecThen hcallPrecThen) hthen₂)
              (ihElse (sBindingEnvPrecision_updateSource hΓ hprecElse hcallPrecElse) helse₂)

theorem gSrcInfer_moreStatic
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (h₁ : GSrcInfer gct₁ hwfct₁ Γ₁ e srcTy₁)
    (h₂ : GSrcInfer gct₂ hwfct₂ Γ₂ e srcTy₂) :
    MoreStatic gct₂ srcTy₁ srcTy₂ :=
  operatorCompareInput_moreStatic (gct := gct₂)
    (gSrcInfer_operatorCompareInput hct hΓ h₁ h₂)

theorem gSrcInfer_callParamCheckedTargetPrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (h₁ : GSrcInfer gct₁ hwfct₁ Γ₁ e srcTy₁)
    (h₂ : GSrcInfer gct₂ hwfct₂ Γ₂ e srcTy₂) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ srcTy₁)
      (callParamCheckedTarget gct₂ srcTy₂) :=
  operatorCompareInput_callParamCheckedTargetPrecision
    (gct₁ := gct₁)
    (gct₂ := gct₂)
    (gSrcInfer_operatorCompareInput hct hΓ h₁ h₂)

theorem checkedBranchRefine_right_refined_then_compileCheck_package_counterexample
    (hwfct : WellFormedGClassTableCore gct)
    (x : Identifier) :
    ∃ _hpack :
        CompileCheckEnvAlignmentPackage gct
          [{ name := x, sourceTy := .callable .any .any }]
          [{ name := x, sourceTy := .any }]
          [(x, .callable .any .any)]
          [(x, .any)],
      CheckedBranchRefineOk gct .any boolClass ∧
      ¬ CheckedBranchRefineOk gct (.callable .any .any) boolClass ∧
      ¬ TyEnvAnnotationPrecision gct
          [(x, .callable .any .any)]
          (GTyEnv.update [(x, GTy.any)] x
            (.intersection GTy.any (.class_ boolClass))) := by
  let Γ₁ : SBindingEnv := [{ name := x, sourceTy := .callable .any .any }]
  let Γ₂ : SBindingEnv := [{ name := x, sourceTy := .any }]
  let Δ₁ : GTyEnv := [(x, .callable .any .any)]
  let Δ₂ : GTyEnv := [(x, .any)]
  have hΓ : SBindingEnvPrecision Γ₁ Γ₂ := by
    exact .cons ⟨rfl, .toAny, .refl⟩ .nil
  have hSourceEnv₁ : SourceEnvOk gct Γ₁ := by
    intro b hb
    simp [Γ₁] at hb
    cases hb
    exact ⟨.callable .any (runtimePublicAnnotation_mk (.classFormula .any)), .callable .any .any⟩
  have hSourceEnv₂ : SourceEnvOk gct Γ₂ := by
    intro b hb
    simp [Γ₂] at hb
    cases hb
    exact ⟨.any, .any⟩
  have hΔ :
      TyEnvAnnotationPrecision gct Δ₁ Δ₂ := by
    exact .cons
      (annotationTargetPrecision_sound (gct := gct)
        (show AnnotationTargetPrecision (.callable .any .any) .any from
          CheckedTargetPrecision.toAny
            (T := checkedTargetOfGTy (.callable .any .any))))
      .nil
  have hElab₁ : ElabEnvOk gct Γ₁ Δ₁ := by
    exact .cons
      ⟨rfl,
        runtimePublicAnnotation_mk (.callable (.classFormula .any) (.classFormula .any)),
        .callable .any .any,
        gradualSubtype_refl gct (.callable .any .any)⟩
      .nil
  have hElab₂ : ElabEnvOk gct Γ₂ Δ₂ := by
    exact .cons
      ⟨rfl,
        runtimePublicAnnotation_mk (.classFormula .any),
        .any,
        gradualSubtype_refl gct .any⟩
      .nil
  refine ⟨compileCheckEnvAlignmentPackage_of_structural gct
      hΓ hSourceEnv₁ hSourceEnv₂ hΔ hElab₁ hElab₂, ?_, ?_, ?_⟩
  · exact checkedBranchRefineOk_any_boolClass gct
  · exact not_checkedBranchRefineOk_callable_any_boolClass hwfct
  · simpa [Δ₁, Δ₂, GTyEnv.update, NamedEnv.update] using
      not_tyEnvAnnotationPrecision_singleton_of_not_moreStatic
        (gct := gct)
        (x := x)
        (T₁ := .callable .any .any)
        (T₂ := .intersection .any (.class_ boolClass))
        (not_moreStatic_callable_any_then_refined_bool hwfct)

import FwPython.Gradual.TypeSystem.Source.Core

/-! # Single-type gradual source typing

Principal source typing for the safe-domain single-type front end. -/

/-- An expression is not syntactically an `isInstance` check. Used to
    keep ordinary `cond` and `condIsInstance` disjoint. -/
def GExpr.notIsInstance : GExpr → Prop
  | .isInstance _ _ => False
  | _ => True

/-- Principal source typing witness. For fixed class table, source
    environment, and expression, the synthesized source type is unique. -/
inductive GSrcInfer (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct) :
    SBindingEnv → GExpr → GTy → Type where
  | var :
      Γ.lookupBinding x = some b →
      GSrcInfer gct hwfct Γ (.var x) b.sourceTy
  | constNone :
      GSrcInfer gct hwfct Γ .constNone (.class_ noneClass)
  | constTrue :
      GSrcInfer gct hwfct Γ .constTrue (.class_ boolClass)
  | constFalse :
      GSrcInfer gct hwfct Γ .constFalse (.class_ boolClass)
  | new :
      findGClass gct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      GSrcInfer gct hwfct Γ (.new cname) (.class_ cname)
  | attrAccess :
      GSrcInfer gct hwfct Γ base baseSrcTy →
      attrSourceTy? gct baseSrcTy attr = some R →
      GSrcInfer gct hwfct Γ (.attrAccess base attr) R
  | call :
      GSrcInfer gct hwfct Γ callee calleeSrcTy →
      GSrcInfer gct hwfct Γ arg argSrcTy →
      (hcallee_callable : SourceCallableTy gct calleeSrcTy) →
      (hcallee_wf : WellFormedGTy gct calleeSrcTy) →
      (harg_wf : WellFormedGTy gct argSrcTy) →
      (hcall :
        callSourceTy?
            (gct := gct)
            (s := calleeSummarySrc gct calleeSrcTy)
            (argTy := argSrcTy)
            hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable hcallee_wf)
            harg_wf
          = some R) →
      GSrcInfer gct hwfct Γ (.call callee arg) R
  | cond :
      condExpr.notIsInstance →
      GSrcInfer gct hwfct Γ condExpr testSrcTy →
      AssignableTo gct testSrcTy (.class_ boolClass) →
      GSrcInfer gct hwfct Γ thenBranch thenSrcTy →
      GSrcInfer gct hwfct Γ elseBranch elseSrcTy →
      GSrcInfer gct hwfct Γ (.cond condExpr thenBranch elseBranch) (.union thenSrcTy elseSrcTy)
  | isInstance :
      Γ.lookupBinding x = some b →
      findGClass gct C = some cls →
      GSrcInfer gct hwfct Γ (.isInstance x C) (.class_ boolClass)
  | condIsInstance :
      Γ.lookupBinding x = some b →
      findGClass gct C = some cls →
      GSrcInfer gct hwfct
        (Γ.updateSource x (.intersection b.sourceTy (.class_ C)))
        thenBranch thenSrcTy →
      GSrcInfer gct hwfct
        (Γ.updateSource x (.intersection b.sourceTy (.negClass C)))
        elseBranch elseSrcTy →
      GSrcInfer gct hwfct Γ
        (.cond (.isInstance x C) thenBranch elseBranch)
        (.union thenSrcTy elseSrcTy)

private theorem gSrcInfer_props
    (henv : SourceEnvOk gct Γ)
    (hinfer : GSrcInfer gct hwfct Γ e srcTy) :
    SourceCallableTy gct srcTy ∧ WellFormedGTy gct srcTy := by
  induction hinfer with
  | var hlook =>
    exact sourceEnvOk_lookup henv hlook
  | constNone =>
    exact ⟨.class_, .class_ hwfct.raw.noneExists.hfind hwfct.raw.noneExists.hmro⟩
  | constTrue | constFalse | isInstance _ _ =>
    exact ⟨.class_, .class_ hwfct.raw.boolExists.hfind hwfct.raw.boolExists.hmro⟩
  | new hfind _ _ _ =>
    exact ⟨.class_, .class_ hfind (hwfct.raw.allMrosExist _ _ hfind).hmro⟩
  | attrAccess hbase hattr ih =>
    exact attrSourceTy?_callable_and_wf hwfct hattr
  | call hcallee harg hcallee_callable hcallee_wf harg_wf hcall ihC ihA =>
    exact callSourceTy?_callable_and_wf
      hwfct
      (callableSummaryOk_calleeSummarySrc hcallee_callable hcallee_wf)
      harg_wf
      hcall
  | cond _ _ _ hthen helse _ ihThen ihElse =>
    have hThen := ihThen henv
    have hElse := ihElse henv
    exact ⟨.union hThen.1 hElse.1, .union hThen.2 hElse.2⟩
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
    rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
    have hb := sourceEnvOk_lookup henv hlook
    let hmroC := (hwfct.raw.allMrosExist _ _ hfind).hmro
    have hclassWf : WellFormedGTy gct (.class_ C) := .class_ hfind hmroC
    have henvThen :
        SourceEnvOk gct (Γ'.updateSource x (.intersection b.sourceTy (.class_ C))) :=
      sourceEnvOk_updateSource henv hlook
        (.intersection hb.1 .class_)
        (.intersection hb.2 hclassWf)
    have henvElse :
        SourceEnvOk gct
          (Γ'.updateSource x (.intersection b.sourceTy (.negClass C))) :=
      sourceEnvOk_updateSource henv hlook
        (.intersection hb.1 .negClass)
        (.intersection hb.2 (.negClass hfind hmroC))
    have hThen := ihThen henvThen
    have hElse := ihElse henvElse
    exact ⟨.union hThen.1 hElse.1, .union hThen.2 hElse.2⟩

theorem gSrcInfer_sourceAdmissible
    (henv : SourceEnvOk gct Γ)
    (hinfer : GSrcInfer gct hwfct Γ e srcTy) :
    SourceCallableTy gct srcTy :=
  (gSrcInfer_props henv hinfer).1

theorem gSrcInfer_sourceWellFormed
    (henv : SourceEnvOk gct Γ)
    (hinfer : GSrcInfer gct hwfct Γ e srcTy) :
    WellFormedGTy gct srcTy :=
  (gSrcInfer_props henv hinfer).2

theorem gSrcInfer_principal_unique :
    GSrcInfer gct hwfct Γ e srcTy₁ →
    GSrcInfer gct hwfct Γ e srcTy₂ →
    srcTy₁ = srcTy₂
  | .var hlook₁, .var hlook₂ => by
    rw [hlook₁] at hlook₂
    cases hlook₂
    rfl
  | .constNone, .constNone
  | .constTrue, .constTrue
  | .constFalse, .constFalse
  | .new .., .new ..
  | .isInstance .., .isInstance .. =>
    rfl
  | .attrAccess hbase₁ hattr₁, .attrAccess hbase₂ hattr₂ => by
    obtain rfl := gSrcInfer_principal_unique hbase₁ hbase₂
    rw [hattr₁] at hattr₂
    cases hattr₂
    rfl
  | .call hcallee₁ harg₁ hcallee_callable₁ hcallee_wf₁ harg_wf₁ hcall₁,
    .call hcallee₂ harg₂ hcallee_callable₂ hcallee_wf₂ harg_wf₂ hcall₂ => by
    obtain rfl := gSrcInfer_principal_unique hcallee₁ hcallee₂
    obtain rfl := gSrcInfer_principal_unique harg₁ harg₂
    have htransport :
        callSourceTy?
            (gct := gct) hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable₁ hcallee_wf₁)
            harg_wf₁ =
          callSourceTy?
            (gct := gct) hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable₂ hcallee_wf₂)
            harg_wf₂ := by
      exact
        callSourceTy?_transport
          (hct := classTableAnnotationPrecision_refl gct)
          hwfct hwfct
          (callableSummaryOk_calleeSummarySrc hcallee_callable₁ hcallee_wf₁)
          (callableSummaryOk_calleeSummarySrc hcallee_callable₂ hcallee_wf₂)
          harg_wf₁ harg_wf₂
    have hcall₂' :
        callSourceTy?
            (gct := gct) hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable₁ hcallee_wf₁)
            harg_wf₁ =
          some srcTy₂ := by
      calc
        callSourceTy?
            (gct := gct) hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable₁ hcallee_wf₁)
            harg_wf₁ =
          callSourceTy?
            (gct := gct) hwfct
            (callableSummaryOk_calleeSummarySrc hcallee_callable₂ hcallee_wf₂)
            harg_wf₂ := htransport
        _ = some srcTy₂ := hcall₂
    rw [hcall₁] at hcall₂'
    cases hcall₂'
    rfl
  | .cond _ _ _ hthen₁ helse₁, .cond _ _ _ hthen₂ helse₂ => by
    obtain rfl := gSrcInfer_principal_unique hthen₁ hthen₂
    obtain rfl := gSrcInfer_principal_unique helse₁ helse₂
    rfl
  | .cond hni .., .condIsInstance .. =>
    absurd hni (by simp [GExpr.notIsInstance])
  | .condIsInstance .., .cond hni .. =>
    absurd hni (by simp [GExpr.notIsInstance])
  | .condIsInstance hlook₁ _ hthen₁ helse₁, .condIsInstance hlook₂ _ hthen₂ helse₂ => by
    rw [hlook₁] at hlook₂
    cases hlook₂
    obtain rfl := gSrcInfer_principal_unique hthen₁ hthen₂
    obtain rfl := gSrcInfer_principal_unique helse₁ helse₂
    rfl

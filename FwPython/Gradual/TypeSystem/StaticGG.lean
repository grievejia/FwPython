import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.Source.Precision
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.ProgramTargetPrecision
import FwPython.Gradual.TypeSystem.Checked.ShapePrecision
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision

/-! # Static gradual guarantee for the single-type pipeline -/

open Checked

private theorem approxTarget_irrelevant
    (G : GTy) :
    approxTarget gct₁ G = approxTarget gct₂ G := by
  induction G with
  | callable _ _ ihP ihR => simp [approxTarget, ihP, ihR]
  | union _ _ ihG ihH => simp [approxTarget, ihG, ihH]
  | _ => rfl

private theorem compileCheck_shapePrecision
    (scope₁ scope₂ : LabelScope)
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hΓ : SBindingEnvPrecision Γ₁ Γ₂)
    (h₁ : GSrcInfer gct₁ hwfct₁ Γ₁ e srcTy₁)
    (h₂ : GSrcInfer gct₂ hwfct₂ Γ₂ e srcTy₂)
    (Δ₁ Δ₂ : GTyEnv)
    (hP :
      CompileTargetPrecision
        (checkedTargetOfRuntimePublicTy P₁)
        (checkedTargetOfRuntimePublicTy P₂))
    (n₁ n₂ : Nat) :
    ShapeExprPrecision gct₁
      (eraseLabelsExpr (compileCheck scope₁ h₁ Δ₁ P₁ n₁).1)
      (eraseLabelsExpr (compileCheck scope₂ h₂ Δ₂ P₂ n₂).1) := by
  induction h₁ generalizing scope₁ scope₂ Γ₂ srcTy₂ Δ₁ Δ₂ P₁ P₂ n₁ n₂ with
  | var hlook₁ =>
      cases h₂ with
      | var hlook₂ =>
          simp [compileCheck, eraseLabelsExpr]
          exact .enforce .var hP
  | constNone =>
      cases h₂
      simp [compileCheck, eraseLabelsExpr]
      exact .enforce .constNone hP
  | constTrue =>
      cases h₂
      simp [compileCheck, eraseLabelsExpr]
      exact .enforce .constTrue hP
  | constFalse =>
      cases h₂
      simp [compileCheck, eraseLabelsExpr]
      exact .enforce .constFalse hP
  | new hfind₁ hbool₁ hnone₁ hbm₁ =>
      cases h₂ with
      | new hfind₂ hbool₂ hnone₂ hbm₂ =>
          simp [compileCheck, eraseLabelsExpr]
          exact .enforce .new hP
  | attrAccess hbase₁ hattr₁ ihBase =>
      cases h₂ with
      | attrAccess hbase₂ hattr₂ =>
          simp [compileCheck, eraseLabelsExpr]
          exact .enforce
            (.dynAttrAccess
              (ihBase scope₁ scope₂ hΓ hbase₂ Δ₁ Δ₂
                (by
                  simpa using
                    (compileTargetPrecision_refl
                      (checkedTargetOfRuntimePublicTy (.any : GTy))))
                n₁ n₂))
            hP
  | call hcallee₁ harg₁ hcallee_callable₁ hcallee_wf₁ harg_wf₁ hcall₁ ihCallee ihArg =>
      rename_i Γ₁' callee calleeSrcTy₁ arg argSrcTy₁ R₁
      cases h₂ with
      | call hcallee₂ harg₂ hcallee_callable₂ hcallee_wf₂ harg_wf₂ hcall₂ =>
          rename_i calleeSrcTy₂ argSrcTy₂
          let D₁ : GTy := callParamTarget gct₁ argSrcTy₁
          let D₂ : GTy := callParamTarget gct₂ argSrcTy₂
          have hDchecked :
              CompileTargetPrecision
                (callParamCheckedTarget gct₁ argSrcTy₁)
                (callParamCheckedTarget gct₂ argSrcTy₂) := by
            exact gSrcInfer_callParamCheckedTargetPrecision hct hΓ harg₁ harg₂
          have hCallablePrec :
              CompileTargetPrecision
                (checkedTargetOfRuntimePublicTy
                  (.callable (callParamTarget gct₁ argSrcTy₁) P₁))
                (checkedTargetOfRuntimePublicTy
                  (.callable (callParamTarget gct₂ argSrcTy₂) P₂)) := by
            simpa [callParamCheckedTarget] using
              (CompileTargetPrecision.callable hDchecked hP)
          simp [compileCheck, eraseLabelsExpr]
          exact .call
            (ihCallee scope₁ scope₂ hΓ hcallee₂ Δ₁ Δ₂ hCallablePrec n₁ n₂)
            (ihArg scope₁ scope₂ hΓ harg₂ Δ₁ Δ₂ hDchecked
              (compileCheck scope₁ hcallee₁ Δ₁ (.callable D₁ P₁) n₁).2
              (compileCheck scope₂ hcallee₂ Δ₂ (.callable D₂ P₂) n₂).2)
            hDchecked
            hP
  | cond hni₁ htest₁ hbool₁ hthen₁ helse₁ ihTest ihThen ihElse =>
      cases h₂ with
      | cond hni₂ htest₂ hbool₂ hthen₂ helse₂ =>
          simp [compileCheck, eraseLabelsExpr]
          exact .cond
            (ihTest scope₁ scope₂ hΓ htest₂ Δ₁ Δ₂
              (by
                simpa using
                  (compileTargetPrecision_refl
                    (checkedTargetOfRuntimePublicTy (.class_ boolClass : GTy))))
              n₁ n₂)
            (ihThen scope₁ scope₂ hΓ hthen₂ Δ₁ Δ₂ hP
              (compileCheck scope₁ htest₁ Δ₁ (.class_ boolClass) n₁).2
              (compileCheck scope₂ htest₂ Δ₂ (.class_ boolClass) n₂).2)
            (ihElse scope₁ scope₂ hΓ helse₂ Δ₁ Δ₂ hP
              (compileCheck scope₁ hthen₁ Δ₁ P₁
                (compileCheck scope₁ htest₁ Δ₁ (.class_ boolClass) n₁).2).2
              (compileCheck scope₂ hthen₂ Δ₂ P₂
                (compileCheck scope₂ htest₂ Δ₂ (.class_ boolClass) n₂).2).2)
      | condIsInstance => cases hni₁
  | isInstance hlook₁ hfind₁ =>
      cases h₂ with
      | isInstance hlook₂ hfind₂ =>
          simp [compileCheck, eraseLabelsExpr]
          exact .enforce .isInstance hP
  | condIsInstance hlook₁ hfind₁ hthen₁ helse₁ ihThen ihElse =>
      rename_i b₁ C cls₁ thenBranch thenSrcTy₁ elseBranch elseSrcTy₁ Γ₁' x
      cases h₂ with
      | cond hni₂ htest₂ hbool₂ hthen₂ helse₂ =>
          cases hni₂
      | condIsInstance hlook₂ hfind₂ hthen₂ helse₂ =>
          rename_i b₂ cls₂ thenSrcTy₂ elseSrcTy₂
          obtain ⟨b₂', hlook₂', hb⟩ := sBindingEnvPrecision_lookup hΓ hlook₁
          rw [hlook₂] at hlook₂'
          cases hlook₂'
          have hΓThen :
              SBindingEnvPrecision
                (SBindingEnv.updateSource Γ₁' x (.intersection b₁.sourceTy (.class_ C)))
                (SBindingEnv.updateSource Γ₂ x (.intersection b₂.sourceTy (.class_ C))) :=
            sBindingEnvPrecision_updateSource hΓ
              (show AnnotationTargetPrecision
                  (.intersection b₁.sourceTy (.class_ C))
                  (.intersection b₂.sourceTy (.class_ C)) from
                .intersection hb.source_prec .refl)
              (callParamCheckedTarget_intersection_class_right_congr
                (gct₁ := ([] : GClassTable))
                (gct₂ := ([] : GClassTable))
                (C := C)
                hb.source_callParam_prec)
          have hΓElse :
              SBindingEnvPrecision
                (SBindingEnv.updateSource Γ₁' x (.intersection b₁.sourceTy (.negClass C)))
                (SBindingEnv.updateSource Γ₂ x (.intersection b₂.sourceTy (.negClass C))) :=
            sBindingEnvPrecision_updateSource hΓ
              (show AnnotationTargetPrecision
                  (.intersection b₁.sourceTy (.negClass C))
                  (.intersection b₂.sourceTy (.negClass C)) from
                .intersection hb.source_prec .refl)
              (callParamCheckedTarget_intersection_negClass_right_congr
                (gct₁ := ([] : GClassTable))
                (gct₂ := ([] : GClassTable))
                (C := C)
                hb.source_callParam_prec)
          cases hΔ₁ : Δ₁.lookup x with
          | none =>
              cases hΔ₂ : Δ₂.lookup x with
              | none =>
                  simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂]
                  exact .cond .isInstance
                    (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁ Δ₂ hP n₁ n₂)
                    (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁ Δ₂ hP
                      (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                      (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)
              | some T₂ =>
                  by_cases href₂ : CheckedBranchRefineOk gct₂ T₂ C
                  · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₂]
                    exact .cond .isInstance
                      (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁
                        (Δ₂.update x (.intersection T₂ (.class_ C))) hP n₁ n₂)
                      (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁
                        (Δ₂.update x (.intersection T₂ (.negClass C))) hP
                        (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                        (compileCheck scope₂ hthen₂
                          (Δ₂.update x (.intersection T₂ (.class_ C))) P₂ n₂).2)
                  · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₂]
                    exact .cond .isInstance
                      (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁ Δ₂ hP n₁ n₂)
                      (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁ Δ₂ hP
                        (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                        (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)
          | some T₁ =>
              by_cases href₁ : CheckedBranchRefineOk gct₁ T₁ C
              · cases hΔ₂ : Δ₂.lookup x with
                | none =>
                    simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁]
                    exact .cond .isInstance
                      (ihThen scope₁ scope₂ hΓThen hthen₂
                        (Δ₁.update x (.intersection T₁ (.class_ C))) Δ₂ hP n₁ n₂)
                      (ihElse scope₁ scope₂ hΓElse helse₂
                        (Δ₁.update x (.intersection T₁ (.negClass C))) Δ₂ hP
                        (compileCheck scope₁ hthen₁
                          (Δ₁.update x (.intersection T₁ (.class_ C))) P₁ n₁).2
                        (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)
                | some T₂ =>
                    by_cases href₂ : CheckedBranchRefineOk gct₂ T₂ C
                    · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁, href₂]
                      exact .cond .isInstance
                        (ihThen scope₁ scope₂ hΓThen hthen₂
                          (Δ₁.update x (.intersection T₁ (.class_ C)))
                          (Δ₂.update x (.intersection T₂ (.class_ C))) hP n₁ n₂)
                        (ihElse scope₁ scope₂ hΓElse helse₂
                          (Δ₁.update x (.intersection T₁ (.negClass C)))
                          (Δ₂.update x (.intersection T₂ (.negClass C))) hP
                          (compileCheck scope₁ hthen₁
                            (Δ₁.update x (.intersection T₁ (.class_ C))) P₁ n₁).2
                          (compileCheck scope₂ hthen₂
                            (Δ₂.update x (.intersection T₂ (.class_ C))) P₂ n₂).2)
                    · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁, href₂]
                      exact .cond .isInstance
                        (ihThen scope₁ scope₂ hΓThen hthen₂
                          (Δ₁.update x (.intersection T₁ (.class_ C))) Δ₂ hP n₁ n₂)
                        (ihElse scope₁ scope₂ hΓElse helse₂
                          (Δ₁.update x (.intersection T₁ (.negClass C))) Δ₂ hP
                          (compileCheck scope₁ hthen₁
                            (Δ₁.update x (.intersection T₁ (.class_ C))) P₁ n₁).2
                          (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)
              · cases hΔ₂ : Δ₂.lookup x with
                | none =>
                    simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁]
                    exact .cond .isInstance
                      (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁ Δ₂ hP n₁ n₂)
                      (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁ Δ₂ hP
                        (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                        (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)
                | some T₂ =>
                    by_cases href₂ : CheckedBranchRefineOk gct₂ T₂ C
                    · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁, href₂]
                      exact .cond .isInstance
                        (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁
                          (Δ₂.update x (.intersection T₂ (.class_ C))) hP n₁ n₂)
                        (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁
                          (Δ₂.update x (.intersection T₂ (.negClass C))) hP
                          (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                          (compileCheck scope₂ hthen₂
                            (Δ₂.update x (.intersection T₂ (.class_ C))) P₂ n₂).2)
                    · simp [compileCheck, eraseLabelsExpr, hΔ₁, hΔ₂, href₁, href₂]
                      exact .cond .isInstance
                        (ihThen scope₁ scope₂ hΓThen hthen₂ Δ₁ Δ₂ hP n₁ n₂)
                        (ihElse scope₁ scope₂ hΓElse helse₂ Δ₁ Δ₂ hP
                          (compileCheck scope₁ hthen₁ Δ₁ P₁ n₁).2
                          (compileCheck scope₂ hthen₂ Δ₂ P₂ n₂).2)

private theorem compileCheck_fst_transport
    (scope : LabelScope)
    (he : e₁ = e₂)
    (hsrc : GSrcInfer gct hwfct Γ e₁ srcTy)
    (Δ : GTyEnv)
    (P : GTy)
    (n : Nat) :
    (compileCheck scope (he ▸ hsrc) Δ P n).1 = (compileCheck scope hsrc Δ P n).1 := by
  cases he
  rfl

private theorem compiledMethod_shapePrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hm : Checked.MethodTargetPrecision gm₁ gm₂)
    (hc₁ : IsCompiledMethodAt gct₁ cname gm₁ cm₁)
    (hc₂ : IsCompiledMethodAt gct₂ cname gm₂ cm₂) :
    ShapeMethodPrecision gct₁
      (eraseLabelsMethod cm₁)
      (eraseLabelsMethod cm₂) := by
  have hparam₁ : checkedTargetOfGTy gm₁.paramTy = cm₁.paramTy := by
    simpa using congrArg checkedTargetOfGTy hc₁.paramTy_eq.symm
  have hparam₂ : checkedTargetOfGTy gm₂.paramTy = cm₂.paramTy := by
    simpa using congrArg checkedTargetOfGTy hc₂.paramTy_eq.symm
  have hreturn₁ : checkedTargetOfGTy gm₁.returnTy = cm₁.returnTy := by
    simpa using congrArg checkedTargetOfGTy hc₁.returnTy_eq.symm
  have hreturn₂ : checkedTargetOfGTy gm₂.returnTy = cm₂.returnTy := by
    simpa using congrArg checkedTargetOfGTy hc₂.returnTy_eq.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc₁.name_eq.trans (hm.name_eq.trans hc₂.name_eq.symm)
  · exact hc₁.receiverParam_eq.trans (hm.receiver_eq.trans hc₂.receiverParam_eq.symm)
  · exact hc₁.param_eq.trans (hm.param_eq.trans hc₂.param_eq.symm)
  · simpa [eraseLabelsMethod] using (hparam₁ ▸ hparam₂ ▸ hm.paramTy_prec)
  · simpa [eraseLabelsMethod] using (hreturn₁ ▸ hreturn₂ ▸ hm.returnTy_prec)
  · obtain ⟨_, srcTy₁, hsrc₁, hbody₁⟩ := hc₁.body_compiled
    obtain ⟨hwfct₂, srcTy₂, hsrc₂_raw, hbody₂_raw⟩ := hc₂.body_compiled
    have hreturnPrec :
        CompileTargetPrecision
          (checkedTargetOfRuntimePublicTy gm₁.returnTy)
          (checkedTargetOfRuntimePublicTy gm₂.returnTy) :=
      compileTargetPrecision_of_checkedTargetPrecision
        (checkedTargetOfRuntimePublicTy_annotationTargetPrecision hm.returnTy_prec)
    let Δ₂ := [(gm₂.param, gm₂.paramTy), (gm₂.receiverParam, .class_ cname)]
    let hsrc₂ :
          GSrcInfer gct₂ hwfct₂
            [{ name := gm₂.param, sourceTy := gm₂.paramTy },
             { name := gm₂.receiverParam, sourceTy := .class_ cname }]
            gm₁.body srcTy₂ :=
      hm.body_eq.symm ▸ hsrc₂_raw
    have hbody₂ :
        cm₂.body =
          (compileCheck (.methodBody cname gm₂.name) hsrc₂ Δ₂ gm₂.returnTy 0).1 :=
      hbody₂_raw.trans <| by
        simpa [hsrc₂] using
          (compileCheck_fst_transport (.methodBody cname gm₂.name) (he := hm.body_eq.symm)
            (hsrc := hsrc₂_raw) (Δ := Δ₂) (P := gm₂.returnTy) (n := 0)).symm
    have hΓ :
        SBindingEnvPrecision
          [{ name := gm₁.param, sourceTy := gm₁.paramTy },
           { name := gm₁.receiverParam, sourceTy := .class_ cname }]
          [{ name := gm₂.param, sourceTy := gm₂.paramTy },
           { name := gm₂.receiverParam, sourceTy := .class_ cname }] :=
      .cons ⟨hm.param_eq, hm.paramTy_prec, by
        simpa [callParamCheckedTarget_eq_callParamAnnotationTarget] using
          hm.paramTy_callParam_prec⟩
        (.cons ⟨hm.receiver_eq, .refl, .refl⟩ .nil)
    simpa [eraseLabelsMethod, hbody₁, hbody₂] using
      compileCheck_shapePrecision
        (.methodBody cname gm₁.name) (.methodBody cname gm₂.name)
        hct hΓ hsrc₁ hsrc₂
        [(gm₁.param, gm₁.paramTy), (gm₁.receiverParam, .class_ cname)]
        Δ₂ hreturnPrec 0 0

private theorem compiledMethods_shapePrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hms : Forall₂ Checked.MethodTargetPrecision gms₁ gms₂)
    (hc₁ : Forall₂ (IsCompiledMethodAt gct₁ cname) gms₁ cms₁)
    (hc₂ : Forall₂ (IsCompiledMethodAt gct₂ cname) gms₂ cms₂) :
    Forall₂ (ShapeMethodPrecision gct₁)
      (cms₁.map eraseLabelsMethod)
      (cms₂.map eraseLabelsMethod) := by
  induction hms generalizing cms₁ cms₂ with
  | nil => cases hc₁; cases hc₂; exact .nil
  | cons hm_head _ ih =>
      cases hc₁ with | cons hc₁_head hc₁_tail =>
      cases hc₂ with | cons hc₂_head hc₂_tail =>
      exact .cons (compiledMethod_shapePrecision hct hm_head hc₁_head hc₂_head)
        (ih hc₁_tail hc₂_tail)

private theorem compiledClass_shapePrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hc : Checked.ClassTargetPrecision gc₁ gc₂)
    (cc₁_ok : IsCompiledClass gct₁ gc₁ cc₁)
    (cc₂_ok : IsCompiledClass gct₂ gc₂ cc₂) :
    ShapeClassPrecision gct₁
      (eraseLabelsClass cc₁)
      (eraseLabelsClass cc₂) := by
  have cc₂_methods_ok := hc.name_eq ▸ cc₂_ok.methods_compiled
  refine ⟨?_, ?_, ?_⟩
  · exact cc₁_ok.name_eq.trans (hc.name_eq.trans cc₂_ok.name_eq.symm)
  · exact cc₁_ok.baseClasses_eq.trans
      (hc.baseClasses_eq.trans cc₂_ok.baseClasses_eq.symm)
  · simpa [eraseLabelsClass] using
      compiledMethods_shapePrecision (cname := gc₁.name)
        hct hc.methods_prec cc₁_ok.methods_compiled cc₂_methods_ok

private theorem compiledClassTable_shapePrecision_aux
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (hgc : Forall₂ Checked.ClassTargetPrecision gclasses₁ gclasses₂)
    (cc₁_ok : Forall₂ (IsCompiledClass gct₁) gclasses₁ cclasses₁)
    (cc₂_ok : Forall₂ (IsCompiledClass gct₂) gclasses₂ cclasses₂) :
    Forall₂ (ShapeClassPrecision gct₁)
      (cclasses₁.map eraseLabelsClass)
      (cclasses₂.map eraseLabelsClass) := by
  induction hgc generalizing cclasses₁ cclasses₂ with
  | nil => cases cc₁_ok; cases cc₂_ok; exact .nil
  | cons hc _ ih =>
      cases cc₁_ok with | cons cc₁_head cc₁_tail =>
      cases cc₂_ok with | cons cc₂_head cc₂_tail =>
      exact .cons (compiledClass_shapePrecision hct hc cc₁_head cc₂_head)
        (ih cc₁_tail cc₂_tail)

private theorem compiledClassTable_shapePrecision
    (hct : Checked.ClassTableTargetPrecision gct₁ gct₂)
    (cc₁_ok : IsCompiledClassTable gct₁ cct₁)
    (cc₂_ok : IsCompiledClassTable gct₂ cct₂) :
    Forall₂ (ShapeClassPrecision gct₁)
      (cct₁.map eraseLabelsClass)
      (cct₂.map eraseLabelsClass) :=
  compiledClassTable_shapePrecision_aux hct hct cc₁_ok cc₂_ok

private theorem static_gradual_guarantee_shape
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    ShapeProgramPrecision gp₁.classes
      (eraseLabelsProgram cp₁)
      (eraseLabelsProgram cp₂) := by
  let hct : Checked.ClassTableTargetPrecision gp₁.classes gp₂.classes :=
    hgp.classes_prec
  have hP' :
      CompileTargetPrecision
        (checkedTargetOfRuntimePublicTy P₁)
        (checkedTargetOfRuntimePublicTy P₂) :=
    compileTargetPrecision_of_checkedTargetPrecision hP
  refine ⟨compiledClassTable_shapePrecision hct
            helab₁.classes_elab helab₂.classes_elab, ?_⟩
  let h2_hsrc : GSrcInfer gp₂.classes helab₂.hwfct [] gp₁.main helab₂.main_srcTy :=
    hgp.main_eq.symm ▸ helab₂.main_hsrc
  have h2_eq : cp₂.main = (compileCheck .main h2_hsrc [] P₂ 0).1 :=
    helab₂.main_eq.trans <| by
      simpa [h2_hsrc] using
        (compileCheck_fst_transport .main (he := hgp.main_eq.symm)
          (hsrc := helab₂.main_hsrc) (Δ := []) (P := P₂) (n := 0)).symm
  simpa [eraseLabelsProgram, helab₁.main_eq, h2_eq] using
    compileCheck_shapePrecision .main .main hct
      (.nil : SBindingEnvPrecision [] []) helab₁.main_hsrc h2_hsrc [] [] hP' 0 0

theorem static_gradual_guarantee
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    CheckedProgramPrecision gp₁.classes cp₁ cp₂ := by
  simpa [CheckedProgramPrecision] using
    static_gradual_guarantee_shape hgp helab₁ helab₂ hP

theorem static_gradual_guarantee_main_moreStatic
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    MoreStatic gp₂.classes helab₁.main_srcTy helab₂.main_srcTy ∧
    CheckedProgramPrecision gp₁.classes cp₁ cp₂ := by
  let hct : Checked.ClassTableTargetPrecision gp₁.classes gp₂.classes :=
    hgp.classes_prec
  let h2_hsrc : GSrcInfer gp₂.classes helab₂.hwfct [] gp₁.main helab₂.main_srcTy :=
    hgp.main_eq.symm ▸ helab₂.main_hsrc
  exact
    ⟨gSrcInfer_moreStatic hct
        (.nil : SBindingEnvPrecision [] [])
        helab₁.main_hsrc h2_hsrc,
      static_gradual_guarantee hgp helab₁ helab₂ hP⟩

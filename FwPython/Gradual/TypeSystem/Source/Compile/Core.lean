import FwPython.Gradual.TypeSystem.Source.Compile.Approx

/-! # Use-site elaboration core -/

private theorem gTyEnv_update_eq_self
    {Δ : GTyEnv} {x : Identifier} {T : GTy}
    (hlook : Δ.lookup x = some T) :
    Δ.update x T = Δ := by
  induction Δ with
  | nil =>
    simp [NamedEnv.lookup] at hlook
  | cons p rest ih =>
    by_cases hp : p.1 = x
    · subst hp
      cases p with
      | mk k v =>
        simp [GTyEnv.update, NamedEnv.update, NamedEnv.lookup] at hlook ⊢
        cases hlook
        rfl
    · cases p with
      | mk k v =>
        have hlookRest : NamedEnv.lookup rest x = some T := by
          simpa [NamedEnv.lookup, hp] using hlook
        have ih' := ih hlookRest
        simp [GTyEnv.update, NamedEnv.update, hp, ih']

theorem elabEnvOk_intersection_update_refine
    (R : GTy)
    (helab : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T)
    (hRchecked : RuntimePublicAnnotation gct (.intersection T R))
    (hRwf : WellFormedGTy gct (.intersection T R)) :
    ElabEnvOk gct
      (Γ.updateSource x (.intersection b.sourceTy R))
      (Δ.update x (.intersection T R)) := by
  obtain ⟨T', hlookΔ', _, _, hsub⟩ := elabEnvOk_lookup helab hlookΓ
  rw [hlookΔ] at hlookΔ'
  cases hlookΔ'
  exact elabEnvOk_updateBoth helab hlookΓ hlookΔ
    hRchecked hRwf
    (gradualSubtype_intersection_mono hsub (gradualSubtype_refl gct R))

theorem elabEnvOk_intersection_sourceOnly_refine
    (R : GTy)
    (helab : ElabEnvOk gct Γ Δ)
    (hlookΓ : Γ.lookupBinding x = some b)
    (hlookΔ : Δ.lookup x = some T) :
    ElabEnvOk gct
      (Γ.updateSource x (.intersection b.sourceTy R))
      Δ := by
  obtain ⟨T', hlookΔ', hcheckedT, hwfT, hsub⟩ := elabEnvOk_lookup helab hlookΓ
  rw [hlookΔ] at hlookΔ'
  cases hlookΔ'
  have helab' := elabEnvOk_updateBoth helab hlookΓ hlookΔ hcheckedT hwfT
    (gradualSubtype_trans
      (gradualSubtype_intersection_left gct b.sourceTy R)
      hsub)
  rw [gTyEnv_update_eq_self hlookΔ] at helab'
  exact helab'

def compileCheck :
    LabelScope →
    GSrcInfer gct hwfct Γ e srcTy →
    GTyEnv →
    GTy →
    Nat →
    CheckedExpr × Nat
  | scope, .var (x := x) _, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce (.var x) target labels, n')
  | scope, .constNone, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce .constNone target labels, n')
  | scope, .constTrue, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce .constTrue target labels, n')
  | scope, .constFalse, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce .constFalse target labels, n')
  | scope, .new (cname := cname) _ _ _ _, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce (.new cname) target labels, n')
  | scope, .attrAccess (attr := attr) hbase _, Δ, P, n =>
      let (base', n₁) := compileCheck scope hbase Δ .any n
      let (ℓ, n₂) := freshLabel scope .context n₁
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n₃) := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n₂
      (.enforce (.dynAttrAccess base' attr ℓ) target labels, n₃)
  | scope, .call (argSrcTy := argSrcTy) hcallee harg _ _ _ _, Δ, P, n =>
      let D := callParamTarget gct argSrcTy
      let paramTarget := callParamCheckedTarget gct argSrcTy
      let (callee', n₁) := compileCheck scope hcallee Δ (.callable D P) n
      let (arg', n₂) := compileCheck scope harg Δ D n₁
      let returnTarget := checkedTargetOfRuntimePublicTy P
      let (labels, n₃) :=
        mkBoundaryLabels scope .positive (compileBoundaryTarget returnTarget) n₂
      (.call callee' arg' paramTarget returnTarget labels, n₃)
  | scope, .cond _ htest _ hthen helse, Δ, P, n =>
      let (test', n₁) := compileCheck scope htest Δ (.class_ boolClass) n
      let (then', n₂) := compileCheck scope hthen Δ P n₁
      let (else', n₃) := compileCheck scope helse Δ P n₂
      (.cond test' then' else', n₃)
  | scope, .isInstance (x := x) (C := C) _ _, _, P, n =>
      let target := checkedTargetOfRuntimePublicTy P
      let (labels, n') := mkBoundaryLabels scope .positive (compileBoundaryTarget target) n
      (.enforce (.isInstance x C) target labels, n')
  | scope, .condIsInstance (x := x) (C := C) _ _ hthen helse, Δ, P, n =>
      match Δ.lookup x with
      | some T =>
          if CheckedBranchRefineOk gct T C then
            let (then', n₁) :=
              compileCheck scope hthen (Δ.update x (.intersection T (.class_ C))) P n
            let (else', n₂) :=
              compileCheck scope helse (Δ.update x (.intersection T (.negClass C))) P n₁
            (.cond (.isInstance x C) then' else', n₂)
          else
            let (then', n₁) := compileCheck scope hthen Δ P n
            let (else', n₂) := compileCheck scope helse Δ P n₁
            (.cond (.isInstance x C) then' else', n₂)
      | none =>
          let (then', n₁) := compileCheck scope hthen Δ P n
          let (else', n₂) := compileCheck scope helse Δ P n₁
          (.cond (.isInstance x C) then' else', n₂)

theorem compileCheck_checked
    (scope : LabelScope)
    (henv : SourceEnvOk gct Γ)
    (helab : ElabEnvOk gct Γ Δ)
    (hwfct : WellFormedGClassTableCore gct)
    (hPruntime : RuntimePublicAnnotation gct P)
    (hPwf : WellFormedGTy gct P)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    CheckedHasType gct Δ (compileCheck scope hsrc Δ P n).1 (runtimePublicTy P) := by
  induction hsrc generalizing scope Δ P n with
  | var hlook =>
    simp [compileCheck]
    obtain ⟨T, hlookΔ, _, _, _⟩ := elabEnvOk_lookup helab hlook
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        (.var hlookΔ)
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | constNone =>
    simp [compileCheck]
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        CheckedHasType.constNone
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | constTrue =>
    simp [compileCheck]
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        CheckedHasType.constTrue
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | constFalse =>
    simp [compileCheck]
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        CheckedHasType.constFalse
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | new hfind hbool hnone hbm =>
    simp [compileCheck]
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        (CheckedHasType.new hfind hbool hnone hbm)
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | attrAccess hbase hattr ih =>
    simp [compileCheck]
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        (CheckedHasType.dynAttrAccess
          (ih scope henv helab (runtimePublicAnnotation_mk (.classFormula .any)) .any))
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | call hcallee harg _ _ _ _ ihC ihA =>
    rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
    simp [compileCheck]
    let D : GTy := callParamTarget gct argSrcTy
    have hDruntime : RuntimePublicAnnotation gct D :=
      callParamTarget_checkedTarget (gct := gct) (argSrcTy := argSrcTy)
    have hDwF : WellFormedGTy gct D :=
      callParamTarget_wellFormed (gct := gct) (argSrcTy := argSrcTy) harg_wf
    have hCallableRuntime : RuntimePublicAnnotation gct (.callable D P) :=
      runtimePublicAnnotation_mk
        (.callable
          (runtimePublicAnnotation_checked hDruntime)
          (runtimePublicAnnotation_checked hPruntime))
    have hCallableWf : WellFormedGTy gct (.callable D P) := .callable hDwF hPwf
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.call
        (paramTy := callParamCheckedTarget gct argSrcTy)
        (returnTy := checkedTargetOfRuntimePublicTy P)
        (by
          simpa [D, interpTarget_callParamCheckedTarget,
            interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
            (ihC scope henv helab hCallableRuntime hCallableWf))
        (by
          simpa [D, runtimePublicTy_id] using
            (ihA scope henv helab hDruntime hDwF))
        (by
          simpa [D, interpTarget_callParamCheckedTarget] using
            (assignableTo_refl gct D))
        (callParamCheckedTarget_runtimePublic (gct := gct) (argSrcTy := argSrcTy))
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime))
        (by
          simpa [D, interpTarget_callParamCheckedTarget] using hDwF)
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
            wellFormedGTy_runtimePublicTy hPwf))
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
    simp [compileCheck]
    exact .cond
      (ihTest scope henv helab
        (runtimePublicAnnotation_mk (CheckedTargetTy.classFormula FormulaGTy.class_))
        (boolClass_wellFormed hwfct))
      (ihThen scope henv helab hPruntime hPwf)
      (ihElse scope henv helab hPruntime hPwf)
      (runtimePublicAnnotation_mk
        (checkedTargetTy_runtimePublicTy (runtimePublicAnnotation_checked hPruntime)))
  | isInstance hlook hfind =>
    simp [compileCheck]
    obtain ⟨T, hlookΔ, _, _, _⟩ := elabEnvOk_lookup helab hlook
    simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using
      (CheckedHasType.enforce
        (target := checkedTargetOfRuntimePublicTy P)
        (CheckedHasType.isInstance hlookΔ hfind)
        (by
          simpa [interpTarget_checkedTargetOfRuntimePublicTy] using
            wellFormedGTy_runtimePublicTy hPwf)
        (checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
          (runtimePublicAnnotation_checked hPruntime)))
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
    rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
    obtain ⟨T, hlookΔ, hTchecked, hTwf, hsub⟩ := elabEnvOk_lookup helab hlook
    rw [compileCheck, hlookΔ]
    have hb := sourceEnvOk_lookup henv hlook
    have hclassWf := classTy_wellFormed_of_findGClass hwfct hfind
    have henvThen :
        SourceEnvOk gct (Γ'.updateSource x (.intersection b.sourceTy (.class_ C))) :=
      sourceEnvOk_updateSource henv hlook
        (.intersection hb.1 .class_)
        (.intersection hb.2 hclassWf)
    let hmroC := (hwfct.raw.allMrosExist _ _ hfind).hmro
    have hnegClassWf : WellFormedGTy gct (.negClass C) := .negClass hfind hmroC
    have henvElse :
        SourceEnvOk gct
          (Γ'.updateSource x (.intersection b.sourceTy (.negClass C))) :=
      sourceEnvOk_updateSource henv hlook
        (.intersection hb.1 .negClass)
        (.intersection hb.2 hnegClassWf)
    by_cases href : CheckedBranchRefineOk gct T C
    · have helabThen :=
        elabEnvOk_intersection_update_refine (.class_ C) helab hlook hlookΔ
          href.1 (.intersection hTwf hclassWf)
      have helabElse :=
        elabEnvOk_intersection_update_refine (.negClass C) helab hlook hlookΔ
          href.2 (.intersection hTwf hnegClassWf)
      simp [href]
      exact .condIsInstance hlookΔ hfind
        (runtimePublicAnnotation_mk
          (checkedTargetTy_runtimePublicTy (runtimePublicAnnotation_checked hPruntime)))
        href.1 href.2
        (ihThen scope henvThen helabThen hPruntime hPwf)
        (ihElse scope henvElse helabElse hPruntime hPwf)
    · have helabThen := elabEnvOk_intersection_sourceOnly_refine (.class_ C) helab hlook hlookΔ
      have helabElse :=
        elabEnvOk_intersection_sourceOnly_refine (.negClass C) helab hlook hlookΔ
      simp [href]
      exact .cond
        (.isInstance hlookΔ hfind)
        (ihThen scope henvThen helabThen hPruntime hPwf)
        (ihElse scope henvElse helabElse hPruntime hPwf)
        (runtimePublicAnnotation_mk
          (checkedTargetTy_runtimePublicTy (runtimePublicAnnotation_checked hPruntime)))

theorem compileCheck_counter_monotone
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    n ≤ (compileCheck scope hsrc Δ P n).2 := by
  induction hsrc generalizing scope Δ P n with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      simp [compileCheck, mkBoundaryLabels_next]
  | attrAccess hbase _ ih =>
      simp [compileCheck, mkBoundaryLabels_next, freshLabel]
      have hbaseMono := ih (scope := scope) (Δ := Δ) (P := .any) (n := n)
      omega
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' callee calleeSrcTy arg argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      simp [compileCheck, mkBoundaryLabels_next]
      have hcalleeMono :=
        ihC (scope := scope) (Δ := Δ) (P := .callable D P) (n := n)
      have hcalleeMono' :
          n ≤ (compileCheck scope hcallee Δ (.callable (callParamTarget gct argSrcTy) P) n).2 := by
        simpa [D] using hcalleeMono
      have hargMono :=
        ihA (scope := scope)
          (Δ := Δ)
          (P := D)
          (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
      have hargMono' :
          (compileCheck scope hcallee Δ (.callable (callParamTarget gct argSrcTy) P) n).2 ≤
            (compileCheck scope harg Δ (callParamTarget gct argSrcTy)
              (compileCheck scope hcallee Δ (.callable (callParamTarget gct argSrcTy) P) n).2).2 := by
        simpa [D] using hargMono
      have hcount :
          0 < (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P)).labelCount := by
        simpa [compileBoundaryTarget_checkedTargetOfRuntimePublicTy, BoundaryContract.labelCount]
          using (show 0 < (compileBoundaryRaw (runtimePublicTy P)).labelCount by
            cases runtimePublicTy P <;>
              simp [compileBoundaryRaw, BoundaryContract.labelCount] <;> omega)
      omega
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      simp [compileCheck]
      have htestMono :
          n ≤ (compileCheck scope htest Δ (.class_ boolClass) n).2 :=
        ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n)
      have hthenMono :
          (compileCheck scope htest Δ (.class_ boolClass) n).2 ≤
            (compileCheck scope hthen Δ P
              (compileCheck scope htest Δ (.class_ boolClass) n).2).2 :=
        ihThen (scope := scope) (Δ := Δ) (P := P) (n := _)
      have helseMono :
          (compileCheck scope hthen Δ P
            (compileCheck scope htest Δ (.class_ boolClass) n).2).2 ≤
            (compileCheck scope helse Δ P
              (compileCheck scope hthen Δ P
                (compileCheck scope htest Δ (.class_ boolClass) n).2).2).2 :=
        ihElse (scope := scope) (Δ := Δ) (P := P) (n := _)
      omega
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          simp [compileCheck, hΔ]
          have hthenMono : n ≤ (compileCheck scope hthen Δ P n).2 :=
            ihThen (scope := scope) (Δ := Δ) (P := P) (n := n)
          have helseMono :
                (compileCheck scope hthen Δ P n).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P n).2).2 :=
              ihElse (scope := scope) (Δ := Δ) (P := P) (n := _)
          omega
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · simp [compileCheck, hΔ, href]
            have hthenMono :
                n ≤
                  (compileCheck scope hthen
                    (Δ.update x (.intersection T (.class_ C))) P n).2 :=
              ihThen
                (scope := scope)
                (Δ := Δ.update x (.intersection T (.class_ C)))
                (P := P)
                (n := n)
            have helseMono :
                (compileCheck scope hthen
                  (Δ.update x (.intersection T (.class_ C))) P n).2 ≤
                  (compileCheck scope helse
                    (Δ.update x (.intersection T (.negClass C))) P
                    (compileCheck scope hthen
                      (Δ.update x (.intersection T (.class_ C))) P n).2).2 :=
              ihElse
                (scope := scope)
                (Δ := Δ.update x (.intersection T (.negClass C)))
                (P := P)
                (n := _)
            omega
          · simp [compileCheck, hΔ, href]
            have hthenMono : n ≤ (compileCheck scope hthen Δ P n).2 :=
              ihThen (scope := scope) (Δ := Δ) (P := P) (n := n)
            have helseMono :
                (compileCheck scope hthen Δ P n).2 ≤
                  (compileCheck scope helse Δ P
                    (compileCheck scope hthen Δ P n).2).2 :=
              ihElse (scope := scope) (Δ := Δ) (P := P) (n := _)
            omega

theorem compileCheck_enforce_labels_form
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath e' c labels},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath = some (.enforce e' c labels) →
      ∃ k, labels = (mkBoundaryLabels scope .positive (compileBoundaryTarget c) k).1 := by
  intro Δ P n exprPath e' c labels
  induction hsrc generalizing scope Δ P n exprPath e' c labels with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
          rcases hnode with ⟨_, rfl, hlabels⟩
          cases hlabels
          exact ⟨n, rfl⟩
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          rcases hnode with ⟨_, rfl, hlabels⟩
          cases hlabels
          exact ⟨(compileCheck scope hbase Δ .any n).2 + 1, rfl⟩
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                simp [CheckedExpr.nodeAt] at hnode
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  exact ih (scope := scope) (Δ := Δ) (P := .any) (n := n) hnode
  | call hcallee harg _ _ _ _ ihC ihA =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            exact ihC (scope := scope) (Δ := Δ) (P := _) (n := n) hnode
          case callArg =>
            exact ihA (scope := scope) (Δ := Δ) (P := _) (n := _) hnode
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            exact ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) hnode
          case condThen =>
            exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
          case condElse =>
            exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
              · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.class_ C)))
                    (P := P)
                    (n := n)
                    hnode
                · exact ihElse
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.negClass C)))
                    (P := P)
                    (n := _)
                    hnode
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
                · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode

theorem compileCheck_dynAttr_label_form
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath e' attr ℓ},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath = some (.dynAttrAccess e' attr ℓ) →
      ∃ k, ℓ = (freshLabel scope .context k).1 := by
  intro Δ P n exprPath e' attr ℓ
  induction hsrc generalizing scope Δ P n exprPath e' attr ℓ with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                simp [CheckedExpr.nodeAt] at hnode
                rcases hnode with ⟨rfl, rfl, rfl⟩
                exact ⟨(compileCheck scope hbase Δ .any n).2, rfl⟩
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  exact ih (scope := scope) (Δ := Δ) (P := .any) (n := n) hnode
  | call hcallee harg _ _ _ _ ihC ihA =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            exact ihC (scope := scope) (Δ := Δ) (P := _) (n := n) hnode
          case callArg =>
            exact ihA (scope := scope) (Δ := Δ) (P := _) (n := _) hnode
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            exact ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) hnode
          case condThen =>
            exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
          case condElse =>
            exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
              · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.class_ C)))
                    (P := P)
                    (n := n)
                    hnode
                · exact ihElse
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.negClass C)))
                    (P := P)
                    (n := _)
                    hnode
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
                · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode

theorem compileCheck_call_return_labels_form
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    ∀ {Δ P n exprPath callee arg paramTy returnTy}
      {labels : BoundaryLabels (compileBoundaryTarget returnTy)},
      (compileCheck scope hsrc Δ P n).1.nodeAt exprPath =
        some (.call callee arg paramTy returnTy labels) →
      ∃ k,
        labels = (mkBoundaryLabels scope .positive
          (compileBoundaryTarget returnTy) k).1 := by
  intro Δ P n exprPath callee arg paramTy returnTy labels
  induction hsrc generalizing scope Δ P n exprPath callee arg paramTy returnTy labels with
  | var | constNone | constTrue | constFalse | new | isInstance =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case enforceBody =>
            cases rest <;> simp [CheckedExpr.nodeAt] at hnode
  | attrAccess hbase _ ih =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt, freshLabel] at hnode
          case enforceBody =>
            cases rest with
            | nil =>
                simp [CheckedExpr.nodeAt] at hnode
            | cons child' tail =>
                cases child' <;> simp [CheckedExpr.nodeAt] at hnode
                case dynAttrBase =>
                  exact ih (scope := scope) (Δ := Δ) (P := .any) (n := n) hnode
  | call hcallee harg _ _ _ _ ihC ihA =>
      rename_i Γ' calleeSrc calleeSrcTy argSrc argSrcTy R hcallee_callable hcallee_wf harg_wf hcall
      let D : GTy := callParamTarget gct argSrcTy
      cases exprPath with
      | nil =>
          intro hnode
          have hEq :
              CheckedExpr.call
                  (compileCheck scope hcallee Δ (.callable D P) n).1
                  (compileCheck scope harg Δ D
                    (compileCheck scope hcallee Δ (.callable D P) n).2).1
                  (callParamCheckedTarget gct argSrcTy)
                  (checkedTargetOfRuntimePublicTy P)
                  (mkBoundaryLabels scope .positive
                    (compileBoundaryTarget (checkedTargetOfRuntimePublicTy P))
                    (compileCheck scope harg Δ D
                      (compileCheck scope hcallee Δ (.callable D P) n).2).2).1 =
                CheckedExpr.call callee arg paramTy returnTy labels := by
            exact Option.some.inj (by
              simpa [CheckedExpr.nodeAt, compileCheck, D] using hnode)
          obtain ⟨hR, _, _, _, hlabels⟩ := checkedExpr_call_inversion hEq
          cases hR
          exact ⟨(compileCheck scope harg Δ D
              (compileCheck scope hcallee Δ (.callable D P) n).2).2,
            hlabels.symm⟩
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case callCallee =>
            exact ihC (scope := scope) (Δ := Δ) (P := .callable D P) (n := n) hnode
          case callArg =>
            exact ihA
              (scope := scope)
              (Δ := Δ)
              (P := D)
              (n := (compileCheck scope hcallee Δ (.callable D P) n).2)
              hnode
  | cond _ htest _ hthen helse ihTest ihThen ihElse =>
      cases exprPath with
      | nil =>
          intro hnode
          simp [compileCheck, CheckedExpr.nodeAt] at hnode
      | cons child rest =>
          intro hnode
          cases child <;> simp [compileCheck, CheckedExpr.nodeAt] at hnode
          case condTest =>
            exact ihTest (scope := scope) (Δ := Δ) (P := .class_ boolClass) (n := n) hnode
          case condThen =>
            exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
          case condElse =>
            exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
      rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
      cases hΔ : Δ.lookup x with
      | none =>
          cases exprPath with
          | nil =>
              intro hnode
              simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
          | cons child rest =>
              intro hnode
              cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ] at hnode
              · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
              · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
              · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode
      | some T =>
          by_cases href : CheckedBranchRefineOk gct T C
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.class_ C)))
                    (P := P)
                    (n := n)
                    hnode
                · exact ihElse
                    (scope := scope)
                    (Δ := Δ.update x (.intersection T (.negClass C)))
                    (P := P)
                    (n := _)
                    hnode
          · cases exprPath with
            | nil =>
                intro hnode
                simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
            | cons child rest =>
                intro hnode
                cases child <;> simp [compileCheck, CheckedExpr.nodeAt, hΔ, href] at hnode
                · cases rest <;> simp [CheckedExpr.nodeAt] at hnode
                · exact ihThen (scope := scope) (Δ := Δ) (P := P) (n := n) hnode
                · exact ihElse (scope := scope) (Δ := Δ) (P := P) (n := _) hnode

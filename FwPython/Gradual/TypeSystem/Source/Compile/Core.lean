import FwPython.Gradual.TypeSystem.Source.Compile.Approx
import FwPython.Gradual.TypeSystem.CallParamTarget
import FwPython.Gradual.Checked.Core
import FwPython.Gradual.TypeSystem.Checked.Typing
import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.SourceObligation

/-! # Use-site elaboration core -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

/-- Wrap a checked body with a boundary check that re-verifies the requested
gradual target `P` at the source expression site. Used by every `compileCheck`
arm whose root produces a boundary obligation (the leaves, `attrAccess`). -/
def compileEnforce
    (body : CheckedExpr)
    (P : GTy)
    (site : SourceExpressionSite) :
    CheckedExpr :=
  .enforce body (checkedTargetOfGTy P) (.hasType (.expression site) P)

/-- Checked environments for an `isInstance`-refined conditional. The first
component is the then-branch environment and the second component is the
else-branch environment. A bound checked variable is refined through
`isInstanceThenRefinement` and `isInstanceElseRefinement` exactly when both
computed branch targets are admissible. -/
def condIsInstanceBranchEnvironments
    (gct : GClassTable) (Delta : GTyEnv) (x C : Identifier) : GTyEnv × GTyEnv :=
  match Delta.lookup x with
  | some T =>
      if CheckedBranchRefineOk gct T C then
        (Delta.update x (isInstanceThenRefinement T C),
         Delta.update x (isInstanceElseRefinement T C))
      else (Delta, Delta)
  | none => (Delta, Delta)

private theorem compileEnforce_checked
    {body : CheckedExpr} {bodyTy P : GTy}
    (hbody : CheckedHasType gct structural Δ body bodyTy)
    (hPruntime : CheckedTargetTy gct P)
    (hPwf : WellFormedGTy gct P)
    (site : SourceExpressionSite) :
    CheckedHasType gct structural Δ
      (compileEnforce body P site) P := by
  simpa [compileEnforce] using
    CheckedHasType.enforce (target := checkedTargetOfGTy P) hbody
      (by simpa using hPwf) (by simpa using hPruntime)

/-- Compile a source typing derivation at a requested checked target and source
expression site. -/
def compileCheck :
    GSrcInfer gct hwfct Γ e srcTy →
    GTyEnv →
    GTy →
    SourceExpressionSite →
    CheckedExpr
  | .var (x := x) _, _, P, site =>
      compileEnforce (.var x) P site
  | .constNone, _, P, site =>
      compileEnforce .constNone P site
  | .constTrue, _, P, site =>
      compileEnforce .constTrue P site
  | .constFalse, _, P, site =>
      compileEnforce .constFalse P site
  | .new (cname := cname) _ _ _ _, _, P, site =>
      compileEnforce (.new cname) P site
  | .attrAccess (attr := attr) hbase _, Δ, P, site =>
      let base := compileCheck hbase Δ .any (site.child .attributeReceiver)
      compileEnforce (.dynAttrAccess base attr (.hasAttribute site attr)) P site
  | .call (argSrcTy := argSrcTy) hcallee harg _, Δ, P, site =>
      let D := callParamTarget argSrcTy
      let paramTarget := callParamCheckedTarget argSrcTy
      let callee := compileCheck hcallee Δ (.callable D P) (site.child .callCallee)
      let arg := compileCheck harg Δ D (site.child .callArgument)
      let returnTarget := checkedTargetOfGTy P
      .call callee arg paramTarget returnTarget (.hasType (.expression site) P)
  | .cond _ htest _ hthen helse, Δ, P, site =>
      .cond
        (compileCheck htest Δ (.class_ boolClass) (site.child .conditionTest))
        (compileCheck hthen Δ P (site.child .conditionThen))
        (compileCheck helse Δ P (site.child .conditionElse))
  | .isInstance (x := x) (C := C) _ _, _, P, site =>
      compileEnforce (.isInstance x C) P site
  | .condIsInstance (x := x) (C := C) _ _ hthen helse, Δ, P, site =>
      let branchEnvironments := condIsInstanceBranchEnvironments gct Δ x C
      .cond (.isInstance x C)
        (compileCheck hthen branchEnvironments.1 P (site.child .conditionThen))
        (compileCheck helse branchEnvironments.2 P (site.child .conditionElse))

/-- `compileCheck` is determined by the source expression, checked
environment, requested target, and source site. Different principal source
typing witnesses for the same expression compile to the same checked syntax. -/
theorem compileCheck_sourceCoherent
    (left :
      GSrcInfer gct hwfct Γ e leftSrcTy)
    (right :
      GSrcInfer gct hwfct Γ e rightSrcTy)
    (Delta : GTyEnv)
    (target : GTy)
    (site : SourceExpressionSite) :
    compileCheck left Delta target site =
      compileCheck right Delta target site := by
  induction left generalizing rightSrcTy Delta target site with
  | var _ =>
      cases right
      rfl
  | constNone =>
      cases right
      rfl
  | constTrue =>
      cases right
      rfl
  | constFalse =>
      cases right
      rfl
  | new _ _ _ _ =>
      cases right
      rfl
  | attrAccess _ _ ih =>
      cases right with
      | attrAccess hbase' _ =>
          simp [compileCheck, ih hbase']
  | call _ harg _ ihCallee ihArg =>
      cases right with
      | call hcallee' harg' _ =>
          obtain rfl := gSrcInfer_principal_unique harg harg'
          simp [compileCheck, ihCallee hcallee', ihArg harg']
  | cond hnotIsInstance _ _ _ _ ihTest ihThen ihElse =>
      cases right with
      | cond _ htest' _ hthen' helse' =>
          simp [compileCheck, ihTest htest', ihThen hthen', ihElse helse']
      | condIsInstance _ _ _ _ =>
          simp [GExpr.notIsInstance] at hnotIsInstance
  | isInstance _ _ =>
      cases right
      rfl
  | condIsInstance hlook _ _ _ ihThen ihElse =>
      cases right with
      | cond hnotIsInstance' _ _ _ _ =>
          simp [GExpr.notIsInstance] at hnotIsInstance'
      | condIsInstance hlook' _ hthen' helse' =>
          rw [hlook] at hlook'
          cases hlook'
          simp [compileCheck, ihThen hthen', ihElse helse']

/-- The compiled expression has the requested target type under a compatible checked environment.
The environment relation supplies source validity through its upper-bound subtype proofs. -/
theorem compileCheck_checked
    (hwfct : WellFormedGClassTableCore gct)
    (helab : ElabEnvOk gct hwfct.toWellFormedClassHierarchy Γ Δ)
    (hPruntime : CheckedTargetTy gct P)
    (hPwf : WellFormedGTy gct P)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy)
    (site : SourceExpressionSite) :
    CheckedHasType gct hwfct.toWellFormedClassHierarchy Δ (compileCheck hsrc Δ P site) P := by
  induction hsrc generalizing Δ P site with
  | var hlook =>
    obtain ⟨T, hlookΔ, _, _, _⟩ := elabEnvOk_lookup helab hlook
    exact compileEnforce_checked (.var hlookΔ) hPruntime hPwf site
  | constNone =>
    exact compileEnforce_checked CheckedHasType.constNone hPruntime hPwf site
  | constTrue =>
    exact compileEnforce_checked CheckedHasType.constTrue hPruntime hPwf site
  | constFalse =>
    exact compileEnforce_checked CheckedHasType.constFalse hPruntime hPwf site
  | new hfind hbool hnone hbm =>
    exact compileEnforce_checked
      (CheckedHasType.new hfind hbool hnone hbm) hPruntime hPwf site
  | attrAccess _ _ ih =>
    exact compileEnforce_checked
      (CheckedHasType.dynAttrAccess
        (ih helab (.classFormula .any) .any (site.child .attributeReceiver)))
      hPruntime hPwf site
  | call _ _ hcall ihC ihA =>
    rename_i argSrcTy _ _ _
    have harg_wf := callSourceTy?_argumentWellFormed hwfct hcall
    let D : GTy := callParamTarget argSrcTy
    have hDruntime : CheckedTargetTy gct D :=
      callParamTarget_checkedTarget (gct := gct) (argSrcTy := argSrcTy)
    have hDwF : WellFormedGTy gct D :=
      callParamTarget_wellFormed (gct := gct) (argSrcTy := argSrcTy) harg_wf
    have hCallableRuntime : CheckedTargetTy gct (.callable D P) :=
      .callable hDruntime hPruntime
    have hCallableWf : WellFormedGTy gct (.callable D P) := .callable hDwF hPwf
    simpa using
      (CheckedHasType.call
        (paramTy := callParamCheckedTarget argSrcTy)
        (returnTy := checkedTargetOfGTy P)
        (by
          simpa [D, interpTarget_callParamCheckedTarget] using
            (ihC helab hCallableRuntime hCallableWf (site.child .callCallee)))
        (by
          simpa [D] using
            (ihA helab hDruntime hDwF (site.child .callArgument)))
        (by
          simpa [D, interpTarget_callParamCheckedTarget] using
            (assignableTo_refl gct hwfct.toWellFormedClassHierarchy D hDwF))
        (by simpa [interpTarget_callParamCheckedTarget] using hDruntime)
        (by simpa using hPruntime)
        (by
          simpa [D, interpTarget_callParamCheckedTarget] using hDwF)
        (by simpa using hPwf))
  | cond _ _ _ _ _ ihTest ihThen ihElse =>
    exact .cond
      (ihTest helab
        (CheckedTargetTy.classFormula FormulaGTy.class_)
        (boolClass_wellFormed hwfct)
        (site.child .conditionTest))
      (ihThen helab hPruntime hPwf (site.child .conditionThen))
      (ihElse helab hPruntime hPwf (site.child .conditionElse))
      hPruntime
  | isInstance hlook hfind =>
    obtain ⟨T, hlookΔ, _, _, _⟩ := elabEnvOk_lookup helab hlook
    exact compileEnforce_checked
      (CheckedHasType.isInstance hlookΔ hfind) hPruntime hPwf site
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
    rename_i b C _ _ _ _ _ Γ' x _ _
    obtain ⟨T, hlookΔ, hTchecked, hTwf, hsub⟩ := elabEnvOk_lookup helab hlook
    have hb := (wellFormedGTy_of_boundsNamesKnown hwfct.raw b.sourceTy).2 hsub.sourceWellFormed
    have hclassWf := classTy_wellFormed_of_findGClass hwfct hfind
    by_cases href : CheckedBranchRefineOk gct T C
    · have hcheckedThenEnv :=
        elabEnvOk_updateBoth helab hlook hlookΔ
          href.1 (wellFormedGTy_isInstanceThenRefinement hTwf hclassWf)
          (isInstanceThenRefinement_mono hsub hclassWf)
      have hcheckedElseEnv :=
        elabEnvOk_updateBoth helab hlook hlookΔ
          href.2 (wellFormedGTy_isInstanceElseRefinement hTwf hclassWf)
          (isInstanceElseRefinement_mono hsub hclassWf)
      simpa [compileCheck, condIsInstanceBranchEnvironments, hlookΔ, href] using
        CheckedHasType.condIsInstance hlookΔ hfind
        hPruntime
        href.1 href.2
        (ihThen hcheckedThenEnv hPruntime hPwf (site.child .conditionThen))
        (ihElse hcheckedElseEnv hPruntime hPwf (site.child .conditionElse))
    · have hcheckedThenEnv :
          ElabEnvOk gct hwfct.toWellFormedClassHierarchy
            (Γ'.updateSource x (isInstanceThenRefinement b.sourceTy C)) Δ := by
        have helab' :=
          elabEnvOk_updateBoth helab hlook hlookΔ hTchecked hTwf
            (gradualSubtype_trans
              (isInstanceThenRefinement_subtype_self gct hwfct.toWellFormedClassHierarchy b.sourceTy C
                hb hclassWf)
              hsub)
        simpa [namedEnv_update_eq_self hlookΔ] using helab'
      have hcheckedElseEnv :
          ElabEnvOk gct hwfct.toWellFormedClassHierarchy
            (Γ'.updateSource x (isInstanceElseRefinement b.sourceTy C)) Δ := by
        have helab' :=
          elabEnvOk_updateBoth helab hlook hlookΔ hTchecked hTwf
            (gradualSubtype_trans
              (isInstanceElseRefinement_subtype_self gct hwfct.toWellFormedClassHierarchy b.sourceTy C
                hb hclassWf)
              hsub)
        simpa [namedEnv_update_eq_self hlookΔ] using helab'
      simpa [compileCheck, condIsInstanceBranchEnvironments, hlookΔ, href] using
        CheckedHasType.cond
        (.isInstance hlookΔ hfind)
        (ihThen hcheckedThenEnv hPruntime hPwf (site.child .conditionThen))
        (ihElse hcheckedElseEnv hPruntime hPwf (site.child .conditionElse))
        hPruntime

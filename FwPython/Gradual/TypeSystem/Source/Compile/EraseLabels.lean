import FwPython.Gradual.TypeSystem.Source.Compile.Core

/-! # Label erasure for `compileCheck` -/

private def compileCheckShape :
    GSrcInfer gct hwfct Γ e srcTy →
    GTy →
    ShapeExpr
  | .var (x := x) _, P =>
      .enforce (.var x) (checkedTargetOfRuntimePublicTy P)
  | .constNone, P =>
      .enforce .constNone (checkedTargetOfRuntimePublicTy P)
  | .constTrue, P =>
      .enforce .constTrue (checkedTargetOfRuntimePublicTy P)
  | .constFalse, P =>
      .enforce .constFalse (checkedTargetOfRuntimePublicTy P)
  | .new (cname := cname) _ _ _ _, P =>
      .enforce (.new cname) (checkedTargetOfRuntimePublicTy P)
  | .attrAccess (attr := attr) hbase _, P =>
      .enforce (.dynAttrAccess (compileCheckShape hbase .any) attr)
        (checkedTargetOfRuntimePublicTy P)
  | .call (argSrcTy := argSrcTy) hcallee harg _ _ _ _, P =>
      let D := callParamTarget gct argSrcTy
      .call
        (compileCheckShape hcallee (.callable D P))
        (compileCheckShape harg D)
        (callParamCheckedTarget gct argSrcTy)
        (checkedTargetOfRuntimePublicTy P)
  | .cond _ htest _ hthen helse, P =>
      .cond
        (compileCheckShape htest (.class_ boolClass))
        (compileCheckShape hthen P)
        (compileCheckShape helse P)
  | .isInstance (x := x) (C := C) _ _, P =>
      .enforce (.isInstance x C) (checkedTargetOfRuntimePublicTy P)
  | .condIsInstance (x := x) (C := C) _ _ hthen helse, P =>
      .cond
        (.isInstance x C)
        (compileCheckShape hthen P)
        (compileCheckShape helse P)

private theorem compileCheck_eraseLabels
    (scope : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    eraseLabelsExpr (compileCheck scope hsrc Δ P n).1 = compileCheckShape hsrc P := by
  induction hsrc generalizing Δ P n with
  | var | constNone | constTrue | constFalse | new | isInstance =>
    simp [compileCheck, compileCheckShape, eraseLabelsExpr]
  | attrAccess _ _ ih =>
    simp [compileCheck, compileCheckShape, eraseLabelsExpr, ih]
  | call _ _ _ _ _ _ ihC ihA =>
    simp [compileCheck, compileCheckShape, eraseLabelsExpr, ihC, ihA]
  | cond _ _ _ _ _ ihTest ihThen ihElse =>
    simp [compileCheck, compileCheckShape, eraseLabelsExpr, ihTest, ihThen, ihElse]
  | condIsInstance hlook hfind hthen helse ihThen ihElse =>
    rename_i b C cls thenBranch thenSrcTy elseBranch elseSrcTy Γ' x
    cases hΔ : Δ.lookup x with
    | none =>
      simp [compileCheck, compileCheckShape, eraseLabelsExpr, hΔ, ihThen, ihElse]
    | some T =>
      by_cases href : CheckedBranchRefineOk gct T C <;>
        simp [compileCheck, compileCheckShape, eraseLabelsExpr, hΔ, href, ihThen, ihElse]

theorem compileCheck_eraseLabels_congr
    (scope₁ scope₂ : LabelScope)
    (hsrc : GSrcInfer gct hwfct Γ e srcTy) :
    eraseLabelsExpr (compileCheck scope₁ hsrc Δ1 P n1).1 =
      eraseLabelsExpr (compileCheck scope₂ hsrc Δ2 P n2).1 :=
  (compileCheck_eraseLabels scope₁ hsrc).trans (compileCheck_eraseLabels scope₂ hsrc).symm

import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.TypeSystem.Source.Core

/-! # Gradual source typing

Source inference assigns one type to each expression. Calls use `callSourceTy?`
to decide acceptance and compute the result type. -/

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
  /-- Infer a call result from its function and argument source types.
  Acceptance establishes the validity of the argument annotation. -/
  | call :
      GSrcInfer gct hwfct Γ callee calleeSrcTy →
      GSrcInfer gct hwfct Γ arg argSrcTy →
      (hcall :
        callSourceTy? gct calleeSrcTy argSrcTy hwfct = some R) →
      GSrcInfer gct hwfct Γ (.call callee arg) R
  | cond :
      condExpr.notIsInstance →
      GSrcInfer gct hwfct Γ condExpr testSrcTy →
      AssignableTo gct hwfct.toWellFormedClassHierarchy testSrcTy (.class_ boolClass) →
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
        (Γ.updateSource x (isInstanceThenRefinement b.sourceTy C))
        thenBranch thenSrcTy →
      GSrcInfer gct hwfct
        (Γ.updateSource x (isInstanceElseRefinement b.sourceTy C))
        elseBranch elseSrcTy →
      GSrcInfer gct hwfct Γ
        (.cond (.isInstance x C) thenBranch elseBranch)
        (.union thenSrcTy elseSrcTy)

/-- Inference in a valid source environment produces a valid type. -/
theorem gSrcInfer_sourceWellFormed
    (henv : ∀ b ∈ Γ, WellFormedGTy gct b.sourceTy)
    (hinfer : GSrcInfer gct hwfct Γ e srcTy) :
    WellFormedGTy gct srcTy := by
  have lookupValid {environment : SBindingEnv} {name : Identifier} {binding : SBinding}
      (valid : ∀ b ∈ environment, WellFormedGTy gct b.sourceTy)
      (found : environment.lookupBinding name = some binding) :
      WellFormedGTy gct binding.sourceTy := by
    induction environment with
    | nil => simp [SBindingEnv.lookupBinding] at found
    | cons head _ ih =>
        by_cases same : head.name = name
        · simp [SBindingEnv.lookupBinding, same] at found
          cases found
          exact valid _ (.head _)
        · exact ih (fun b member => valid b (.tail _ member))
            (by simpa [SBindingEnv.lookupBinding, same] using found)
  have updated {environment : SBindingEnv} {name : Identifier} {newType : GTy}
      (environmentValid : ∀ b ∈ environment, WellFormedGTy gct b.sourceTy)
      (valid : WellFormedGTy gct newType) :
      ∀ b ∈ environment.updateSource name newType, WellFormedGTy gct b.sourceTy := by
    intro binding member
    induction environment with
    | nil => cases member
    | cons head _ ih =>
        by_cases same : head.name = name
        · simp only [SBindingEnv.updateSource, same, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | member
          · exact valid
          · exact environmentValid _ (.tail _ member)
        · simp only [SBindingEnv.updateSource, same, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | member
          · exact environmentValid _ (.head _)
          · exact ih (fun b member => environmentValid b (.tail _ member)) member
  induction hinfer with
  | var hlook =>
      exact lookupValid henv hlook
  | constNone =>
      exact .class_ hwfct.raw.noneExists.hfind hwfct.raw.noneExists.hmro
  | constTrue | constFalse | isInstance _ _ =>
      exact .class_ hwfct.raw.boolExists.hfind hwfct.raw.boolExists.hmro
  | new hfind _ _ _ =>
      exact .class_ hfind (hwfct.raw.allMrosExist _ _ hfind).hmro
  | attrAccess _ hattr _ =>
      exact attrSourceTy?_wellFormed hwfct hattr
  | call _ _ hcall _ _ =>
      exact callSourceTy?_wellFormed hwfct hcall
  | cond _ _ _ _ _ _ ihThen ihElse =>
      exact .union (ihThen henv) (ihElse henv)
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
      have bindingValid := lookupValid henv hlook
      let mro := (hwfct.raw.allMrosExist _ _ hfind).hmro
      exact .union
        (ihThen (updated henv
          (wellFormedGTy_isInstanceThenRefinement bindingValid (.class_ hfind mro))))
        (ihElse (updated henv
          (wellFormedGTy_isInstanceElseRefinement bindingValid (.class_ hfind mro))))

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
  | .call hcallee₁ harg₁ hcall₁,
    .call hcallee₂ harg₂ hcall₂ => by
    obtain rfl := gSrcInfer_principal_unique hcallee₁ hcallee₂
    obtain rfl := gSrcInfer_principal_unique harg₁ harg₂
    rw [hcall₁] at hcall₂
    cases hcall₂
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

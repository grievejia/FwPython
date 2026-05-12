import FwPython.Gradual.TypeSystem.Source.Typing
import FwPython.Gradual.Checked.Core
import FwPython.Gradual.TypeSystem.Checked.Typing
import FwPython.Gradual.TypeSystem.Checked.ShapePrecision
import FwPython.Gradual.TypeSystem.CallParamTarget
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision
import FwPython.Gradual.TypeSystem.CheckedTargetSemantics

/-! # Use-site elaboration for the single-type source front end -/

def approxFormula : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable _ _ => .any
  | .union G H => .union (approxFormula G) (approxFormula H)
  | .intersection G H => .intersection (approxFormula G) (approxFormula H)

def approxTarget (gct : GClassTable) : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable P R => .callable (approxTarget gct P) (approxTarget gct R)
  | .union G H => .union (approxTarget gct G) (approxTarget gct H)
  | .intersection G H => approxFormula (.intersection G H)

private def normalizeCallParamUnion (left right : GTy) : GTy :=
  match left, right with
  | .any, _ => .any
  | _, .any => .any
  | _, _ => .union left right

private abbrev checkedTargetCmp : CheckedTarget → CheckedTarget → Ordering :=
  Checked.checkedTargetCmp

private abbrev normalizeCallParamCheckedIntersection
    (left right : CheckedTarget) : CheckedTarget :=
  Checked.normalizeCallParamAnnotationIntersection left right

private def normalizeCallParamIntersection (left right : GTy) : GTy :=
  match left, right with
  | .any, G => G
  | G, .any => G
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | G, H =>
      if G = H then G
      else if checkedTargetCmp
          (checkedTargetOfRuntimePublicTy G)
          (checkedTargetOfRuntimePublicTy H) = .gt then
        .intersection H G
      else
        .intersection G H

def callParamTarget (gct : GClassTable) : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable _ _ => .any
  | .union G H =>
      normalizeCallParamUnion
        (callParamTarget gct G)
        (callParamTarget gct H)
  | .intersection G H =>
      normalizeCallParamIntersection
        (callParamTarget gct G)
        (callParamTarget gct H)

def CheckedBranchRefineOk (gct : GClassTable) (T : GTy) (C : Identifier) : Prop :=
  RuntimePublicAnnotation gct (.intersection T (.class_ C)) ∧
  RuntimePublicAnnotation gct (.intersection T (.negClass C))

instance checkedBranchRefineOk_decidable
    (gct : GClassTable) (T : GTy) (C : Identifier) :
    Decidable (CheckedBranchRefineOk gct T C) := by
  dsimp [CheckedBranchRefineOk]
  infer_instance

theorem checkedBranchRefineOk_gPrecision
    (hprec : AnnotationTargetPrecision T₁ T₂)
    (href : CheckedBranchRefineOk gct T₁ C) :
    CheckedBranchRefineOk gct T₂ C := by
  constructor
  · exact runtimePublicAnnotation_mk
      (checkedTargetTy_annotationPrecision
        (G₁ := .intersection T₁ (.class_ C))
        (G₂ := .intersection T₂ (.class_ C))
        (.intersection hprec .refl)
        (runtimePublicAnnotation_checked href.1))
  · exact runtimePublicAnnotation_mk
      (checkedTargetTy_annotationPrecision
        (G₁ := .intersection T₁ (.negClass C))
        (G₂ := .intersection T₂ (.negClass C))
        (.intersection hprec .refl)
        (runtimePublicAnnotation_checked href.2))

theorem classTy_wellFormed_of_findGClass
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : findGClass gct C = some cls) :
    WellFormedGTy gct (.class_ C) := by
  exact .class_ hfind (hwfct.raw.allMrosExist _ _ hfind).hmro

theorem negClassTy_wellFormed_of_findGClass
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : findGClass gct C = some cls) :
    WellFormedGTy gct (.negClass C) := by
  exact .negClass hfind (hwfct.raw.allMrosExist _ _ hfind).hmro

theorem boolClass_wellFormed
    (hwfct : WellFormedGClassTableCore gct) :
    WellFormedGTy gct (.class_ boolClass) := by
  exact .class_ hwfct.raw.boolExists.hfind hwfct.raw.boolExists.hmro

theorem approxFormula_formula :
    FormulaGTy (approxFormula G) := by
  induction G with
  | any => exact .any
  | class_ => exact .class_
  | callable _ _ => exact .any
  | union _ _ ihG ihH => exact .union ihG ihH
  | intersection _ _ ihG ihH => exact .intersection ihG ihH
  | bottom => exact .bottom
  | negClass _ => exact .negClass

theorem approxFormula_wellFormed
    (hwf : WellFormedGTy gct G) :
    WellFormedGTy gct (approxFormula G) := by
  induction hwf with
  | any => exact .any
  | bottom => exact .bottom
  | class_ hfind hmro => exact .class_ hfind hmro
  | callable _ _ => exact .any
  | union _ _ ihG ihH => exact .union ihG ihH
  | intersection _ _ ihG ihH => exact .intersection ihG ihH
  | negClass hfind hmro => exact .negClass hfind hmro

private def approxFormulaCheckedTarget : CheckedTarget → CheckedTarget
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable _ _ => .any
  | .union G H => .union (approxFormulaCheckedTarget G) (approxFormulaCheckedTarget H)
  | .intersection G H =>
      .intersection (approxFormulaCheckedTarget G) (approxFormulaCheckedTarget H)

@[simp] private theorem approxFormulaCheckedTarget_checkedTargetOfGTy
    (G : GTy) :
    approxFormulaCheckedTarget (checkedTargetOfGTy G) =
      checkedTargetOfGTy (approxFormula G) := by
  induction G <;> simp [approxFormulaCheckedTarget, approxFormula, checkedTargetOfGTy, *]

private theorem approxFormulaCheckedTarget_precision
    (h : CheckedTargetPrecision T₁ T₂) :
    CheckedTargetPrecision
      (approxFormulaCheckedTarget T₁)
      (approxFormulaCheckedTarget T₂) := by
  induction h with
  | refl =>
      exact .refl
  | toAny =>
      exact .toAny
  | callable =>
      exact .refl
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ ihG ihH =>
      exact .intersection ihG ihH

theorem approxFormula_precision
    (h : AnnotationTargetPrecision G₁ G₂) :
    AnnotationTargetPrecision (approxFormula G₁) (approxFormula G₂) := by
  simpa [AnnotationTargetPrecision] using
    (approxFormulaCheckedTarget_precision
      (T₁ := checkedTargetOfGTy G₁)
      (T₂ := checkedTargetOfGTy G₂)
      h)

theorem approxTarget_checkedTarget :
    RuntimePublicAnnotation gct (approxTarget gct G) := by
  induction G with
  | any => exact runtimePublicAnnotation_mk (.classFormula .any)
  | class_ => exact runtimePublicAnnotation_mk (.classFormula .class_)
  | bottom => exact runtimePublicAnnotation_mk (.classFormula .bottom)
  | negClass _ => exact runtimePublicAnnotation_mk (.classFormula .negClass)
  | callable _ _ ihP ihR =>
      exact runtimePublicAnnotation_mk
        (.callable (runtimePublicAnnotation_checked ihP) (runtimePublicAnnotation_checked ihR))
  | union _ _ ihG ihH =>
      exact runtimePublicAnnotation_mk
        (.union (runtimePublicAnnotation_checked ihG) (runtimePublicAnnotation_checked ihH))
  | intersection _ _ _ _ =>
      exact runtimePublicAnnotation_mk (.classFormula approxFormula_formula)

theorem approxTarget_wellFormed
    (hwf : WellFormedGTy gct G) :
    WellFormedGTy gct (approxTarget gct G) := by
  induction hwf with
  | any => exact .any
  | bottom => exact .bottom
  | class_ hfind hmro => exact .class_ hfind hmro
  | negClass hfind hmro => exact .negClass hfind hmro
  | callable _ _ ihP ihR => exact .callable ihP ihR
  | union _ _ ihG ihH => exact .union ihG ihH
  | intersection hwfG hwfH _ _ =>
    exact .intersection (approxFormula_wellFormed hwfG) (approxFormula_wellFormed hwfH)

private def approxTargetCheckedTarget (gct : GClassTable) : CheckedTarget → CheckedTarget
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable P R =>
      .callable (approxTargetCheckedTarget gct P) (approxTargetCheckedTarget gct R)
  | .union G H =>
      .union (approxTargetCheckedTarget gct G) (approxTargetCheckedTarget gct H)
  | .intersection G H =>
      approxFormulaCheckedTarget (.intersection G H)

@[simp] private theorem approxTargetCheckedTarget_checkedTargetOfGTy
    (gct : GClassTable) (G : GTy) :
    approxTargetCheckedTarget gct (checkedTargetOfGTy G) =
      checkedTargetOfGTy (approxTarget gct G) := by
  induction G with
  | any =>
      rfl
  | class_ =>
      rfl
  | bottom =>
      rfl
  | negClass =>
      rfl
  | callable _ _ ihP ihR =>
      simp [approxTargetCheckedTarget, approxTarget, checkedTargetOfGTy, ihP, ihR]
  | union _ _ ihG ihH =>
      simp [approxTargetCheckedTarget, approxTarget, checkedTargetOfGTy, ihG, ihH]
  | intersection G H =>
      simp [approxTargetCheckedTarget, approxTarget, checkedTargetOfGTy,
        approxFormula, approxFormulaCheckedTarget,
        approxFormulaCheckedTarget_checkedTargetOfGTy (G := G),
        approxFormulaCheckedTarget_checkedTargetOfGTy (G := H)]

private theorem approxTargetCheckedTarget_precision
    (gct : GClassTable)
    (h : CheckedTargetPrecision T₁ T₂) :
    CheckedTargetPrecision
      (approxTargetCheckedTarget gct T₁)
      (approxTargetCheckedTarget gct T₂) := by
  induction h with
  | refl =>
      exact .refl
  | toAny =>
      exact .toAny
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection hG hH =>
      simpa [approxTargetCheckedTarget] using
        approxFormulaCheckedTarget_precision
          (T₁ := .intersection _ _)
          (T₂ := .intersection _ _)
          (CheckedTargetPrecision.intersection hG hH)

theorem approxTarget_precision
    (h : AnnotationTargetPrecision G₁ G₂) :
    AnnotationTargetPrecision (approxTarget gct G₁) (approxTarget gct G₂) := by
  simpa [AnnotationTargetPrecision] using
    (approxTargetCheckedTarget_precision
      (gct := gct)
      (T₁ := checkedTargetOfGTy G₁)
      (T₂ := checkedTargetOfGTy G₂)
      h)

def CallParamTargetNormalForm : GTy → Prop
  | .any => True
  | .class_ _ => True
  | .bottom => True
  | .negClass _ => True
  | .callable _ _ => False
  | .union G H =>
      CallParamTargetNormalForm G ∧
      CallParamTargetNormalForm H ∧
      G ≠ .any ∧
      H ≠ .any
  | .intersection G H =>
      CallParamTargetNormalForm G ∧
      CallParamTargetNormalForm H ∧
      G ≠ .any ∧
      H ≠ .any ∧
      G ≠ .bottom ∧
      H ≠ .bottom ∧
      G ≠ H ∧
      normalizeCallParamIntersection G H = .intersection G H

def CallParamCheckedTargetNormalForm : CheckedTarget → Prop
  | .any => True
  | .class_ _ => True
  | .bottom => True
  | .negClass _ => True
  | .callable _ _ => False
  | .union G H =>
      CallParamCheckedTargetNormalForm G ∧
      CallParamCheckedTargetNormalForm H ∧
      G ≠ .any ∧
      H ≠ .any
  | .intersection G H =>
      CallParamCheckedTargetNormalForm G ∧
      CallParamCheckedTargetNormalForm H ∧
      G ≠ .any ∧
      H ≠ .any ∧
      G ≠ .bottom ∧
      H ≠ .bottom ∧
      G ≠ H ∧
      normalizeCallParamCheckedIntersection G H = .intersection G H

private theorem normalizeCallParamUnion_formula
    (hLeft : FormulaGTy left)
    (hRight : FormulaGTy right) :
    FormulaGTy (normalizeCallParamUnion left right) := by
  by_cases hleft : left = .any
  · subst hleft
    exact .any
  · by_cases hright : right = .any
    · subst hright
      cases left <;> exact .any
    · simpa [normalizeCallParamUnion, hleft, hright] using
        FormulaGTy.union hLeft hRight

private theorem normalizeCallParamIntersection_formula
    (hLeft : FormulaGTy left)
    (hRight : FormulaGTy right) :
    FormulaGTy (normalizeCallParamIntersection left right) := by
  by_cases hleftAny : left = .any
  · subst hleftAny
    simp [normalizeCallParamIntersection] at hRight ⊢
    exact hRight
  · by_cases hrightAny : right = .any
    · subst hrightAny
      simp [normalizeCallParamIntersection] at hLeft ⊢
      exact hLeft
    · by_cases hleftBottom : left = .bottom
      · subst hleftBottom
        cases right <;> exact .bottom
      · by_cases hrightBottom : right = .bottom
        · subst hrightBottom
          cases left <;> exact .bottom
        · by_cases hEq : left = right
          · subst hEq
            simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
              hleftBottom, hrightBottom] using hLeft
          · by_cases hOrd :
              Checked.checkedTargetCmp
                  (checkedTargetOfRuntimePublicTy left)
                  (checkedTargetOfRuntimePublicTy right) = .gt
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                FormulaGTy.intersection hRight hLeft
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                FormulaGTy.intersection hLeft hRight

private theorem normalizeCallParamUnion_wellFormed
    (hwfLeft : WellFormedGTy gct left)
    (hwfRight : WellFormedGTy gct right) :
    WellFormedGTy gct (normalizeCallParamUnion left right) := by
  by_cases hleft : left = .any
  · subst hleft
    exact .any
  · by_cases hright : right = .any
    · subst hright
      cases left <;> exact .any
    · simpa [normalizeCallParamUnion, hleft, hright] using
        WellFormedGTy.union hwfLeft hwfRight

private theorem normalizeCallParamIntersection_wellFormed
    (hwfLeft : WellFormedGTy gct left)
    (hwfRight : WellFormedGTy gct right) :
    WellFormedGTy gct (normalizeCallParamIntersection left right) := by
  by_cases hleftAny : left = .any
  · subst hleftAny
    simp [normalizeCallParamIntersection] at hwfRight ⊢
    exact hwfRight
  · by_cases hrightAny : right = .any
    · subst hrightAny
      simp [normalizeCallParamIntersection] at hwfLeft ⊢
      exact hwfLeft
    · by_cases hleftBottom : left = .bottom
      · subst hleftBottom
        cases right <;> exact .bottom
      · by_cases hrightBottom : right = .bottom
        · subst hrightBottom
          cases left <;> exact .bottom
        · by_cases hEq : left = right
          · subst hEq
            simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
              hleftBottom, hrightBottom] using hwfLeft
          · by_cases hOrd :
              Checked.checkedTargetCmp
                  (checkedTargetOfRuntimePublicTy left)
                  (checkedTargetOfRuntimePublicTy right) = .gt
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                WellFormedGTy.intersection hwfRight hwfLeft
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                WellFormedGTy.intersection hwfLeft hwfRight

private theorem normalizeCallParamUnion_normalForm
    (hLeft : CallParamTargetNormalForm left)
    (hRight : CallParamTargetNormalForm right) :
    CallParamTargetNormalForm (normalizeCallParamUnion left right) := by
  by_cases hleft : left = .any
  · subst hleft
    simp [CallParamTargetNormalForm, normalizeCallParamUnion]
  · by_cases hright : right = .any
    · subst hright
      simp [CallParamTargetNormalForm, normalizeCallParamUnion]
    · simpa [CallParamTargetNormalForm, normalizeCallParamUnion, hleft, hright] using
        And.intro hLeft <| And.intro hRight <| And.intro hleft hright

private theorem normalizeCallParamIntersection_normalForm
    (hLeft : CallParamTargetNormalForm left)
    (hRight : CallParamTargetNormalForm right) :
    CallParamTargetNormalForm (normalizeCallParamIntersection left right) := by
  by_cases hleftAny : left = .any
  · subst hleftAny
    simpa [CallParamTargetNormalForm, normalizeCallParamIntersection] using hRight
  · by_cases hrightAny : right = .any
    · subst hrightAny
      simpa [CallParamTargetNormalForm, normalizeCallParamIntersection] using hLeft
    · by_cases hleftBottom : left = .bottom
      · subst hleftBottom
        simp [CallParamTargetNormalForm, normalizeCallParamIntersection]
      · by_cases hrightBottom : right = .bottom
        · subst hrightBottom
          simp [CallParamTargetNormalForm, normalizeCallParamIntersection]
        · by_cases hEq : left = right
          · subst hEq
            simpa [CallParamTargetNormalForm, normalizeCallParamIntersection,
              hleftAny, hrightAny, hleftBottom, hrightBottom] using hLeft
          · by_cases hOrd :
              Checked.checkedTargetCmp
                  (checkedTargetOfRuntimePublicTy left)
                  (checkedTargetOfRuntimePublicTy right) = .gt
            · have hSwap :
                  normalizeCallParamIntersection left right =
                    .intersection right left := by
                simp [normalizeCallParamIntersection, hEq, hOrd]
              rw [hSwap]
              refine ⟨hRight, hLeft, hrightAny, hleftAny, hrightBottom, hleftBottom, ?_, ?_⟩
              · simpa [eq_comm] using hEq
              · have hOrd' :
                    Checked.checkedTargetCmp
                        (checkedTargetOfRuntimePublicTy right)
                        (checkedTargetOfRuntimePublicTy left) = .lt :=
                  Checked.checkedTargetCmp_lt_of_gt hOrd
                simp [normalizeCallParamIntersection,
                  show right ≠ left by simpa [eq_comm] using hEq,
                  hOrd']
            · have hKeep :
                  normalizeCallParamIntersection left right =
                    .intersection left right := by
                simp [normalizeCallParamIntersection, hEq, hOrd]
              rw [hKeep]
              refine ⟨hLeft, hRight, hleftAny, hrightAny, hleftBottom, hrightBottom, hEq, ?_⟩
              simp [normalizeCallParamIntersection, hEq, hOrd]

theorem callParamTarget_formula
    (gct : GClassTable) (G : GTy) :
    FormulaGTy (callParamTarget gct G) := by
  induction G with
  | any =>
      exact .any
  | class_ =>
      exact .class_
  | bottom =>
      exact .bottom
  | negClass =>
      exact .negClass
  | callable _ _ =>
      exact .any
  | union _ _ ihG ihH =>
      exact normalizeCallParamUnion_formula ihG ihH
  | intersection _ _ ihG ihH =>
      exact normalizeCallParamIntersection_formula ihG ihH

theorem callParamTarget_checkedTarget :
    RuntimePublicAnnotation gct (callParamTarget gct argSrcTy) :=
  runtimePublicAnnotation_mk (.classFormula (callParamTarget_formula gct argSrcTy))

theorem callParamTarget_wellFormed
    (hwf : WellFormedGTy gct argSrcTy) :
    WellFormedGTy gct (callParamTarget gct argSrcTy) := by
  induction hwf with
  | any =>
      exact .any
  | bottom =>
      exact .bottom
  | class_ hfind hmro =>
      exact .class_ hfind hmro
  | negClass hfind hmro =>
      exact .negClass hfind hmro
  | callable _ _ =>
      exact .any
  | union _ _ ihG ihH =>
      exact normalizeCallParamUnion_wellFormed ihG ihH
  | intersection _ _ ihG ihH =>
      exact normalizeCallParamIntersection_wellFormed ihG ihH

theorem callParamTarget_normalForm
    (gct : GClassTable) (G : GTy) :
    CallParamTargetNormalForm (callParamTarget gct G) := by
  induction G with
  | any =>
      simp [CallParamTargetNormalForm, callParamTarget]
  | class_ =>
      simp [CallParamTargetNormalForm, callParamTarget]
  | bottom =>
      simp [CallParamTargetNormalForm, callParamTarget]
  | negClass =>
      simp [CallParamTargetNormalForm, callParamTarget]
  | callable _ _ =>
      simp [CallParamTargetNormalForm, callParamTarget]
  | union _ _ ihG ihH =>
      exact normalizeCallParamUnion_normalForm ihG ihH
  | intersection _ _ ihG ihH =>
      exact normalizeCallParamIntersection_normalForm ihG ihH

theorem callParamTarget_eq_self_of_normalForm
    (gct : GClassTable) (T : GTy)
    (h : CallParamTargetNormalForm T) :
    callParamTarget gct T = T := by
  cases T with
  | any | class_ | bottom | negClass =>
      rfl
  | callable =>
      cases h
  | union G H =>
      rcases h with ⟨hG, hH, hGne, hHne⟩
      change
        normalizeCallParamUnion
          (callParamTarget gct G)
          (callParamTarget gct H) =
        G.union H
      rw [callParamTarget_eq_self_of_normalForm gct G hG,
        callParamTarget_eq_self_of_normalForm gct H hH]
      simp [normalizeCallParamUnion]
  | intersection G H =>
      rcases h with
        ⟨hG, hH, hGneAny, hHneAny, hGneBottom, hHneBottom, hNe, hNorm⟩
      change
        normalizeCallParamIntersection
          (callParamTarget gct G)
          (callParamTarget gct H) =
        G.intersection H
      rw [callParamTarget_eq_self_of_normalForm gct G hG,
        callParamTarget_eq_self_of_normalForm gct H hH]
      simpa using hNorm

theorem callParamTarget_union_any_left
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.union .any G) = .any := by
  rfl

theorem callParamTarget_union_any_right
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.union G .any) = .any := by
  cases h : callParamTarget gct G <;> simp [callParamTarget, normalizeCallParamUnion, h]

theorem callParamTarget_intersection_any_left
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.intersection .any G) = callParamTarget gct G := by
  rfl

theorem callParamTarget_intersection_any_right
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.intersection G .any) = callParamTarget gct G := by
  cases h : callParamTarget gct G <;> simp [callParamTarget, normalizeCallParamIntersection, h]

theorem callParamTarget_intersection_bottom_left
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.intersection .bottom G) = .bottom := by
  cases h : callParamTarget gct G <;> simp [callParamTarget, normalizeCallParamIntersection, h]

theorem callParamTarget_intersection_bottom_right
    (gct : GClassTable) (G : GTy) :
    callParamTarget gct (.intersection G .bottom) = .bottom := by
  cases h : callParamTarget gct G <;> simp [callParamTarget, normalizeCallParamIntersection, h]

theorem callParamTarget_intersection_diag
    (gct : GClassTable) (X : GTy) :
    callParamTarget gct (.intersection X X) = callParamTarget gct X := by
  cases h : callParamTarget gct X <;> simp [callParamTarget, normalizeCallParamIntersection, h]

theorem callParamTarget_irrelevant
    (gct₁ gct₂ : GClassTable) (G : GTy) :
    callParamTarget gct₁ G = callParamTarget gct₂ G := by
  induction G with
  | callable _ _ =>
      rfl
  | union _ _ ihG ihH =>
      simp [callParamTarget, ihG, ihH]
  | intersection _ _ ihG ihH =>
      simp [callParamTarget, ihG, ihH]
  | _ =>
      rfl

/-- Checked-target version of `approxTarget`, normalized through the explicit
checked-target interface used by the runtime/compiler rewrite. -/
def approxCheckedTarget (gct : GClassTable) (G : GTy) : CheckedTarget :=
  checkedTargetOfRuntimePublicTy (approxTarget gct G)

@[simp] theorem interpTarget_approxCheckedTarget
    (gct : GClassTable) (G : GTy) :
    interpTarget (approxCheckedTarget gct G) = approxTarget gct G := by
  simp [approxCheckedTarget, runtimePublicTy_id]

@[simp] theorem compileBoundaryTarget_approxCheckedTarget
    (gct : GClassTable) (G : GTy) :
    compileBoundaryTarget (approxCheckedTarget gct G) =
      compileBoundaryRaw (approxTarget gct G) := by
  rw [compileBoundaryTarget_eq_compileBoundaryRaw_interp, interpTarget_approxCheckedTarget]

theorem approxCheckedTarget_runtimePublic
    (gct : GClassTable) (G : GTy) :
    RuntimePublicCheckedTarget gct (approxCheckedTarget gct G) := by
  exact checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
    (runtimePublicAnnotation_checked
      (approxTarget_checkedTarget (gct := gct) (G := G)))

theorem checkedTargetOfRuntimePublicTy_annotationTargetPrecision
    (h : AnnotationTargetPrecision G₁ G₂) :
    CheckedTargetPrecision
      (checkedTargetOfRuntimePublicTy G₁)
      (checkedTargetOfRuntimePublicTy G₂) := by
  simpa [AnnotationTargetPrecision, checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using h

theorem approxCheckedTarget_precision
    (gct : GClassTable)
    (h : AnnotationTargetPrecision G₁ G₂) :
    CheckedTargetPrecision
      (approxCheckedTarget gct G₁)
      (approxCheckedTarget gct G₂) := by
  unfold approxCheckedTarget
  exact checkedTargetOfRuntimePublicTy_annotationTargetPrecision
    (approxTarget_precision (gct := gct) h)

@[simp] theorem checkedTargetOfRuntimePublicTy_any :
    checkedTargetOfRuntimePublicTy .any = .any := by
  rfl

@[simp] theorem checkedTargetOfRuntimePublicTy_bottom :
    checkedTargetOfRuntimePublicTy .bottom = .bottom := by
  rfl

@[simp] theorem checkedTargetOfRuntimePublicTy_union
    (G H : GTy) :
    checkedTargetOfRuntimePublicTy (.union G H) =
      .union
        (checkedTargetOfRuntimePublicTy G)
        (checkedTargetOfRuntimePublicTy H) := by
  rfl

@[simp] theorem checkedTargetOfRuntimePublicTy_intersection
    (G H : GTy) :
    checkedTargetOfRuntimePublicTy (.intersection G H) =
      .intersection
        (checkedTargetOfRuntimePublicTy G)
        (checkedTargetOfRuntimePublicTy H) := by
  rfl

private theorem checkedTargetOfRuntimePublicTy_injective :
    Function.Injective checkedTargetOfRuntimePublicTy := by
  intro G H hEq
  have hInterp := congrArg interpTarget hEq
  simpa [interpTarget_checkedTargetOfRuntimePublicTy, runtimePublicTy_id] using hInterp

private theorem checkedTargetOfGTy_injective :
    Function.Injective checkedTargetOfGTy := by
  intro G H hEq
  have hInterp := congrArg interpTarget hEq
  simpa using hInterp

private theorem checkedTargetOfGTy_eq_iff
    (G H : GTy) :
    checkedTargetOfGTy G = checkedTargetOfGTy H ↔
      G = H := by
  constructor
  · intro hEq
    exact checkedTargetOfGTy_injective hEq
  · intro hEq
    simp [hEq]

private theorem checkedTargetOfGTy_runtimePublic_eq_iff
    (G H : GTy) :
    checkedTargetOfGTy (runtimePublicTy G) =
      checkedTargetOfGTy (runtimePublicTy H) ↔
      G = H := by
  constructor
  · intro hEq
    apply checkedTargetOfGTy_injective
    simpa [runtimePublicTy_id] using hEq
  · intro hEq
    simp [hEq]

private theorem checkedTargetOfGTy_if
    (p : Prop) [Decidable p] (G H : GTy) :
    checkedTargetOfGTy (if p then G else H) =
      if p then checkedTargetOfGTy G else checkedTargetOfGTy H := by
  by_cases hp : p <;> simp [hp]

theorem callParamCheckedTargetNormalForm_of_callParamTargetNormalForm
    (h : CallParamTargetNormalForm T) :
    CallParamCheckedTargetNormalForm (checkedTargetOfRuntimePublicTy T) := by
  cases T with
  | any =>
      trivial
  | class_ =>
      trivial
  | bottom =>
      trivial
  | negClass =>
      trivial
  | callable =>
      cases h
  | union G H =>
      rcases h with ⟨hG, hH, hGne, hHne⟩
      refine ⟨
        callParamCheckedTargetNormalForm_of_callParamTargetNormalForm hG,
        callParamCheckedTargetNormalForm_of_callParamTargetNormalForm hH,
        ?_, ?_⟩
      · intro hEq
        apply hGne
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · intro hEq
        apply hHne
        exact checkedTargetOfRuntimePublicTy_injective hEq
  | intersection G H =>
      rcases h with
        ⟨hG, hH, hGneAny, hHneAny, hGneBottom, hHneBottom, hNe, hNorm⟩
      refine ⟨
        callParamCheckedTargetNormalForm_of_callParamTargetNormalForm hG,
        callParamCheckedTargetNormalForm_of_callParamTargetNormalForm hH,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hEq
        apply hGneAny
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · intro hEq
        apply hHneAny
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · intro hEq
        apply hGneBottom
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · intro hEq
        apply hHneBottom
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · intro hEq
        apply hNe
        exact checkedTargetOfRuntimePublicTy_injective hEq
      · have hNeChecked :
            checkedTargetOfRuntimePublicTy G ≠ checkedTargetOfRuntimePublicTy H := by
          intro hEq
          exact hNe (checkedTargetOfRuntimePublicTy_injective hEq)
        have hNotGt :
            ¬ Checked.checkedTargetCmp
                (checkedTargetOfRuntimePublicTy G)
                (checkedTargetOfRuntimePublicTy H) = .gt := by
          intro hOrd
          have hSwap : (.intersection H G : GTy) = .intersection G H := by
            simp [normalizeCallParamIntersection, hNe, hOrd] at hNorm
          cases hSwap
          exact hNe rfl
        dsimp [normalizeCallParamCheckedIntersection,
          Checked.normalizeCallParamAnnotationIntersection]
        by_cases hEqChecked : checkedTargetOfRuntimePublicTy G = checkedTargetOfRuntimePublicTy H
        · exact False.elim (hNeChecked hEqChecked)
        · by_cases hCmp :
              Checked.checkedTargetCmp
                  (checkedTargetOfRuntimePublicTy G)
                  (checkedTargetOfRuntimePublicTy H) = .gt
          · exact False.elim (hNotGt hCmp)
          · have hEqChecked' :
                ¬ checkedTargetOfGTy (runtimePublicTy G) =
                  checkedTargetOfGTy (runtimePublicTy H) := by
              simpa [checkedTargetOfRuntimePublicTy] using hEqChecked
            have hCmp' :
                ¬ Checked.checkedTargetCmp
                    (checkedTargetOfGTy (runtimePublicTy G))
                    (checkedTargetOfGTy (runtimePublicTy H)) = .gt := by
              simpa [checkedTargetOfRuntimePublicTy] using hCmp
            rw [if_neg hEqChecked', if_neg hCmp']

/-- Checked-target version of `callParamTarget`. -/
def callParamCheckedTarget (gct : GClassTable) (argSrcTy : GTy) : CheckedTarget :=
  checkedTargetOfRuntimePublicTy (callParamTarget gct argSrcTy)

theorem callParamCheckedTarget_irrelevant
    (gct₁ gct₂ : GClassTable) (G : GTy) :
    callParamCheckedTarget gct₁ G =
      callParamCheckedTarget gct₂ G := by
  simpa [callParamCheckedTarget] using
    congrArg checkedTargetOfRuntimePublicTy
      (callParamTarget_irrelevant gct₁ gct₂ G)

@[simp] theorem interpTarget_callParamCheckedTarget
    (gct : GClassTable) (argSrcTy : GTy) :
    interpTarget (callParamCheckedTarget gct argSrcTy) =
      callParamTarget gct argSrcTy := by
  simp [callParamCheckedTarget, runtimePublicTy_id]

@[simp] theorem compileBoundaryTarget_callParamCheckedTarget
    (gct : GClassTable) (argSrcTy : GTy) :
    compileBoundaryTarget (callParamCheckedTarget gct argSrcTy) =
      compileBoundaryRaw (callParamTarget gct argSrcTy) := by
  simp [callParamCheckedTarget, runtimePublicTy_id]

theorem callParamCheckedTarget_runtimePublic
    (gct : GClassTable) (argSrcTy : GTy) :
    RuntimePublicCheckedTarget gct (callParamCheckedTarget gct argSrcTy) := by
  exact checkedTargetOfRuntimePublicTy_runtimePublic_of_checked
    (runtimePublicAnnotation_checked
      (callParamTarget_checkedTarget (gct := gct) (argSrcTy := argSrcTy)))

theorem callParamCheckedTarget_normalForm
    (gct : GClassTable) (G : GTy) :
    CallParamCheckedTargetNormalForm (callParamCheckedTarget gct G) :=
  callParamCheckedTargetNormalForm_of_callParamTargetNormalForm
    (callParamTarget_normalForm gct G)

theorem callParamCheckedTarget_union_any_left
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.union .any G) = .any := by
  simp [callParamCheckedTarget, callParamTarget_union_any_left]

theorem callParamCheckedTarget_union_any_right
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.union G .any) = .any := by
  simp [callParamCheckedTarget, callParamTarget_union_any_right]

theorem callParamCheckedTarget_intersection_any_left
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.intersection .any G) =
      callParamCheckedTarget gct G := by
  simp [callParamCheckedTarget, callParamTarget_intersection_any_left]

theorem callParamCheckedTarget_intersection_any_right
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.intersection G .any) =
      callParamCheckedTarget gct G := by
  simp [callParamCheckedTarget, callParamTarget_intersection_any_right]

theorem callParamCheckedTarget_intersection_bottom_left
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.intersection .bottom G) = .bottom := by
  simp [callParamCheckedTarget, callParamTarget_intersection_bottom_left]

theorem callParamCheckedTarget_intersection_bottom_right
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct (.intersection G .bottom) = .bottom := by
  simp [callParamCheckedTarget, callParamTarget_intersection_bottom_right]

theorem callParamCheckedTarget_intersection_diag
    (gct : GClassTable) (X : GTy) :
    callParamCheckedTarget gct (.intersection X X) =
      callParamCheckedTarget gct X := by
  simp [callParamCheckedTarget, callParamTarget_intersection_diag]

theorem callParamCheckedTarget_intersection_left_of_callParamTarget_any
    (gct : GClassTable) (G H : GTy)
    (hany : callParamTarget gct G = .any) :
    callParamCheckedTarget gct (.intersection G H) =
      callParamCheckedTarget gct H := by
  simp [callParamCheckedTarget, callParamTarget, normalizeCallParamIntersection, hany]

theorem callParamCheckedTarget_intersection_right_of_callParamTarget_any
    (gct : GClassTable) (G H : GTy)
    (hany : callParamTarget gct H = .any) :
    callParamCheckedTarget gct (.intersection G H) =
      callParamCheckedTarget gct G := by
  unfold callParamCheckedTarget
  rw [show callParamTarget gct (.intersection G H) =
      callParamTarget gct (.intersection G .any) by
        simp [callParamTarget, normalizeCallParamIntersection, hany]]
  exact congrArg checkedTargetOfRuntimePublicTy
    (callParamTarget_intersection_any_right gct G)

theorem callParamCheckedTarget_intersection_of_callParamTarget_eq
    (gct : GClassTable) (G H : GTy)
    (hEq : callParamTarget gct G = callParamTarget gct H) :
    callParamCheckedTarget gct (.intersection G H) =
      callParamCheckedTarget gct G := by
  unfold callParamCheckedTarget
  rw [show callParamTarget gct (.intersection G H) =
      callParamTarget gct (.intersection H H) by
        simp [callParamTarget, normalizeCallParamIntersection, hEq]]
  simpa [hEq] using callParamCheckedTarget_intersection_diag gct H

theorem callParamCheckedTarget_intersection_of_uncollapsed
    (gct : GClassTable) (G H : GTy)
    (hGAny : callParamTarget gct G ≠ .any)
    (hHAny : callParamTarget gct H ≠ .any)
    (hGBottom : callParamTarget gct G ≠ .bottom)
    (hHBottom : callParamTarget gct H ≠ .bottom)
    (hNe : callParamTarget gct G ≠ callParamTarget gct H) :
    callParamCheckedTarget gct (.intersection G H) =
      Checked.normalizeCallParamAnnotationIntersection
        (callParamCheckedTarget gct G)
        (callParamCheckedTarget gct H) := by
  have hNeChecked :
      callParamCheckedTarget gct G ≠ callParamCheckedTarget gct H := by
    intro hEq
    apply hNe
    exact checkedTargetOfRuntimePublicTy_injective hEq
  by_cases hOrd :
      Checked.checkedTargetCmp
          (checkedTargetOfRuntimePublicTy (callParamTarget gct G))
          (checkedTargetOfRuntimePublicTy (callParamTarget gct H)) = .gt
  · unfold Checked.normalizeCallParamAnnotationIntersection
    simp [callParamCheckedTarget, callParamTarget, normalizeCallParamIntersection,
      hNe, hOrd]
    intro hEq
    exact False.elim (hNeChecked hEq)
  · unfold Checked.normalizeCallParamAnnotationIntersection
    simp [callParamCheckedTarget, callParamTarget, normalizeCallParamIntersection,
      hNe, hOrd]
    intro hEq
    exact False.elim (hNeChecked hEq)

theorem callParamTarget_toAny
    (gct : GClassTable) (G : GTy) :
    AnnotationTargetPrecision (callParamTarget gct G) .any := by
  simpa [AnnotationTargetPrecision] using
    (CheckedTargetPrecision.toAny
      (T := checkedTargetOfGTy (callParamTarget gct G)))

theorem callParamCheckedTarget_toAny
    (gct : GClassTable) (G : GTy) :
    CompileTargetPrecision
      (callParamCheckedTarget gct G)
      (callParamCheckedTarget gct .any) := by
  simpa [callParamCheckedTarget] using
    (CompileTargetPrecision.toAny (T := callParamCheckedTarget gct G))

theorem compileTargetPrecision_any_left_inversion
    (h : CompileTargetPrecision .any T)
    (hnf : CallParamCheckedTargetNormalForm T) :
    T = .any := by
  cases h with
  | refl =>
      rfl
  | toAny =>
      rfl
  | meet hLeft hRight =>
      rcases hnf with ⟨hLeftNf, hRightNf, hLeftNotAny, hRightNotAny, _, _, hNe, _⟩
      have hLeftEq : _ = CheckedTarget.any :=
        compileTargetPrecision_any_left_inversion hLeft hLeftNf
      have hRightEq : _ = CheckedTarget.any :=
        compileTargetPrecision_any_left_inversion hRight hRightNf
      subst hLeftEq
      subst hRightEq
      contradiction

theorem annotationTargetPrecision_eq_bottom_of_right
    (h : AnnotationTargetPrecision G₁ G₂)
    (hbottom : G₂ = .bottom) :
    G₁ = .bottom := by
  subst hbottom
  cases G₁ <;> cases h <;> rfl

private theorem callParamCheckedTarget_eq_bottom_of_compileTargetPrecision_right_aux
    (h : CompileTargetPrecision T₁ .bottom)
    (hnf : CallParamCheckedTargetNormalForm T₁) :
    T₁ = .bottom := by
  cases h with
  | refl =>
      rfl
  | fromBottom =>
      rfl
  | intersection_left_toAny _ hRight =>
      rcases hnf with ⟨_, hRightNf, _, _, _, hRightNotBottom, _⟩
      exact False.elim
        (hRightNotBottom
          (callParamCheckedTarget_eq_bottom_of_compileTargetPrecision_right_aux hRight hRightNf))
  | intersection_right_toAny hLeft _ =>
      rcases hnf with ⟨hLeftNf, _, _, _, hLeftNotBottom, _, _⟩
      exact False.elim
        (hLeftNotBottom
          (callParamCheckedTarget_eq_bottom_of_compileTargetPrecision_right_aux hLeft hLeftNf))

theorem callParamTarget_eq_bottom_of_compileTargetPrecision_right
    (h :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂))
    (hbottom : callParamTarget gct₂ G₂ = .bottom) :
    callParamTarget gct₁ G₁ = .bottom := by
  have hchecked₂ : callParamCheckedTarget gct₂ G₂ = .bottom := by
    simp [callParamCheckedTarget, hbottom]
  have hchecked₁ :
      callParamCheckedTarget gct₁ G₁ = .bottom :=
    callParamCheckedTarget_eq_bottom_of_compileTargetPrecision_right_aux
      (T₁ := callParamCheckedTarget gct₁ G₁)
      (by simpa [hchecked₂] using h)
      (callParamCheckedTarget_normalForm gct₁ G₁)
  have hInterp := congrArg interpTarget hchecked₁
  simpa [interpTarget_callParamCheckedTarget] using hInterp

private theorem callParamTarget_eq_any_of_compileTargetPrecision_left_any
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

theorem callParamCheckedTarget_union_congr
    (hG :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ G₁)
        (callParamCheckedTarget gct₂ G₂))
    (hH :
      CompileTargetPrecision
        (callParamCheckedTarget gct₁ H₁)
        (callParamCheckedTarget gct₂ H₂)) :
    CompileTargetPrecision
      (callParamCheckedTarget gct₁ (.union G₁ H₁))
      (callParamCheckedTarget gct₂ (.union G₂ H₂)) := by
  by_cases hG₁Any : callParamTarget gct₁ G₁ = .any
  · have hG₂Any : callParamTarget gct₂ G₂ = .any :=
      callParamTarget_eq_any_of_compileTargetPrecision_left_any hG hG₁Any
    simpa [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
      hG₁Any, hG₂Any] using
      (CompileTargetPrecision.refl (T := CheckedTarget.any))
  · by_cases hH₁Any : callParamTarget gct₁ H₁ = .any
    · have hH₂Any : callParamTarget gct₂ H₂ = .any :=
        callParamTarget_eq_any_of_compileTargetPrecision_left_any hH hH₁Any
      cases hG₂ : callParamTarget gct₂ G₂ <;>
        simpa [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
          hH₁Any, hH₂Any, hG₂] using
          (CompileTargetPrecision.refl (T := CheckedTarget.any))
    · by_cases hG₂Any : callParamTarget gct₂ G₂ = .any
      · simp [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
          hG₂Any]
        exact .toAny
      · by_cases hH₂Any : callParamTarget gct₂ H₂ = .any
        · simp [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
            hH₂Any]
          exact .toAny
        · simpa [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
            hG₁Any, hH₁Any, hG₂Any, hH₂Any] using
            (CompileTargetPrecision.union hG hH)

theorem callParamCheckedTarget_union
    (gct : GClassTable) (G H : GTy) :
    callParamCheckedTarget gct (.union G H) =
      match callParamCheckedTarget gct G, callParamCheckedTarget gct H with
      | .any, _ => .any
      | _, .any => .any
      | G', H' => .union G' H' := by
  cases hG : callParamTarget gct G <;>
    cases hH : callParamTarget gct H <;>
    simp [callParamCheckedTarget, callParamTarget, normalizeCallParamUnion,
      checkedTargetOfRuntimePublicTy, checkedTargetOfGTy, runtimePublicTy_id,
      coreNormalizeCheckedTarget, hG, hH]

theorem callParamCheckedTarget_intersection
    (gct : GClassTable) (G H : GTy) :
    callParamCheckedTarget gct (.intersection G H) =
      match callParamCheckedTarget gct G, callParamCheckedTarget gct H with
      | .any, T => T
      | T, .any => T
      | .bottom, _ => .bottom
      | _, .bottom => .bottom
      | T, U => Checked.normalizeCallParamAnnotationIntersection T U := by
  cases hG : callParamTarget gct G <;>
    cases hH : callParamTarget gct H <;>
    simp [callParamCheckedTarget, callParamTarget, normalizeCallParamIntersection,
      Checked.normalizeCallParamAnnotationIntersection,
      checkedTargetOfRuntimePublicTy, checkedTargetOfGTy, runtimePublicTy,
      runtimePublicTy_id, coreNormalizeCheckedTarget, checkedTargetOfGTy_eq_iff,
      checkedTargetOfGTy_if, hG, hH]

theorem callParamCheckedTarget_eq_callParamAnnotationTarget
    (gct : GClassTable) (G : GTy) :
    callParamCheckedTarget gct G = Checked.callParamAnnotationTarget G := by
  induction G with
  | any =>
      rfl
  | class_ =>
      rfl
  | callable =>
      rfl
  | bottom =>
      rfl
  | negClass =>
      rfl
  | union G H ihG ihH =>
      rw [callParamCheckedTarget_union, Checked.callParamAnnotationTarget_union, ihG, ihH]
      rfl
  | intersection G H ihG ihH =>
      rw [callParamCheckedTarget_intersection, Checked.callParamAnnotationTarget_intersection, ihG, ihH]
      rfl

private theorem moreStatic_runtimePublicTy :
    (G : GTy) → MoreStatic gct G (runtimePublicTy G)
  | .any => moreStatic_refl _ _
  | .class_ _ => moreStatic_refl _ _
  | .bottom => moreStatic_refl _ _
  | .negClass _ => moreStatic_refl _ _
  | .callable P R =>
      moreStatic_callable
        (moreStatic_runtimePublicTy P)
        (moreStatic_runtimePublicTy R)
  | .union G H =>
      moreStatic_union
        (moreStatic_runtimePublicTy G)
        (moreStatic_runtimePublicTy H)
  | .intersection G H =>
      moreStatic_intersection
        (moreStatic_runtimePublicTy G)
        (moreStatic_runtimePublicTy H)

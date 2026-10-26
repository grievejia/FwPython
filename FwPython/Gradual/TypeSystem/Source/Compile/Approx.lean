import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.TypeSystem.Source.Typing
import FwPython.Gradual.TypeSystem.TargetAdmissibility

/-! # Use-site elaboration target approximations -/

def approxFormula : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable _ _ => .any
  | .union G H => .union (approxFormula G) (approxFormula H)
  | .intersection G H => .intersection (approxFormula G) (approxFormula H)

def approxTarget : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable P R => .callable (approxTarget P) (approxTarget R)
  | .union G H => .union (approxTarget G) (approxTarget H)
  | .intersection G H => approxFormula (.intersection G H)

def CheckedBranchRefineOk (gct : GClassTable) (T : GTy) (C : Identifier) : Prop :=
  CheckedTargetTy gct (isInstanceThenRefinement T C) ∧
  CheckedTargetTy gct (isInstanceElseRefinement T C)

instance checkedBranchRefineOk_decidable
    (gct : GClassTable) (T : GTy) (C : Identifier) :
    Decidable (CheckedBranchRefineOk gct T C) := by
  dsimp [CheckedBranchRefineOk]
  infer_instance

theorem classTy_wellFormed_of_findGClass
    (hwfct : WellFormedGClassTableCore gct)
    (hfind : findGClass gct C = some cls) :
    WellFormedGTy gct (.class_ C) := by
  exact .class_ hfind (hwfct.raw.allMrosExist _ _ hfind).hmro

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

theorem approxTarget_checkedTarget
    (gct : GClassTable) (G : GTy) :
    CheckedTargetTy gct (approxTarget G) := by
  induction G with
  | any => exact .classFormula .any
  | class_ => exact .classFormula .class_
  | bottom => exact .classFormula .bottom
  | negClass _ => exact .classFormula .negClass
  | callable _ _ ihP ihR =>
      exact .callable ihP ihR
  | union _ _ ihG ihH =>
      exact .union ihG ihH
  | intersection _ _ _ _ =>
      exact .classFormula approxFormula_formula

theorem approxTarget_wellFormed
    (hwf : WellFormedGTy gct G) :
    WellFormedGTy gct (approxTarget G) := by
  induction hwf with
  | any => exact .any
  | bottom => exact .bottom
  | class_ hfind hmro => exact .class_ hfind hmro
  | negClass hfind hmro => exact .negClass hfind hmro
  | callable _ _ ihP ihR => exact .callable ihP ihR
  | union _ _ ihG ihH => exact .union ihG ihH
  | intersection hwfG hwfH _ _ =>
    exact .intersection (approxFormula_wellFormed hwfG) (approxFormula_wellFormed hwfH)

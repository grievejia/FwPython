import FwPython.Gradual.TypeSystem.TargetAdmissibility
import FwPython.Gradual.TypeSystem.WellFormedness
import FwPython.Gradual.TypeSystem.CheckedTargetSyntax

namespace Checked

def callParamAnnotationRawUnion
    (left right : GTy) : GTy :=
  match left, right with
  | .any, _ => .any
  | _, .any => .any
  | _, _ => .union left right

private def natListCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      match compare a b with
      | .eq => natListCmp as bs
      | other => other

private def identifierOrderTokens (a : Identifier) : List Nat :=
  a.toUTF8.toList.map (fun b => b.toNat.succ) ++ [0]

private def checkedTargetOrderTokens : CheckedTarget → List Nat
  | .any => [0]
  | .class_ a => 1 :: identifierOrderTokens a
  | .callable p r => 2 :: checkedTargetOrderTokens p ++ checkedTargetOrderTokens r
  | .union g h => 3 :: checkedTargetOrderTokens g ++ checkedTargetOrderTokens h
  | .intersection g h => 4 :: checkedTargetOrderTokens g ++ checkedTargetOrderTokens h
  | .bottom => [5]
  | .negClass a => 6 :: identifierOrderTokens a

def checkedTargetCmp (a b : CheckedTarget) : Ordering :=
  natListCmp (checkedTargetOrderTokens a) (checkedTargetOrderTokens b)

def normalizeCallParamAnnotationIntersection
    (left right : CheckedTarget) : CheckedTarget :=
  if left = right then left
  else if checkedTargetCmp left right = .gt then
    .intersection right left
  else
    .intersection left right

def callParamAnnotationRawIntersection
    (left right : GTy) : GTy :=
  match left, right with
  | .any, G => G
  | G, .any => G
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | G, H =>
      if G = H then G
      else if checkedTargetCmp
          (checkedTargetOfGTy G)
          (checkedTargetOfGTy H) = .gt then
        .intersection H G
      else
        .intersection G H

def callParamAnnotationRaw : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .bottom => .bottom
  | .negClass C => .negClass C
  | .callable _ _ => .any
  | .union G H =>
      callParamAnnotationRawUnion
        (callParamAnnotationRaw G)
        (callParamAnnotationRaw H)
  | .intersection G H =>
      callParamAnnotationRawIntersection
        (callParamAnnotationRaw G)
        (callParamAnnotationRaw H)

end Checked

private abbrev normalizeCallParamUnion (left right : GTy) : GTy :=
  Checked.callParamAnnotationRawUnion left right

private abbrev normalizeCallParamIntersection (left right : GTy) : GTy :=
  Checked.callParamAnnotationRawIntersection left right

/-- Source-facing normalized parameter target used by compiled calls. The
target is computed only from the source argument type; class-table facts are
proved separately by the admissibility lemmas below. -/
def callParamTarget (argSrcTy : GTy) : GTy :=
  Checked.callParamAnnotationRaw argSrcTy

-- Local unfolding lets the shape and validity proofs use the parameter operations directly.
attribute [local simp] Checked.callParamAnnotationRaw Checked.callParamAnnotationRawUnion
  Checked.callParamAnnotationRawIntersection

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
                  (checkedTargetOfGTy left)
                  (checkedTargetOfGTy right) = .gt
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
                  (checkedTargetOfGTy left)
                  (checkedTargetOfGTy right) = .gt
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                WellFormedGTy.intersection hwfRight hwfLeft
            · simpa [normalizeCallParamIntersection, hleftAny, hrightAny,
                hleftBottom, hrightBottom, hEq, hOrd] using
                WellFormedGTy.intersection hwfLeft hwfRight

theorem callParamTarget_formula
    (G : GTy) :
    FormulaGTy (callParamTarget G) := by
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

theorem callParamTarget_checkedTarget
    (gct : GClassTable) (argSrcTy : GTy) :
    CheckedTargetTy gct (callParamTarget argSrcTy) :=
  .classFormula (callParamTarget_formula argSrcTy)

theorem callParamTarget_wellFormed
    (hwf : WellFormedGTy gct argSrcTy) :
    WellFormedGTy gct (callParamTarget argSrcTy) := by
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

/-- Checked-target image of `callParamTarget`, used directly by checked calls. -/
def callParamCheckedTarget (argSrcTy : GTy) : CheckedTarget :=
  checkedTargetOfGTy (callParamTarget argSrcTy)

@[simp] theorem interpTarget_callParamCheckedTarget
    (argSrcTy : GTy) :
    interpTarget (callParamCheckedTarget argSrcTy) =
      callParamTarget argSrcTy := by
  simp [callParamCheckedTarget]

theorem callParamCheckedTarget_intersection_any_left
    (G : GTy) :
    callParamCheckedTarget (.intersection .any G) =
      callParamCheckedTarget G := rfl

/-- The parameter target for a union is the union of its targets, unless either target is any. -/
theorem callParamCheckedTarget_union
    (G H : GTy) :
    callParamCheckedTarget (.union G H) =
      match callParamCheckedTarget G, callParamCheckedTarget H with
      | .any, _ => .any
      | _, .any => .any
      | G', H' => .union G' H' := by
  cases hG : Checked.callParamAnnotationRaw G <;>
    cases hH : Checked.callParamAnnotationRaw H <;>
    simp [callParamCheckedTarget, callParamTarget, Checked.callParamAnnotationRaw,
      Checked.callParamAnnotationRawUnion, checkedTargetOfGTy, hG, hH]

/-- Intersection parameter targets discard any and absorb bottom. Equal targets occur once;
distinct targets are placed in a fixed order. -/
theorem callParamCheckedTarget_intersection
    (G H : GTy) :
    callParamCheckedTarget (.intersection G H) =
      match callParamCheckedTarget G, callParamCheckedTarget H with
      | .any, T => T
      | T, .any => T
      | .bottom, _ => .bottom
      | _, .bottom => .bottom
      | T, U => Checked.normalizeCallParamAnnotationIntersection T U := by
  cases hG : Checked.callParamAnnotationRaw G <;>
    cases hH : Checked.callParamAnnotationRaw H <;>
    simp [callParamCheckedTarget, callParamTarget, Checked.callParamAnnotationRaw,
      Checked.callParamAnnotationRawIntersection, Checked.normalizeCallParamAnnotationIntersection,
      checkedTargetOfGTy, checkedTargetOfGTy_eq_iff, checkedTargetOfGTy_if, hG, hH]

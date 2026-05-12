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

private theorem natListCmp_swap :
    ∀ (as bs : List Nat), natListCmp as bs = (natListCmp bs as).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      unfold natListCmp
      have hab : compare a b = (compare b a).swap := by
        simpa using (Nat.compare_swap b a).symm
      cases hba : compare b a <;>
        simp [hab, hba, Ordering.swap, natListCmp_swap as bs]

theorem checkedTargetCmp_swap (a b : CheckedTarget) :
    checkedTargetCmp a b = (checkedTargetCmp b a).swap := by
  unfold checkedTargetCmp
  exact natListCmp_swap _ _

theorem checkedTargetCmp_lt_of_gt {a b : CheckedTarget}
    (h : checkedTargetCmp a b = .gt) :
    checkedTargetCmp b a = .lt := by
  rw [checkedTargetCmp_swap, h]; rfl

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
          (checkedTargetOfRuntimePublicTy G)
          (checkedTargetOfRuntimePublicTy H) = .gt then
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

def callParamAnnotationTarget (G : GTy) : CheckedTarget :=
  checkedTargetOfRuntimePublicTy (callParamAnnotationRaw G)

private theorem checkedTargetOfGTy_injective :
    Function.Injective checkedTargetOfGTy :=
  fun _ _ hEq => by simpa using congrArg interpTarget hEq

private theorem checkedTargetOfGTy_eq_iff
    (G H : GTy) :
    checkedTargetOfGTy G = checkedTargetOfGTy H ↔
      G = H :=
  ⟨fun h => checkedTargetOfGTy_injective h, fun h => h ▸ rfl⟩

private theorem checkedTargetOfGTy_if
    (p : Prop) [Decidable p] (G H : GTy) :
    checkedTargetOfGTy (if p then G else H) =
      if p then checkedTargetOfGTy G else checkedTargetOfGTy H := by
  by_cases hp : p <;> simp [hp]

@[simp] theorem callParamAnnotationTarget_any :
    callParamAnnotationTarget .any = .any := rfl

@[simp] theorem callParamAnnotationTarget_class_ (C : Identifier) :
    callParamAnnotationTarget (.class_ C) = .class_ C := rfl

@[simp] theorem callParamAnnotationTarget_callable (P R : GTy) :
    callParamAnnotationTarget (.callable P R) = .any := rfl

@[simp] theorem callParamAnnotationTarget_bottom :
    callParamAnnotationTarget .bottom = .bottom := rfl

@[simp] theorem callParamAnnotationTarget_negClass (C : Identifier) :
    callParamAnnotationTarget (.negClass C) = .negClass C := rfl

theorem callParamAnnotationTarget_union
    (G H : GTy) :
    callParamAnnotationTarget (.union G H) =
      match callParamAnnotationTarget G, callParamAnnotationTarget H with
      | .any, _ => .any
      | _, .any => .any
      | G', H' => .union G' H' := by
  cases hG : callParamAnnotationRaw G <;>
    cases hH : callParamAnnotationRaw H <;>
    simp [callParamAnnotationTarget, callParamAnnotationRaw, callParamAnnotationRawUnion,
      checkedTargetOfRuntimePublicTy, checkedTargetOfGTy, runtimePublicTy_id,
      coreNormalizeCheckedTarget, hG, hH]

theorem callParamAnnotationTarget_intersection
    (G H : GTy) :
    callParamAnnotationTarget (.intersection G H) =
      match callParamAnnotationTarget G, callParamAnnotationTarget H with
      | .any, T => T
      | T, .any => T
      | .bottom, _ => .bottom
      | _, .bottom => .bottom
      | T, U => normalizeCallParamAnnotationIntersection T U := by
  cases hG : callParamAnnotationRaw G <;>
    cases hH : callParamAnnotationRaw H <;>
    simp [callParamAnnotationTarget, callParamAnnotationRaw, callParamAnnotationRawIntersection,
      normalizeCallParamAnnotationIntersection,
      checkedTargetOfRuntimePublicTy, checkedTargetOfGTy, runtimePublicTy,
      runtimePublicTy_id, coreNormalizeCheckedTarget, checkedTargetOfGTy_eq_iff,
      checkedTargetOfGTy_if, hG, hH]

end Checked

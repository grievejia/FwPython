import FwPython.Static.Subtyping.ObjectTypeLowerBound
import FwPython.Static.Subtyping.Equations
import FwPython.Static.Subtyping.Core
import FwPython.Common.ListSubsets

set_option autoImplicit false

/-! # Comparing class and function types

A function subtype must accept every input required by the target function. Its
result also lies below the target result when the target input is not below bottom.
For class types, subtyping places the target class in the source class's actual MRO.
-/

namespace FwPython.Static.Subtyping

/-- A function subtype reverses the input relation and constrains results when the target input is nonempty. -/
private theorem callable_subtype_consequences {ct : ClassTable}
    {structural : WellFormedClassHierarchy ct} {sourceParameter sourceResult targetParameter targetResult : Ty}
    (included : IsSubtype structural
      (.callable sourceParameter sourceResult) (.callable targetParameter targetResult)) :
    IsSubtype structural targetParameter sourceParameter ∧
      (IsSubtype structural targetParameter .bottom ∨ IsSubtype structural sourceResult targetResult) := by
  let context := structural.typeContext
  let P : WellFormedType context.names := ⟨sourceParameter, included.sourceWellFormed.callable_param⟩
  let R : WellFormedType context.names := ⟨sourceResult, included.sourceWellFormed.callable_return⟩
  let Q : WellFormedType context.names := ⟨targetParameter, included.targetWellFormed.callable_param⟩
  let S : WellFormedType context.names := ⟨targetResult, included.targetWellFormed.callable_return⟩
  have inputBound := (functionIntersection_subtype_iff context [(P, R)] Q S).mp
    (.trans (WellFormedType.functionIntersection_subtype List.mem_cons_self) included)
  rw [inputTypeForResult_eq_join, subsetsWithResultBelow_eq_filter, nonemptySubsets_singleton (P, R)] at inputBound
  simp only [List.filter_cons, List.filter_nil, List.map_cons, List.map_nil] at inputBound
  by_cases accepted : checkSubtypeBool context (WellFormedType.meetTypes context.valid.objectKnown [R]) S = true
  · simp only [if_pos accepted, List.map_cons, List.map_nil] at inputBound
    have resultBound := (checkSubtypeBool_iff_subtype context
      (WellFormedType.meetTypes context.valid.objectKnown [R]) S).mp accepted
    exact ⟨.trans inputBound (.unionElim
      (.interLeft (.refl P.namesKnown) context.objectType.namesKnown) (.bottom P.namesKnown)),
      .inr (.trans (.interIntro (.refl R.namesKnown) (.objectTop R.namesKnown)) resultBound)⟩
  · simp only [if_neg accepted, List.map_nil] at inputBound
    exact ⟨.trans inputBound (.bottom P.namesKnown), .inl inputBound⟩

end FwPython.Static.Subtyping

open FwPython.Static.Subtyping

/-- The target function's required input is below the source function's accepted input. -/
theorem callable_domain_subtype {ct : ClassTable} {structural : WellFormedClassHierarchy ct} {P R Q S : Ty}
    (included : IsSubtype structural (.callable P R) (.callable Q S)) :
    IsSubtype structural Q P :=
  (callable_subtype_consequences included).1

/-- When the target input is not below bottom, the source result lies below the target result. -/
theorem callable_return_subtype {ct : ClassTable} {structural : WellFormedClassHierarchy ct} {P R Q S : Ty}
    (included : IsSubtype structural (.callable P R) (.callable Q S))
    (nonempty : ¬ IsSubtype structural Q .bottom) : IsSubtype structural R S :=
  (callable_subtype_consequences included).2.resolve_left nonempty

/-- A class subtype relation places the target class in the source declaration's MRO. -/
theorem class_subtype_mem_mro {ct : ClassTable} {c a : Identifier}
    {declaration : Class} {linearization : List Identifier} (structural : WellFormedClassHierarchy ct)
    (included : IsSubtype structural (.class_ c) (.class_ a))
    (lookup : findClass ct c = some declaration) (computed : ComputeMro ct declaration linearization) :
    a ∈ linearization :=
  objectTypeLowerBound_mem_mro structural lookup computed
    (.trans (objectTypeLowerBound_ownClass structural c (findClass_name_known lookup)) included)

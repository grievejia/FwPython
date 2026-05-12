import FwPython.Gradual.TypeSystem.Source.Precision
import FwPython.Examples.Gradual.BlameProvenanceExamples

/-! # Gradual source typing regression examples -/

open Checked

private def pokeDogMethod : GMethod where
  name := "poke"
  receiverParam := "self"
  param := "arg"
  paramTy := .class_ "Dog"
  returnTy := .class_ "Dog"
  body := .constTrue

private def pokeCatMethod : GMethod where
  name := "poke"
  receiverParam := "self"
  param := "arg"
  paramTy := .class_ "Cat"
  returnTy := .class_ "Cat"
  body := .constFalse

private def callableAttrObjectClass : GClass where
  name := objectClass
  baseClasses := []
  methods := []

private def callableAttrDogClass : GClass where
  name := "DogFn"
  baseClasses := [objectClass]
  methods := [pokeDogMethod]

private def callableAttrCatClass : GClass where
  name := "CatFn"
  baseClasses := [objectClass]
  methods := [pokeCatMethod]

private def callableAttrCt : GClassTable :=
  [callableAttrDogClass, callableAttrCatClass, callableAttrObjectClass]

private def dogFacet : CallableFacet :=
  { paramTy := .class_ "Dog", returnTy := .class_ "Dog" }

private def catFacet : CallableFacet :=
  { paramTy := .class_ "Cat", returnTy := .class_ "Cat" }

private def dogCatInterSummary : CallableSummary :=
  .intersection (.leaf dogFacet) (.leaf catFacet)

private def dogCatUnionSummary : CallableSummary :=
  .union (.leaf dogFacet) (.leaf catFacet)

private theorem any_to_class_assignable (gct : GClassTable) (C : Identifier) :
    AssignableTo gct .any (.class_ C) := by
  simpa [AssignableTo, lowerBound, upperBound] using
    (IsSubtype.bottom (ct := eraseClassTable gct) (T := (.class_ C : Ty)))

private theorem dogCatInterSummary_ok
    (hDog : WellFormedGTy gct (.class_ "Dog"))
    (hCat : WellFormedGTy gct (.class_ "Cat")) :
    CallableSummaryOk gct dogCatInterSummary := by
  refine .intersection ?_ ?_
  · exact .leaf ⟨.class_, hDog, .class_, hDog⟩
  · exact .leaf ⟨.class_, hCat, .class_, hCat⟩

private theorem dogCatUnionSummary_ok
    (hDog : WellFormedGTy gct (.class_ "Dog"))
    (hCat : WellFormedGTy gct (.class_ "Cat")) :
    CallableSummaryOk gct dogCatUnionSummary := by
  refine .union ?_ ?_
  · exact .leaf ⟨.class_, hDog, .class_, hDog⟩
  · exact .leaf ⟨.class_, hCat, .class_, hCat⟩

example :
  attrSourceTy? callableAttrCt (.intersection (.class_ "DogFn") (.class_ "CatFn")) "poke" =
    some (.intersection (.callable (.class_ "Dog") (.class_ "Dog"))
                        (.callable (.class_ "Cat") (.class_ "Cat"))) := by
  native_decide

example :
  attrSourceTy? overrideCt (.intersection (.class_ "Dog") (.negClass boolClass)) "speak" =
    some (.callable .any .any) := by
  native_decide

example :
  attrSourceTy? overrideCt (.intersection (.class_ "Dog") .any) "speak" =
    some (.intersection (.callable .any .any) .any) := by
  native_decide

example :
  attrSourceTy? callableAttrCt (.union (.class_ "DogFn") (.negClass boolClass)) "poke" = none := by
  native_decide

-- Keep the envelope merge explicit so this fails for the intended reason.
example :
  mergeAttrUnionResult (some .any) (some .bottom) = some (.union .any .bottom) := rfl

example :
  attrSourceTy? callableAttrCt (.union .any .bottom) "poke" = some (.union .any .bottom) := by
  native_decide

example :
  attrSourceTy? callableAttrCt (.intersection .bottom .bottom) "poke" =
    some (.intersection .bottom .bottom) := by
  native_decide

example :
  ¬ RuntimePublicAnnotation callableAttrCt
      (.intersection (.callable (.class_ "Dog") (.class_ "Dog"))
        (.callable (.class_ "Cat") (.class_ "Cat"))) := by
  intro h
  have hchecked := runtimePublicAnnotation_checked h
  cases hchecked with
  | classFormula hformula =>
      cases hformula with
      | intersection hLeft hRight => cases hLeft <;> cases hRight
  | interCallableLeft _ _ hbm => cases hbm.1
  | interCallableRight hbm _ _ => cases hbm.1

example
    (gct : GClassTable)
    (hwfct : WellFormedGClassTableCore gct)
    (hDog : WellFormedGTy gct (.class_ "Dog"))
    (hCat : WellFormedGTy gct (.class_ "Cat"))
    (hDogNotCat : ¬ AssignableTo gct (.class_ "Dog") (.class_ "Cat")) :
    callSourceTy? (gct := gct) (s := dogCatInterSummary) (argTy := .class_ "Dog")
      hwfct (dogCatInterSummary_ok (gct := gct) hDog hCat) hDog = some (.class_ "Dog") := by
  have hw :
      CallResultWitness gct (.class_ "Dog") dogCatInterSummary (some (.class_ "Dog")) :=
    .inter_left
      (.leaf_hit (assignableTo_refl gct (.class_ "Dog")))
      (.leaf_miss hDogNotCat)
  simpa [dogCatInterSummary] using
    (callSourceTy?_of_witness
      (hwfct := hwfct)
      (hsum := dogCatInterSummary_ok (gct := gct) hDog hCat)
      (hwfArg := hDog)
      hw)

example (gct : GClassTable) :
    CallResultWitness gct .any dogCatInterSummary (some .any) := by
  exact .inter_both
    (.leaf_hit (any_to_class_assignable gct "Dog"))
    (.leaf_hit (any_to_class_assignable gct "Cat"))

example
    (gct : GClassTable)
    (hwfct : WellFormedGClassTableCore gct)
    (hDog : WellFormedGTy gct (.class_ "Dog"))
    (hCat : WellFormedGTy gct (.class_ "Cat")) :
    callSourceTy? (gct := gct) (s := dogCatInterSummary) (argTy := .any)
      hwfct (dogCatInterSummary_ok (gct := gct) hDog hCat) .any = some .any := by
  simpa [dogCatInterSummary] using
    (callSourceTy?_of_witness
      (gct := gct)
      (argTy := .any)
      (s := dogCatInterSummary)
      (result := some .any)
      (hwfct := hwfct)
      (hsum := dogCatInterSummary_ok (gct := gct) hDog hCat)
      (hwfArg := .any)
      (show CallResultWitness gct .any dogCatInterSummary (some .any) by
        exact .inter_both
          (.leaf_hit (any_to_class_assignable gct "Dog"))
          (.leaf_hit (any_to_class_assignable gct "Cat"))))

example
    (gct : GClassTable)
    (hwfct : WellFormedGClassTableCore gct)
    (hDog : WellFormedGTy gct (.class_ "Dog"))
    (hCat : WellFormedGTy gct (.class_ "Cat"))
    (hDogNotCat : ¬ AssignableTo gct (.class_ "Dog") (.class_ "Cat")) :
    callSourceTy? (gct := gct) (s := dogCatUnionSummary) (argTy := .class_ "Dog")
      hwfct (dogCatUnionSummary_ok (gct := gct) hDog hCat) hDog = none := by
  have hw :
      CallResultWitness gct (.class_ "Dog") dogCatUnionSummary none :=
    .union_none_right
      (.leaf_hit (assignableTo_refl gct (.class_ "Dog")))
      (.leaf_miss hDogNotCat)
  simpa [dogCatUnionSummary] using
    (callSourceTy?_of_witness
      (hwfct := hwfct)
      (hsum := dogCatUnionSummary_ok (gct := gct) hDog hCat)
      (hwfArg := hDog)
      hw)

example
    (gct : GClassTable)
    (hwfct : WellFormedGClassTableCore gct)
    (hDog : WellFormedGTy gct (.class_ "Dog")) :
    let summary : CallableSummary := .union .tainted (.leaf dogFacet)
    callSourceTy? (gct := gct) (s := summary) (argTy := .class_ "Dog")
      hwfct
      (by
        refine .union .tainted ?_
        exact .leaf ⟨.class_, hDog, .class_, hDog⟩)
      hDog = some (.union .any (.class_ "Dog")) := by
  have hw :
      CallResultWitness gct (.class_ "Dog") (.union .tainted (.leaf dogFacet))
        (some (.union .any (.class_ "Dog"))) :=
    .union_some .tainted (.leaf_hit (assignableTo_refl gct (.class_ "Dog")))
  simpa [dogFacet] using
    (callSourceTy?_of_witness
      (gct := gct)
      (argTy := .class_ "Dog")
      (s := .union .tainted (.leaf dogFacet))
      (result := some (.union .any (.class_ "Dog")))
      (hwfct := hwfct)
      (hsum := by
        refine .union .tainted ?_
        exact .leaf ⟨.class_, hDog, .class_, hDog⟩)
      (hwfArg := hDog)
      hw)

example
    (gct : GClassTable)
    (hwfct : WellFormedGClassTableCore gct) :
    let summary : CallableSummary :=
      .union
        (.leaf { paramTy := .bottom, returnTy := .bottom })
        (.leaf { paramTy := .bottom, returnTy := .bottom })
    callSourceTy? (gct := gct) (s := summary) (argTy := .bottom)
      hwfct
      (by
        refine .union ?_ ?_ <;>
          exact .leaf ⟨.bottom, .bottom, .bottom, .bottom⟩)
      .bottom = some (.union .bottom .bottom) := by
  have hw :
      CallResultWitness gct .bottom
        (.union
          (.leaf { paramTy := .bottom, returnTy := .bottom })
          (.leaf { paramTy := .bottom, returnTy := .bottom }))
        (some (.union .bottom .bottom)) :=
    .union_some
      (.leaf_hit (assignableTo_refl gct .bottom))
      (.leaf_hit (assignableTo_refl gct .bottom))
  simpa using
    (callSourceTy?_of_witness
      (gct := gct)
      (argTy := .bottom)
      (s := .union
        (.leaf { paramTy := .bottom, returnTy := .bottom })
        (.leaf { paramTy := .bottom, returnTy := .bottom }))
      (result := some (.union .bottom .bottom))
      (hwfct := hwfct)
      (hsum := by
        refine .union ?_ ?_ <;>
          exact .leaf ⟨.bottom, .bottom, .bottom, .bottom⟩)
      (hwfArg := .bottom)
      hw)

example :
  CompileTargetPrecision
    (callParamCheckedTarget ([] : GClassTable) (.intersection (.class_ "C") (.class_ "Bar")))
    (callParamCheckedTarget ([] : GClassTable) (.intersection .any (.class_ "Bar"))) := by
  have hLeft :
      callParamCheckedTarget ([] : GClassTable) (.intersection (.class_ "C") (.class_ "Bar")) =
        .intersection (.class_ "Bar") (.class_ "C") := by
    have hOrd :
        Checked.checkedTargetCmp
            (checkedTargetOfRuntimePublicTy (GTy.class_ "C"))
            (checkedTargetOfRuntimePublicTy (GTy.class_ "Bar")) = .gt := by
      native_decide
    have hNe :
        checkedTargetOfRuntimePublicTy (GTy.class_ "C") ≠
          checkedTargetOfRuntimePublicTy (GTy.class_ "Bar") := by
      decide
    have hEq := callParamCheckedTarget_intersection_of_uncollapsed
        ([] : GClassTable)
        (.class_ "C")
        (.class_ "Bar")
        (by simp [callParamTarget])
        (by simp [callParamTarget])
        (by simp [callParamTarget])
        (by simp [callParamTarget])
        (by simp [callParamTarget])
    unfold Checked.normalizeCallParamAnnotationIntersection at hEq
    simpa [callParamCheckedTarget, callParamTarget, hOrd, hNe] using hEq
  rw [hLeft]
  rw [callParamCheckedTarget_intersection_any_left ([] : GClassTable) (.class_ "Bar")]
  exact CompileTargetPrecision.intersection_right_toAny
    (CompileTargetPrecision.refl (T := .class_ "Bar"))
    (CompileTargetPrecision.toAny (T := .class_ "C"))

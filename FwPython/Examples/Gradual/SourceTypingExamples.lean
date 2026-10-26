import FwPython.Gradual
import FwPython.Examples.Static.Subtyping

/-! # Tests for gradual source typing -/

open Checked

private def overrideSpeakMammal : GMethod where
  name := "speak"
  receiverParam := "self"
  param := "arg"
  paramTy := .any
  returnTy := .any
  body := .constTrue

private def overrideSpeakDog : GMethod where
  name := "speak"
  receiverParam := "self"
  param := "arg"
  paramTy := .any
  returnTy := .any
  body := .constFalse

private def overrideObjectClass : GClass where
  name := objectClass
  baseClasses := []
  methods := []

private def overrideMammalClass : GClass where
  name := "Mammal"
  baseClasses := [objectClass]
  methods := [overrideSpeakMammal]

private def overrideDogClass : GClass where
  name := "Dog"
  baseClasses := ["Mammal"]
  methods := [overrideSpeakDog]

private def overrideCt : GClassTable :=
  [overrideDogClass, overrideMammalClass, overrideObjectClass]

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

/-- Method lookup finds Dog as both the input type and result type of DogFn's method. -/
private theorem callableAttrDog_find :
    FindGMethodType callableAttrCt "DogFn" "poke" (.class_ "Dog") (.class_ "Dog") :=
  ⟨callableAttrDogClass, ["DogFn", objectClass], pokeDogMethod, rfl,
    .step rfl (by decide +kernel) (.cons rfl (.root rfl) .nil) rfl, rfl, rfl, rfl⟩

/-- Lookup finds Dog's override before Mammal's method. -/
private theorem overrideDog_find : FindGMethodType overrideCt "Dog" "speak" .any .any :=
  ⟨overrideDogClass, ["Dog", "Mammal", objectClass], overrideSpeakDog, rfl,
    .step rfl (by decide +kernel)
      (.cons rfl
        (.step rfl (by decide +kernel) (.cons rfl (.root rfl) .nil) rfl) .nil)
      rfl, rfl, rfl, rfl⟩

example :
    isInstanceThenRefinement .any "Dog" = .class_ "Dog" := rfl

example :
    isInstanceElseRefinement .any "Dog" = .negClass "Dog" := rfl

example :
    isInstanceThenRefinement .bottom "Dog" =
      .intersection .bottom (.class_ "Dog") := rfl

example :
    isInstanceThenRefinement (.negClass "Cat") "Dog" =
      .intersection (.negClass "Cat") (.class_ "Dog") := rfl

example :
    isInstanceThenRefinement (.intersection .any .any) "Dog" =
      .class_ "Dog" := rfl

example :
    isInstanceThenRefinement (.intersection (.class_ "Mammal") .any) "Dog" =
      .intersection (.class_ "Mammal") (.class_ "Dog") := rfl

example :
    isInstanceThenRefinement (.union (.class_ "Mammal") .any) "Dog" =
      .class_ "Dog" := rfl

example :
    isInstanceThenRefinement (.union (.callable .any .any) .any) "Dog" =
      .class_ "Dog" := rfl

example :
    isInstanceThenRefinement
        (.intersection (.union (.class_ "Mammal") (.class_ "Pet")) .any)
        "Dog" =
      .intersection (.union (.class_ "Mammal") (.class_ "Pet")) (.class_ "Dog") := rfl

example :
    isInstanceThenRefinement (.callable .any .any) "Dog" =
      .intersection (.callable .any .any) (.class_ "Dog") := rfl

example
    (hfind : findGClass gct "Dog" = some cls) :
    GSrcInfer gct hwfct
      [{ name := "x", sourceTy := .any }]
      (.cond (.isInstance "x" "Dog") (.var "x") (.var "x"))
      (.union (.class_ "Dog") (.negClass "Dog")) := by
  refine GSrcInfer.condIsInstance
    (b := { name := "x", sourceTy := .any })
    (by simp [SBindingEnv.lookupBinding]) hfind ?_ ?_
  · exact GSrcInfer.var
      (x := "x")
      (b := { name := "x", sourceTy := .class_ "Dog" })
      (by rfl)
  · exact GSrcInfer.var
      (x := "x")
      (b := { name := "x", sourceTy := .negClass "Dog" })
      (by rfl)

example
    (hfind : findGClass gct "Dog" = some cls) :
    GSrcInfer gct hwfct
      [{ name := "x", sourceTy := .intersection (.class_ "Mammal") .any }]
      (.cond (.isInstance "x" "Dog") (.var "x") (.var "x"))
      (.union
        (.intersection (.class_ "Mammal") (.class_ "Dog"))
        (.intersection (.class_ "Mammal") (.negClass "Dog"))) := by
  refine GSrcInfer.condIsInstance
    (b := { name := "x", sourceTy := .intersection (.class_ "Mammal") .any })
    (by simp [SBindingEnv.lookupBinding]) hfind ?_ ?_
  · exact GSrcInfer.var
      (x := "x")
      (b := { name := "x", sourceTy := .intersection (.class_ "Mammal") (.class_ "Dog") })
      (by rfl)
  · exact GSrcInfer.var
      (x := "x")
      (b := { name := "x", sourceTy := .intersection (.class_ "Mammal") (.negClass "Dog") })
      (by rfl)

example :
  attrSourceTy? callableAttrCt (.intersection (.class_ "DogFn") (.class_ "CatFn")) "poke" =
    some (.intersection (.callable (.class_ "Dog") (.class_ "Dog"))
                        (.callable (.class_ "Cat") (.class_ "Cat"))) := by
  have catFind :
      FindGMethodType callableAttrCt "CatFn" "poke" (.class_ "Cat") (.class_ "Cat") :=
    ⟨callableAttrCatClass, ["CatFn", objectClass], pokeCatMethod, rfl,
      .step rfl (by decide +kernel) (.cons rfl (.root rfl) .nil) rfl, rfl, rfl, rfl⟩
  simp [attrSourceTy?, lookupMethodTy?_of_find callableAttrDog_find,
    lookupMethodTy?_of_find catFind, mergeAttrIntersectionResult]

example :
  attrSourceTy? overrideCt (.intersection (.class_ "Dog") (.negClass boolClass)) "speak" =
    some (.callable .any .any) := by
  simp [attrSourceTy?, lookupMethodTy?_of_find overrideDog_find, mergeAttrIntersectionResult]

example :
  attrSourceTy? overrideCt (.intersection (.class_ "Dog") .any) "speak" =
    some (.intersection (.callable .any .any) .any) := by
  simp [attrSourceTy?, lookupMethodTy?_of_find overrideDog_find, mergeAttrIntersectionResult]

example :
  attrSourceTy? callableAttrCt (.union (.class_ "DogFn") (.negClass boolClass)) "poke" = none := by
  simp [attrSourceTy?, lookupMethodTy?_of_find callableAttrDog_find, mergeAttrUnionResult]

-- Keep the envelope merge explicit so this fails for the intended reason.
example :
  mergeAttrUnionResult (some .any) (some .bottom) = some (.union .any .bottom) := rfl

example :
  attrSourceTy? callableAttrCt (.union .any .bottom) "poke" = some (.union .any .bottom) := by
  decide +kernel

example :
  attrSourceTy? callableAttrCt (.intersection .bottom .bottom) "poke" =
    some (.intersection .bottom .bottom) := by
  decide +kernel

example :
  ¬ CheckedTargetTy callableAttrCt
      (.intersection (.callable (.class_ "Dog") (.class_ "Dog"))
        (.callable (.class_ "Cat") (.class_ "Cat"))) := by
  intro h
  cases h with
  | classFormula hformula =>
      cases hformula with
      | intersection hLeft hRight => cases hLeft <;> cases hRight
  | interCallableLeft _ _ hbm => cases hbm.1
  | interCallableRight hbm _ _ => cases hbm.1

open FwPython.Examples.Static.Subtyping

/-- The call examples use four builtin classes, with no methods. -/
private def callClasses : EmbeddableStaticClassTable (fixtureTable none) where
  hwf := fixtureWellFormed
  methodSigChecked := by
    intro name declaration method lookup member
    have selected := findClass_mem lookup
    simp [fixtureTable] at selected
    rcases selected with rfl | rfl | rfl | rfl <;> cases member

private abbrev callCore := wellFormedGClassTableCore_embedClassTable callClasses
private abbrev callTable := embedClassTable (fixtureTable none)

private abbrev booleanSource : GTy := .class_ boolClass
private abbrev noneSource : GTy := .class_ noneClass
private abbrev bothFunctions : GTy :=
  .intersection (.callable booleanSource booleanSource) (.callable noneSource noneSource)
private abbrev eitherFunction : GTy :=
  .union (.callable booleanSource booleanSource) (.callable noneSource noneSource)

/-- Compare both bounds in the builtin test table, including name validation. -/
private def boundsSubtypeDecidable (source target : GTy) :
    Decidable (BoundsSubtype callTable callCore.toWellFormedClassHierarchy source target) := by
  unfold BoundsSubtype
  letI := callCore.subtypeDecidable (lowerBound source) (lowerBound target)
  letI := callCore.subtypeDecidable (upperBound source) (upperBound target)
  infer_instance

/-- True when a call's result has the same lower and upper bounds as the expected type. -/
private def callHasBounds (callee argument expected : GTy) : Bool :=
  match callSourceTy? callTable callee argument callCore with
  | none => false
  | some result =>
      @decide (BoundsSubtype callTable callCore.toWellFormedClassHierarchy result expected ∧ BoundsSubtype callTable callCore.toWellFormedClassHierarchy expected result)
        (by
          haveI := boundsSubtypeDecidable result expected
          haveI := boundsSubtypeDecidable expected result
          infer_instance)

/-! ## Call checks require known class names -/

/-- An empty callee does not bypass the class-name check on its argument. -/
example : callSourceTy? callTable .bottom (.class_ "Unknown") callCore = none := by
  decide +kernel

/-- A call with an unknown class name in the callee annotation is rejected. -/
example : callSourceTy? callTable (.class_ "Unknown") .any callCore = none := by
  decide +kernel

/-- Callee validation checks names inside declared function results. -/
example : callSourceTy? callTable (.callable .any (.class_ "Unknown"))
    (.class_ boolClass) callCore = none := by
  decide +kernel

/-- An empty callee still needs valid names in its function requirements. -/
example : callSourceTy? callTable
    (.intersection .bottom (.callable .any (.class_ "Unknown"))) .any callCore = none := by
  decide +kernel

/-! ## Results depend on the argument annotation -/

/-- A Bool argument selects the Bool result and excludes the NoneType requirement. -/
example : callSourceTy? callTable bothFunctions booleanSource
    callCore = some booleanSource := by decide +kernel

/-- A NoneType argument selects the NoneType result. -/
example : callSourceTy? callTable bothFunctions noneSource
    callCore = some noneSource := by decide +kernel

/-- An argument with both types keeps both result requirements. -/
example : callSourceTy? callTable bothFunctions (.intersection booleanSource noneSource)
    callCore =
    some (.intersection booleanSource noneSource) := by decide +kernel

/-- A bottom argument permits both requirements; their results are intersected. -/
example : callSourceTy? callTable bothFunctions .bottom
    callCore = some (.intersection booleanSource noneSource) := by decide +kernel

/-- Either function can be called on an argument that fits both inputs. Its result can come from either function. -/
example : callSourceTy? callTable eitherFunction (.intersection booleanSource noneSource)
    callCore =
    some (.union booleanSource noneSource) := by decide +kernel

/-- The combined requirements accept an argument with either input type. -/
example : callSourceTy? callTable bothFunctions (.union booleanSource noneSource)
    callCore =
    some (.union booleanSource noneSource) := by decide +kernel

/-- An unknown argument permits both results. The bounds are Bool & NoneType and Bool | NoneType. -/
example : callHasBounds bothFunctions .any
    (.union (.intersection booleanSource noneSource)
      (.intersection .any (.union booleanSource noneSource))) = true := by
  decide +kernel

/-- A possible NoneType function prevents calling this union on Bool. -/
example : callSourceTy? callTable eitherFunction booleanSource
    callCore = none := by decide +kernel

/-- An unknown callee part permits a narrower result than the known Bool requirement.
The result has an empty lower bound and a Bool upper bound. -/
example : callSourceTy? callTable (.intersection .any (.callable booleanSource booleanSource)) booleanSource
    callCore = some (.intersection .any booleanSource) := by decide +kernel

/-- With f : any & (Bool -> Bool), the checker accepts consume(f(x)) for x : Bool
and consume : NoneType -> Bool. The result of f(x) requires a runtime check. -/
example : GSrcInfer callTable callCore
    [⟨"f", .intersection .any (.callable booleanSource booleanSource)⟩,
      ⟨"x", booleanSource⟩, ⟨"consume", .callable noneSource booleanSource⟩]
    (.call (.var "consume") (.call (.var "f") (.var "x"))) booleanSource := by
  refine .call (argSrcTy := .intersection .any booleanSource) (.var rfl) ?_ ?_
  · exact .call (.var rfl) (.var rfl) (by decide +kernel)
  · decide +kernel

/-- An incompatible input can use the unknown part of a callee intersection. -/
example : callSourceTy? callTable (.intersection .any (.callable booleanSource booleanSource)) noneSource
    callCore = some .any := by decide +kernel

/-- An unknown callee alternative cannot bypass the other alternative's input requirement. -/
example : callSourceTy? callTable (.union .any (.callable booleanSource booleanSource)) noneSource
    callCore = none := by decide +kernel

/-- A compatible input permits both callee alternatives. The result keeps their union. -/
example : callSourceTy? callTable (.union .any (.callable booleanSource booleanSource)) booleanSource
    callCore = some (.union .any booleanSource) := by decide +kernel

/-- Equal unknown alternatives give one unknown result. -/
example : callSourceTy? callTable (.union .any .any) booleanSource
    callCore = some .any := by decide +kernel

/-- Independent unknown inputs can accept different argument materializations.
The result permits either Bool or NoneType. -/
example : callHasBounds
    (.intersection (.callable .any booleanSource) (.callable .any noneSource)) .any
    (.union (.intersection booleanSource noneSource)
      (.intersection .any (.union booleanSource noneSource))) = true := by decide +kernel

/-- A static Bool argument can still select different requirements when their inputs contain any.
The result bounds permit Bool or NoneType. -/
example : callHasBounds
    (.intersection (.callable .any booleanSource) (.callable .any noneSource)) booleanSource
    (.union (.intersection booleanSource noneSource)
      (.intersection .any (.union booleanSource noneSource))) = true := by
  decide +kernel

/-- Both Bool input requirements apply to every accepted argument materialization.
Their result is Bool & NoneType even when the argument annotation is any. -/
example : callSourceTy? callTable
    (.intersection (.callable booleanSource booleanSource) (.callable booleanSource noneSource))
    .any callCore = some (.intersection booleanSource noneSource) := by
  decide +kernel

/-- Equivalent static inputs can have different syntax.
Bool and Object & Bool still require both results for an unknown argument. -/
example : callSourceTy? callTable
    (.intersection (.callable booleanSource booleanSource)
      (.callable (.intersection (.class_ objectClass) booleanSource) noneSource))
    .any callCore = some (.intersection booleanSource noneSource) := by
  decide +kernel

/-- A Bool result and an Object result remain possible.
Their approximation keeps a Bool lower bound, so a NoneType parameter rejects it. -/
example : (match callSourceTy? callTable
      (.intersection (.callable booleanSource booleanSource)
        (.callable noneSource (.class_ objectClass))) .any callCore with
    | none => false
    | some result =>
        let expected := GTy.union (.intersection booleanSource (.class_ objectClass))
          (.intersection .any (.union booleanSource (.class_ objectClass)))
        @decide (BoundsSubtype callTable callCore.toWellFormedClassHierarchy result expected ∧ BoundsSubtype callTable callCore.toWellFormedClassHierarchy expected result ∧
            AssignableTo callTable callCore.toWellFormedClassHierarchy result booleanSource ∧ ¬ AssignableTo callTable callCore.toWellFormedClassHierarchy result noneSource)
          (by
            haveI := boundsSubtypeDecidable result expected
            haveI := boundsSubtypeDecidable expected result
            haveI : Decidable (AssignableTo callTable callCore.toWellFormedClassHierarchy result booleanSource) :=
              callCore.subtypeDecidable (lowerBound result) (upperBound booleanSource)
            haveI : Decidable (AssignableTo callTable callCore.toWellFormedClassHierarchy result noneSource) :=
              callCore.subtypeDecidable (lowerBound result) (upperBound noneSource)
            infer_instance)) = true := by
  decide +kernel

/-- A requirement for Bool | NoneType applies whenever the Bool requirement applies.
The case results are Bool & NoneType and NoneType, so the result upper bound is NoneType. -/
example : (match callSourceTy? callTable
      (.intersection (.callable booleanSource booleanSource)
        (.callable (.union booleanSource noneSource) noneSource)) .any callCore with
    | none => false
    | some result => @decide
        (IsSubtype callCore.toWellFormedClassHierarchy (upperBound result) noneType ∧
          IsSubtype callCore.toWellFormedClassHierarchy noneType (upperBound result))
        (by
          haveI := callCore.subtypeDecidable (upperBound result) noneType
          haveI := callCore.subtypeDecidable noneType (upperBound result)
          infer_instance)) = true := by
  decide +kernel

/-- Two Bool requirements still apply together when a NoneType requirement occurs between them.
The result upper bound contains only Bool and NoneType. Object adds no possible result class. -/
example : (match callSourceTy? callTable
      (.intersection (.intersection (.callable booleanSource booleanSource)
        (.callable noneSource noneSource)) (.callable booleanSource (.class_ objectClass)))
      .any callCore with
    | none => false
    | some result => @decide
        (IsSubtype callCore.toWellFormedClassHierarchy (upperBound result) (.union booleanType noneType) ∧
          IsSubtype callCore.toWellFormedClassHierarchy (.union booleanType noneType) (upperBound result))
        (by
          haveI := callCore.subtypeDecidable (upperBound result) (.union booleanType noneType)
          haveI := callCore.subtypeDecidable (.union booleanType noneType) (upperBound result)
          infer_instance)) = true := by
  decide +kernel

/-- A callback with either signature fits the combined input. The result is Bool | NoneType. -/
example : callSourceTy? callTable (.intersection
      (.callable (.callable booleanSource .any) booleanSource)
      (.callable (.callable noneSource .any) noneSource)) (.union (.callable booleanSource booleanSource) (.callable noneSource noneSource))
    callCore =
    some (.union booleanSource noneSource) := by decide +kernel

/-- An unknown parameter selects Bool. The unrelated NoneType requirement does not change the result. -/
example : callSourceTy? callTable
    (.intersection (.callable .any booleanSource) (.callable noneSource noneSource))
    booleanSource callCore =
    some booleanSource := by decide +kernel

/-- A bottom alternative supplies no possible callee. The Bool function remains callable. -/
example : callSourceTy? callTable
    (.union (.callable booleanSource booleanSource) .bottom)
    booleanSource callCore =
    some booleanSource := by decide +kernel

/-- The order of a bottom alternative does not change the call result. -/
example : callSourceTy? callTable
    (.union .bottom (.callable booleanSource booleanSource))
    booleanSource callCore =
    some booleanSource := by decide +kernel

/-- A bottom callee cannot return a value. Its call has type bottom. -/
example : callSourceTy? callTable .bottom booleanSource
    callCore = some .bottom := by decide +kernel

example :
  CompileTargetPrecision
    (callParamCheckedTarget (.intersection (.class_ "C") (.class_ "Bar")))
    (callParamCheckedTarget (.intersection .any (.class_ "Bar"))) := by
  have hLeft :
      callParamCheckedTarget (.intersection (.class_ "C") (.class_ "Bar")) =
        .intersection (.class_ "Bar") (.class_ "C") := by
    decide +kernel
  rw [hLeft]
  rw [callParamCheckedTarget_intersection_any_left (.class_ "Bar")]
  exact CompileTargetPrecision.intersection_right_toAny
    (CompileTargetPrecision.refl (T := .class_ "Bar"))
    (CompileTargetPrecision.toAny (T := .class_ "C"))

/-! ## Bounds intervals and call acceptance -/

/-- MoreStatic is reflexive on valid annotations. -/
example (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (annotation : GTy) (valid : WellFormedGTy gct annotation) :
    MoreStatic gct structural annotation annotation :=
  moreStatic_refl gct structural annotation valid

/-- Enlarging both bounds intervals preserves acceptance of the call itself.
This does not compare the result types or later parameter checks. -/
example (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct)
    (callee₁ callee₂ argument₁ argument₂ result : GTy)
    (calleeChange : MoreStatic gct hwfct.toWellFormedClassHierarchy callee₁ callee₂)
    (argumentChange : MoreStatic gct hwfct.toWellFormedClassHierarchy argument₁ argument₂)
    (accepted : callSourceTy? gct callee₁ argument₁ hwfct = some result) :
    ∃ newResult, callSourceTy? gct callee₂ argument₂ hwfct = some newResult :=
  callSourceTy?_moreStatic hwfct calleeChange argumentChange accepted

/-- The first function requirement accepts Object. The second accepts Bool. -/
private abbrev overlapFunction : GTy :=
  .intersection (.callable (.class_ objectClass) booleanSource)
    (.callable booleanSource noneSource)

/-- With x : Bool, consume(f(x)) is accepted. f(x) has type Bool & NoneType. -/
example : GSrcInfer callTable callCore
    [⟨"f", overlapFunction⟩, ⟨"x", booleanSource⟩,
      ⟨"consume", .callable noneSource booleanSource⟩]
    (.call (.var "consume") (.call (.var "f") (.var "x"))) booleanSource := by
  refine .call (argSrcTy := .intersection booleanSource noneSource) (.var rfl) ?_ ?_
  · exact .call (.var rfl) (.var rfl) (by decide +kernel)
  · decide +kernel

/-- With x : any, f(x) permits the empty result or Bool.
Its lower bound is empty, so consume(f(x)) passes a NoneType parameter check. -/
example : GSrcInfer callTable callCore
    [⟨"f", overlapFunction⟩, ⟨"x", .any⟩, ⟨"consume", .callable noneSource booleanSource⟩]
    (.call (.var "consume") (.call (.var "f") (.var "x"))) booleanSource := by
  let result := (callSourceTy? callTable overlapFunction .any callCore).getD .any
  have selected : callSourceTy? callTable overlapFunction .any callCore = some result := by decide +kernel
  exact .call (.var rfl)
    (.call (.var rfl) (.var rfl) selected) (by decide +kernel)

/-- The unknown argument keeps a Bool upper bound and an empty lower bound. -/
example : callHasBounds overlapFunction .any (.intersection .any booleanSource) = true := by decide +kernel

/-- The Object input permits Bool or NoneType. The Bool input requires NoneType. -/
private abbrev nonemptyOverlapFunction : GTy :=
  .intersection (.callable (.class_ objectClass) (.union booleanSource noneSource))
    (.callable booleanSource noneSource)

/-- Both requirements apply to a Bool argument, so the result is NoneType. -/
example : callSourceTy? callTable nonemptyOverlapFunction booleanSource callCore = some noneSource := by
  decide +kernel

/-- An unknown argument permits the narrower NoneType result as well as Bool | NoneType. -/
example : callHasBounds nonemptyOverlapFunction .any
    (.union noneSource (.intersection .any (.union booleanSource noneSource))) = true := by decide +kernel

/-- The narrower NoneType result lets consume(f(x)) pass with x : any. -/
example : GSrcInfer callTable callCore
    [⟨"f", nonemptyOverlapFunction⟩, ⟨"x", .any⟩, ⟨"consume", .callable noneSource booleanSource⟩]
    (.call (.var "consume") (.call (.var "f") (.var "x"))) booleanSource := by
  let result := (callSourceTy? callTable nonemptyOverlapFunction .any callCore).getD .any
  have selected : callSourceTy? callTable nonemptyOverlapFunction .any callCore = some result := by decide +kernel
  exact .call (.var rfl)
    (.call (.var rfl) (.var rfl) selected) (by decide +kernel)

/-- Bool | NoneType needs both inputs when any is filled with Bool.
The combined result remains possible even though any can also accept the argument alone. -/
example : callHasBounds
    (.intersection (.callable .any booleanSource) (.callable noneSource noneSource))
    (.union booleanSource noneSource)
    (.union booleanSource (.intersection .any (.union booleanSource noneSource))) = true := by decide +kernel

/-! ## Semantic emptiness in source calls -/

/-- Bool & NoneType has no values. A call on it has result bottom. -/
example : callSourceTy? callTable (.intersection booleanSource noneSource) booleanSource
    callCore = some .bottom := by decide +kernel

/-- An empty class intersection stays empty inside a union with bottom. -/
example : callSourceTy? callTable
    (.union (.intersection booleanSource noneSource) .bottom)
    .any callCore = some .bottom := by decide +kernel

/-- A callee cannot be both Bool and a function. Its call also has result bottom. -/
example : callSourceTy? callTable
    (.intersection booleanSource (.callable booleanSource booleanSource))
    noneSource callCore = some .bottom := by decide +kernel

/-! ## Precision limits of calls -/

/-- Bool -> Bool with x : any gives Bool. The source checker rejects consume(f(x)) when consume requires NoneType. -/
example :
    let environment : SBindingEnv :=
      [⟨"f", .callable booleanSource booleanSource⟩, ⟨"x", .any⟩,
        ⟨"consume", .callable noneSource booleanSource⟩]
    Nonempty (GSrcInfer callTable callCore environment (.call (.var "f") (.var "x")) booleanSource) ∧
      ∀ result, GSrcInfer callTable callCore environment
        (.call (.var "consume") (.call (.var "f") (.var "x"))) result → False := by
  intro environment
  have argument : GSrcInfer callTable callCore environment (.call (.var "f") (.var "x")) booleanSource :=
    .call (.var rfl) (.var rfl) (by decide +kernel)
  refine ⟨⟨argument⟩, ?_⟩
  intro result inferred
  cases inferred with
  | call callee input accepted =>
      have consume : GSrcInfer callTable callCore environment (.var "consume")
          (.callable noneSource booleanSource) :=
        .var (b := ⟨"consume", .callable noneSource booleanSource⟩) rfl
      obtain rfl := gSrcInfer_principal_unique consume callee
      obtain rfl := gSrcInfer_principal_unique argument input
      have rejected : callSourceTy? callTable (.callable noneSource booleanSource)
          booleanSource callCore = none := by decide +kernel
      rw [rejected] at accepted
      cases accepted

/-- any -> Bool with True also gives Bool. Its result cannot be passed to consume when consume requires NoneType. -/
example :
    let environment : SBindingEnv :=
      [⟨"f", .callable .any booleanSource⟩, ⟨"consume", .callable noneSource booleanSource⟩]
    Nonempty (GSrcInfer callTable callCore environment (.call (.var "f") .constTrue) booleanSource) ∧
      ∀ result, GSrcInfer callTable callCore environment
        (.call (.var "consume") (.call (.var "f") .constTrue)) result → False := by
  intro environment
  have argument : GSrcInfer callTable callCore environment (.call (.var "f") .constTrue) booleanSource :=
    .call (.var rfl) .constTrue (by decide +kernel)
  refine ⟨⟨argument⟩, ?_⟩
  intro result inferred
  cases inferred with
  | call callee input accepted =>
      have consume : GSrcInfer callTable callCore environment (.var "consume")
          (.callable noneSource booleanSource) :=
        .var (b := ⟨"consume", .callable noneSource booleanSource⟩) rfl
      obtain rfl := gSrcInfer_principal_unique consume callee
      obtain rfl := gSrcInfer_principal_unique argument input
      have rejected : callSourceTy? callTable (.callable noneSource booleanSource)
          booleanSource callCore = none := by decide +kernel
      rw [rejected] at accepted
      cases accepted

/-- Unknown parts inside a callback parameter do not change the declared Bool result. -/
example : callSourceTy? callTable
    (.callable (.callable .any booleanSource) booleanSource) .any callCore = some booleanSource := by
  decide +kernel

/-- Unknown parts in the declared result remain part of that result. -/
example : callSourceTy? callTable
    (.callable .any (.callable .any booleanSource)) booleanSource callCore =
    some (.callable .any booleanSource) := by decide +kernel

/-- A function intersected with BoundMethod keeps Bool for an unknown argument. -/
example : callSourceTy? callTable
    (.intersection (.callable booleanSource booleanSource) (.class_ boundMethodClass))
    .any callCore = some booleanSource := by decide +kernel

/-- An unknown callee part can restrict the known Bool result.
The resulting type passes a NoneType parameter check, which requires a runtime check. -/
example : callSourceTy? callTable
    (.intersection (.callable (.class_ objectClass) booleanSource) .any)
    booleanSource callCore = some (.intersection booleanSource .any) ∧
      callSourceTy? callTable (.callable noneSource booleanSource)
        (.intersection booleanSource .any) callCore = some booleanSource := by
  constructor <;> decide +kernel

/-- The summary removes the empty union alternative. The call gives Bool. -/
example : callSourceTy? callTable
    (.union (.intersection booleanSource noneSource) (.callable booleanSource booleanSource))
    booleanSource callCore = some booleanSource := by decide +kernel

/-- The summary omits the noncallable Bool alternative with or without BoundMethod.
The BoundMethod constraint makes the full callee type callable on Bool. -/
example : callSourceTy? callTable
    (.intersection (.union booleanSource (.callable booleanSource booleanSource))
      (.class_ boundMethodClass)) booleanSource callCore = some booleanSource := by
  decide +kernel

/-- The static checker accepts the same call with result Bool. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.union
        (.intersection fixtureBoolValid fixtureNoneValid)
        (.callable fixtureBoolValid fixtureBoolValid)))
    (.call (.var "f") (.var "x")) booleanType = true := by decide +kernel

/-- The static checker rejects NoneType as the result of that call. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.union
        (.intersection fixtureBoolValid fixtureNoneValid)
        (.callable fixtureBoolValid fixtureBoolValid)))
    (.call (.var "f") (.var "x")) noneType = false := by decide +kernel

/-- BoundMethod with a bottom argument cannot return a value. Its result is bottom. -/
example : callSourceTy? callTable (.class_ boundMethodClass) .bottom callCore = some .bottom := by
  decide +kernel

/-- BoundMethod with an unknown argument is accepted through its empty lower bound. -/
example : callSourceTy? callTable (.class_ boundMethodClass) .any callCore = some .any := by
  decide +kernel

/-- BoundMethod alone supplies no input guarantee for a known Boolean argument. -/
example : callSourceTy? callTable (.class_ boundMethodClass) booleanSource callCore = none := by
  decide +kernel

/-! ## Additional source call results -/

/-- The function has a Bool input and a bottom input. -/
private abbrev bottomInputFunction : GTy :=
  .intersection (.callable booleanSource booleanSource) (.callable .bottom noneSource)

/-- Three requirements grouped with Bool and NoneType first. -/
private abbrev tripleFunctionLeft : GTy :=
  .intersection bothFunctions
    (.callable (.class_ boundMethodClass) (.class_ boundMethodClass))

/-- The same three requirements grouped with NoneType and BoundMethod first. -/
private abbrev tripleFunctionRight : GTy :=
  .intersection (.callable booleanSource booleanSource)
    (.intersection (.callable noneSource noneSource)
      (.callable (.class_ boundMethodClass) (.class_ boundMethodClass)))

/-- A bottom argument type selects both result requirements. The result type is `Bool & NoneType`. -/
example : callSourceTy? callTable
    bottomInputFunction
    .bottom callCore = some (.intersection (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- Either function alternative gives Bool for True. The bottom input requirements do not add NoneType to the result type. -/
example : callSourceTy? callTable
    (.union bottomInputFunction bottomInputFunction)
    (.class_ boolClass) callCore =
    some (.class_ boolClass) := by
  decide +kernel

/-- For a Bool input, one possible function returns Bool and the other returns NoneType. The result type excludes BoundMethod. -/
example : callSourceTy? callTable
    (.union
      (.intersection
        (.callable (.class_ boolClass) (.class_ boolClass))
        (.callable (.class_ noneClass) (.class_ noneClass)))
      (.intersection
        (.callable (.class_ boolClass) (.class_ noneClass))
        (.callable (.class_ boundMethodClass) (.class_ boundMethodClass))))
    (.class_ boolClass) callCore =
    some (.union (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- A bottom argument type selects all three requirements. This arrangement of parentheses gives a result type with no possible values. -/
example : (match callSourceTy? callTable tripleFunctionLeft .bottom
    callCore with
  | none => false
  | some result => @decide (BoundsSubtype callTable callCore.toWellFormedClassHierarchy result .bottom)
      (boundsSubtypeDecidable result .bottom)) = true := by
  decide +kernel

/-- A bottom argument type selects all three requirements. The other arrangement also gives a result type with no possible values. -/
example : (match callSourceTy? callTable
    tripleFunctionRight
    .bottom callCore with
  | none => false
  | some result => @decide (BoundsSubtype callTable callCore.toWellFormedClassHierarchy result .bottom)
      (boundsSubtypeDecidable result .bottom)) = true := by
  decide +kernel

/-- The checker gives `Bool | NoneType` for a `Bool | NoneType` argument. The parentheses group Bool and NoneType first. -/
example : callSourceTy? callTable
    tripleFunctionLeft
    (.union (.class_ boolClass) (.class_ noneClass)) callCore = some (.union (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- Adding `Object &` to the argument type does not add BoundMethod to the result type. The parentheses group Bool and NoneType first. -/
example : callSourceTy? callTable
    tripleFunctionLeft
    (.intersection (.class_ objectClass) (.union (.class_ boolClass) (.class_ noneClass))) callCore = some (.union (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- The checker gives `Bool | NoneType` for a `Bool | NoneType` argument. The parentheses group NoneType and BoundMethod first. -/
example : callSourceTy? callTable
    tripleFunctionRight
    (.union (.class_ boolClass) (.class_ noneClass)) callCore = some (.union (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- Adding `Object &` to the argument type does not add BoundMethod to the result type. The parentheses group NoneType and BoundMethod first. -/
example : callSourceTy? callTable
    tripleFunctionRight
    (.intersection (.class_ objectClass) (.union (.class_ boolClass) (.class_ noneClass))) callCore = some (.union (.class_ boolClass) (.class_ noneClass)) := by
  decide +kernel

/-- A Bool call with an unknown result type gives `any`. -/
example : callSourceTy? callTable
    (.callable (.class_ boolClass) .any)
    (.class_ boolClass) callCore = some .any := by
  decide +kernel

/-- Combining `any` and Object result requirements gives `any`. -/
example : callSourceTy? callTable
    (.intersection
      (.callable (.class_ boolClass) .any)
      (.callable (.class_ objectClass) (.class_ objectClass)))
    (.class_ boolClass) callCore = some .any := by
  decide +kernel

/-- Two unknown result requirements reduce to `any`. -/
example : callSourceTy? callTable
    (.intersection (.callable (.class_ boolClass) .any) (.callable (.class_ objectClass) .any))
    (.class_ boolClass) callCore = some .any := by
  decide +kernel

/-- The result keeps `any & Bool` when one requirement is unknown and the other requires Bool. -/
example : callSourceTy? callTable
    (.intersection
      (.callable (.class_ boolClass) .any)
      (.callable (.class_ boolClass) (.class_ boolClass)))
    (.class_ boolClass) callCore =
    some (.intersection .any (.class_ boolClass)) := by
  decide +kernel

/-- The unknown input can become Bool, which requires an empty result, or NoneType, which permits Bool.
The result has an empty lower bound and a Bool upper bound. -/
example : callHasBounds
    (.intersection (.callable .any (.class_ noneClass))
      (.callable (.class_ boolClass) (.class_ boolClass)))
    (.class_ boolClass) (.intersection .any (.class_ boolClass)) = true := by decide +kernel

/-- A function that requires NoneType accepts the result type `Bool & NoneType`. -/
example : callSourceTy? callTable
    (.callable (.class_ noneClass) (.class_ boolClass))
    (.intersection (.class_ boolClass) (.class_ noneClass)) callCore = some (.class_ boolClass) := by
  decide +kernel

/-! ## Unknown inputs in returned functions -/

/-- An unrelated NoneType requirement leaves the returned `any -> Bool` unchanged. -/
example : callSourceTy? callTable
    (.intersection (.callable booleanSource (.callable .any booleanSource))
      (.callable noneSource noneSource))
    booleanSource callCore = some (.callable .any booleanSource) := by
  decide +kernel

/-- Calling that returned function on True gives Bool, with no unknown result part. -/
example :
    (callSourceTy? callTable
      (.intersection (.callable booleanSource (.callable .any booleanSource))
        (.callable noneSource noneSource))
      booleanSource callCore).bind
        (fun result => callSourceTy? callTable result booleanSource callCore) = some booleanSource := by
  decide +kernel

/-- Source inference accepts `f(True)(True)` with result Bool.
The NoneType requirement on f does not apply to either call. -/
example : GSrcInfer callTable callCore
    [⟨"f", .intersection (.callable booleanSource (.callable .any booleanSource))
      (.callable noneSource noneSource)⟩]
    (.call (.call (.var "f") .constTrue) .constTrue) booleanSource := by
  exact .call
    (.call (R := .callable .any booleanSource) (.var rfl) .constTrue
      (by decide +kernel))
    .constTrue (by decide +kernel)

/-- Equal returned function requirements give one `any -> Bool` annotation.
The second call also gives Bool. -/
example :
    (callSourceTy? callTable
      (.intersection (.callable booleanSource (.callable .any booleanSource))
        (.callable booleanSource (.callable .any booleanSource)))
      booleanSource callCore).bind
        (fun result => callSourceTy? callTable result booleanSource callCore) = some booleanSource := by
  decide +kernel

/-- Both function requirements apply to True.
Their results stay in one intersection, including the combined result requirement. -/
example : callSourceTy? callTable
    (.intersection (.callable booleanSource (.callable .any booleanSource))
      (.callable booleanSource (.callable .any (.class_ objectClass))))
    booleanSource callCore =
      some (.intersection (.callable .any booleanSource)
        (.intersection (.callable .any (.class_ objectClass))
          (.union (.callable .any booleanSource) (.callable .any (.class_ objectClass))))) := by
  decide +kernel

/-- Calling the returned function on True permits Bool or Object results.
The inferred type has lower bound Bool and upper bound Object. -/
example :
    (callSourceTy? callTable
      (.intersection (.callable booleanSource (.callable .any booleanSource))
        (.callable booleanSource (.callable .any (.class_ objectClass))))
      booleanSource callCore).bind
        (fun result => callSourceTy? callTable result booleanSource callCore) =
      some (.union (.intersection booleanSource (.class_ objectClass))
        (.intersection .any (.union booleanSource (.class_ objectClass)))) := by
  decide +kernel

/-- An unknown argument retains the Bool, NoneType, and combined-input cases.
The alternative result includes `Bool -> Object`; it does not reduce to `any -> Bool`. -/
example :
    let first := GTy.callable .any booleanSource
    let second := GTy.callable booleanSource (.class_ objectClass)
    let combined := GTy.union first second
    let boolCase := GTy.intersection first combined
    let noneCase := GTy.intersection second combined
    callSourceTy? callTable
      (.intersection (.callable booleanSource first) (.callable noneSource second))
      .any callCore = some
        (.union (.intersection boolCase (.intersection noneCase combined))
          (.intersection .any (.union boolCase (.union noneCase combined)))) := by
  decide +kernel

/-- Three first-call requirements include the same returned function twice.
Calling the inferred result on True completes and retains the Bool and NoneType cases. -/
example :
    let returnedBool := GTy.callable .any booleanSource
    let boolCase := GTy.union booleanSource .any
    let noneCase := GTy.union noneSource .any
    (callSourceTy? callTable
      (.intersection (.intersection (.callable booleanSource returnedBool)
        (.callable noneSource returnedBool)) (.callable .any (.callable .any noneSource)))
      .any callCore).bind
        (fun result => callSourceTy? callTable result booleanSource callCore) =
      some (.union (.intersection boolCase noneCase)
        (.intersection .any (.union boolCase noneCase))) := by
  decide +kernel

/-- Materializing the returned inputs as NoneType and Bool permits an Object result on True.
This is the result that keeping only `any -> Bool` would omit. -/
example : callSourceTy? callTable
    (.intersection (.callable noneSource booleanSource)
      (.callable booleanSource (.class_ objectClass)))
    booleanSource callCore = some (.class_ objectClass) := by
  decide +kernel

/-- A union containing Bool is not callable on a Bool argument.
Its function alternative alone cannot justify accepting the full union. -/
example : callSourceTy? callTable
    (.union booleanSource (.callable booleanSource booleanSource))
    booleanSource callCore = none := by
  decide +kernel

import FwPython.Gradual
import FwPython.Examples.Static.Subtyping

/-! # Translating and checking a method call

The program creates C and calls `m(True)`. The method returns its Bool argument.
The examples construct the translation proofs and apply the no-blame theorem.
-/

namespace FwPython.Examples.Gradual.MethodEmbedding

open FwPython.Examples.Static.Subtyping

/-- The method returns its argument without changing it. -/
private def identityMethod : Method :=
  { name := "m", receiverParam := "self", param := "x", paramTy := booleanType,
    returnTy := booleanType, body := .var "x" }

/-- C inherits Object and defines the identity method. -/
private def userClass : Class := ⟨"C", [], [identityMethod]⟩

/-- The four builtin classes and C. -/
private def classes : ClassTable := fixtureTable none ++ [userClass]

/-- Each declaration has Object as its implicit parent, except Object itself. -/
private theorem noBases (member : declaration ∈ classes) : declaration.baseClasses = [] := by
  simp [classes, fixtureTable] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The class table has an MRO for each class and respects the sealed builtins. -/
private def structureProof : WellFormedClassHierarchy classes := by
  have objectLookup : findClass classes objectClass = some (fixtureClass objectClass) := rfl
  let allMros : ∀ name declaration, findClass classes name = some declaration →
      ClassMroWitness classes declaration :=
    fun _ declaration lookup => fixtureMro objectLookup declaration (noBases (findClass_mem lookup))
  refine {
    objectExists := ⟨fixtureClass objectClass, objectLookup, rfl⟩
    boolExists := ⟨fixtureClass boolClass, [boolClass, objectClass], rfl, (allMros boolClass _ rfl).hmro⟩
    noneExists := ⟨fixtureClass noneClass, [noneClass, objectClass], rfl, (allMros noneClass _ rfl).hmro⟩
    boundMethodExists := ⟨fixtureClass boundMethodClass, [boundMethodClass, objectClass], rfl, (allMros boundMethodClass _ rfl).hmro⟩
    allMrosExist := allMros
    sealedLeaf := fixtureSealedLeaf objectLookup noBases }

/-- Every selected method is m from C. -/
private theorem onlyMethod (lookup : findClass classes name = some declaration)
    (member : method ∈ declaration.methods) : method = identityMethod := by
  have selected := findClass_mem lookup
  simp [classes, fixtureTable] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [fixtureClass, userClass, List.mem_singleton, List.not_mem_nil] at member
  exact member

/-- The identity method typechecks, and all method signatures use valid class names. -/
private def wellFormed : WellTypedClassHierarchy classes := by
  have booleanValid : WellFormedTy classes booleanType :=
    WellFormedTy.bool structureProof
  refine {
    toWellFormedClassHierarchy := structureProof
    allMethodsWellTyped := ?_
    liskovCondition := ?_
    allMethodNamesDistinct := ?_
    allMethodSignaturesWellFormed := ?_
    classNamesUnique := ?_
    baseClassesDistinct := ?_ }
  · intro name declaration method lookup member
    cases onlyMethod lookup member
    exact .var rfl
  · intro name ancestor declaration ancestorDeclaration mro ancestorMro methodName method ancestorMethod
      _ _ _ _ _ found ancestorFound
    obtain ⟨owner, ownerDeclaration, _, ownerLookup, methodMember⟩ := findMethodInMro_provenance found
    obtain ⟨ancestorOwner, ancestorOwnerDeclaration, _, ancestorOwnerLookup, ancestorMember⟩ :=
      findMethodInMro_provenance ancestorFound
    cases onlyMethod ownerLookup methodMember
    cases onlyMethod ancestorOwnerLookup ancestorMember
    exact ⟨.refl booleanValid, .refl booleanValid⟩
  · intro name declaration lookup
    have selected := findClass_mem lookup
    simp [classes, fixtureTable] at selected
    rcases selected with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro name declaration method lookup member
    cases onlyMethod lookup member
    exact ⟨booleanValid, booleanValid⟩
  · intro first second firstMember secondMember sameName
    simp [classes, fixtureTable] at firstMember secondMember
    rcases firstMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMember with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [fixtureClass, userClass, objectClass, boolClass, noneClass, boundMethodClass]
  · intro name declaration lookup
    simp [noBases (findClass_mem lookup)]

/-- Bool method parameters and results are permitted runtime check targets. -/
private def embedding : EmbeddableStaticClassTable classes where
  hwf := wellFormed
  methodSigChecked := by
    intro name declaration method lookup member
    cases onlyMethod lookup member
    exact ⟨.classFormula .class_, .classFormula .class_⟩

/-- The gradual class table proof obtained by translating the static table. -/
private abbrev core := wellFormedGClassTableCore_embedClassTable embedding

/-- Create C and call its identity method with True. -/
private def program : Program :=
  { classes := classes, main := .call (.attrAccess (.new "C") "m") .constTrue }

/-- The program main expression and method body have explicit translation proofs. -/
private def bridge : BridgeableStaticProgram program := by
  let booleanValid := WellFormedTy.bool wellFormed.toWellFormedClassHierarchy
  let classValid : WellFormedTy classes (.class_ "C") :=
    WellFormedTy.class_of_lookup (declaration := userClass) rfl
  let newInference : GSrcInfer (embedClassTable classes) core [] (.new "C") (.class_ "C") :=
    .new (findGClass_embedClassTable (ct := classes) (c := userClass) rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  let newBridge : EmbeddedExprBridgeCore classes core [] (.new "C") (.class_ "C")
      (.class_ "C") newInference (.class_ "C") :=
    .new rfl (findGClass_embedClassTable (ct := classes) (c := userClass) rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (.refl classValid)
  let methodSelection : FindMethodType classes "C" "m" booleanType booleanType :=
    ⟨userClass, ["C", objectClass], identityMethod, rfl,
      (fixtureMro (table := classes) rfl userClass rfl).hmro, rfl, rfl, rfl⟩
  have attributeResult : attrSourceTy? (embedClassTable classes) (.class_ "C") "m" =
      some (.callable (.class_ boolClass) (.class_ boolClass)) := by
    have selected : FindGMethodType (embedClassTable classes) "C" "m"
        (.class_ boolClass) (.class_ boolClass) :=
      ⟨embedClass userClass, ["C", objectClass], embedMethod identityMethod,
        findGClass_embedClassTable (ct := classes) (c := userClass) rfl,
        computeGMro_embedClassTable (fixtureMro (table := classes) rfl userClass rfl).hmro,
        findGMethodInMro_embed (ct := classes) (m := identityMethod) rfl, rfl, rfl⟩
    simp only [attrSourceTy?, lookupMethodTy?_of_find selected]
  let attributeInference := GSrcInfer.attrAccess newInference attributeResult
  let attributeBridge : EmbeddedExprBridgeCore classes core [] (.attrAccess (.new "C") "m")
      (.callable booleanType booleanType) (.callable (.class_ boolClass) (.class_ boolClass))
      attributeInference (.callable booleanType booleanType) :=
    .attrAccess (ct := classes) (hwfct := core) (Γ := []) (base := .new "C") newInference newBridge (.class_ methodSelection)
      attributeResult .embed (.refl (.callable booleanValid booleanValid))
  let literalBridge : EmbeddedExprBridgeCore classes core [] .constTrue booleanType
      (.class_ boolClass) .constTrue booleanType :=
    .constTrue (.refl booleanValid)
  have callResult : callSourceTy? (embedClassTable classes)
      (.callable (.class_ boolClass) (.class_ boolClass))
      (.class_ boolClass) core = some (.class_ boolClass) := by
    decide +kernel
  exact {
    classTable := embedding
    mainTy := booleanType
    core := core
    mainBridge := {
      producerTy := booleanType
      srcTy := .class_ boolClass
      hsrc := .call attributeInference .constTrue callResult
      core := .call (ct := classes) (hwfct := core) (Γ := []) (callee := .attrAccess (.new "C") "m") (arg := .constTrue)
        attributeInference attributeBridge .constTrue literalBridge
        .callable (.refl booleanValid) callResult
        .embed (.refl booleanValid) }
    methodBodiesBridge := by
      intro name declaration method lookup member
      cases onlyMethod lookup member
      exact {
        producerTy := booleanType
        srcTy := .class_ boolClass
        hsrc := GSrcInfer.var (gct := embedClassTable classes) (hwfct := core)
          (embedTyEnv_lookupBinding (Γ := [("x", booleanType), ("self", .class_ name)])
            (x := "x") (T := booleanType) rfl)
        core := .var (ct := classes) (hwfct := core)
          (Γ := [("x", booleanType), ("self", .class_ name)]) (x := "x")
          rfl (.refl booleanValid) } }

/-- Translation of the method call supplies the exact compiler and method-body proofs. -/
private def elaboration : EmbeddedStaticElaboration program := embedded_static_program_elaborates bridge

/-- Every terminating checked execution of this method-call program returns a value. -/
example (steps : Checked.Steps (embedClassTable program.classes) elaboration.cp.classes
    (Checked.initialState elaboration.cp) finalState)
    (final : Checked.finalResult? finalState = some (heap, result)) :
    ∃ value, result = CheckedResult.success value :=
  embedded_static_success elaboration steps final

/-- The compiled method call terminates and returns True. -/
example : ∃ finalState,
    Checked.Steps (embedClassTable program.classes) elaboration.cp.classes
      (Checked.initialState elaboration.cp) finalState ∧
    Checked.finalResult? finalState = some (finalState.heap, CheckedResult.success (.objRef trueOid)) := by
  have classMro := computeGMro_embedClassTable (fixtureMro (table := classes) rfl userClass rfl).hmro
  have booleanMro := computeGMro_embedClassTable
    (fixtureMro (table := classes) rfl (fixtureClass boolClass) rfl).hmro
  let checkedMethod := compileEmbeddedMethod program core "C" identityMethod
    (bridge.methodBodiesBridge "C" userClass identityMethod rfl (by simp [userClass])).hsrc
  let receiverHeap := (CheckedHeap.initial.alloc ⟨"C", .ordinary⟩).2
  let finalHeap := (receiverHeap.alloc ⟨boundMethodClass, .boundMethod 3 checkedMethod⟩).2
  refine ⟨{ heap := finalHeap, env := [], control := .val (.objRef trueOid), continuation := [] }, ?_, rfl⟩
  repeat first
      | refine RuntimeSteps.step Checked.Step.focusCall ?_
      | refine RuntimeSteps.step Checked.Step.focusEnforce ?_
      | refine RuntimeSteps.step Checked.Step.focusDynAttrAccess ?_
      | refine RuntimeSteps.step Checked.Step.constTrue ?_
      | refine RuntimeSteps.step (Checked.Step.newSuccess (c := embedClass userClass) rfl
          (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl) ?_
      | refine RuntimeSteps.step (Checked.Step.returnEnforceOk EnforceValue.unknown) ?_
      | refine RuntimeSteps.step (Checked.Step.returnEnforceOk
          (EnforceValue.classObjRefOk rfl rfl classMro (by decide +kernel))) ?_
      | refine RuntimeSteps.step (Checked.Step.returnEnforceOk
          (EnforceValue.classObjRefOk rfl rfl booleanMro (by decide +kernel))) ?_
      | refine RuntimeSteps.step (Checked.Step.returnEnforceOk
          (EnforceValue.callableObjRefTransparentOk rfl)) ?_
      | refine RuntimeSteps.step (Checked.Step.returnDynAttrAccess rfl rfl classMro rfl rfl) ?_
      | refine RuntimeSteps.step (Checked.Step.returnCallCalleeBound rfl) ?_
      | refine RuntimeSteps.step (Checked.Step.returnAwaitArgumentOk
          (EnforceValue.classObjRefOk rfl rfl booleanMro (by decide +kernel))) ?_
      | refine RuntimeSteps.step (Checked.Step.varSuccess rfl) ?_
      | refine RuntimeSteps.step Checked.Step.returnFromBody ?_
  exact RuntimeSteps.refl

end FwPython.Examples.Gradual.MethodEmbedding

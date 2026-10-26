import FwPython.Gradual
import FwPython.Examples.Static.Subtyping

open FwPython.Static.Subtyping

/-! # Tests for translation of static programs

Translation preserves the static subtype relation.
The theorem that runtime checks do not reject a translated program requires
`EmbeddedStaticElaboration`. This record contains the translation and its typing proofs. -/

example
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T₁ T₂ : Ty) :
    GradualSubtype gct structural (embedTy T₁) (embedTy T₂) ↔
      IsSubtype structural T₁ T₂ :=
  embedTy_gradualSubtype_iff gct structural T₁ T₂

example (s : Ty) : lowerBound (embedTy s) = s :=
  embedTy_lowerBound s

example (s : Ty) : upperBound (embedTy s) = s :=
  embedTy_upperBound s

example (ct : ClassTable) (structural : WellFormedClassHierarchy ct) (P Q R S : Ty) :
    CallSelection structural
      (.intersection (.callable P R) (.callable Q S))
      (.union P Q)
      (.union R S) :=
  CallSelection.inter_correlated .callable .callable

example (ct : ClassTable) (structural : WellFormedClassHierarchy ct) (P Q R S : Ty)
    (validP : WellFormedTy ct P) (validQ : WellFormedTy ct Q)
    (validR : WellFormedTy ct R) (validS : WellFormedTy ct S) :
    IsSubtype structural
      (.intersection (.callable P R) (.callable Q S))
      (.callable (.union P Q) (.union R S)) :=
  callSelection_subtype_callable (.inter_correlated .callable .callable)
    (.intersection (.callable validP validR) (.callable validQ validS)) (.union validP validQ)

open FwPython.Examples.Static.Subtyping in
/-- Lookup selects the first declaration for each builtin name. Later method declarations do not affect the result. -/
private def fixtureErasedStructure (shadow : Option (List Method)) :
    WellFormedClassHierarchy (eraseClassTable (embedClassTable (fixtureTable shadow))) := by
  cases shadow with
  | none => exact fixtureStructure none
  | some methods =>
      simpa [fixtureTable, fixtureClass, eraseClassTable, embedClassTable,
        eraseClass, embedClass, List.map_map, Function.comp_def] using
        fixtureStructure (some (methods.map (fun method => eraseMethod (embedMethod method))))

open FwPython.Examples.Static.Subtyping in
/-- Translation preserves the selected class names and their ancestors when a class name occurs twice. -/
example :
    classContextOf (fixtureTable (some []))
        (wellFormedClassHierarchy_eraseEmbed_reverse (fixtureErasedStructure (some []))) =
      classContextOf (eraseClassTable (embedClassTable (fixtureTable (some []))))
        (fixtureErasedStructure (some [])) :=
  classContextOf_eraseEmbed_reverse _

open FwPython.Examples.Static.Subtyping in
/-- Translation preserves the selected classes and their ancestors when a later declaration contains different methods. -/
example (method : Method) :
    classContextOf (fixtureTable (some [method]))
        (wellFormedClassHierarchy_eraseEmbed_reverse (fixtureErasedStructure (some [method]))) =
      classContextOf (eraseClassTable (embedClassTable (fixtureTable (some [method]))))
        (fixtureErasedStructure (some [method])) :=
  classContextOf_eraseEmbed_reverse _

open FwPython.Examples.Static.Subtyping in
/-- The original and translated tables give the same selected classes and ancestors. -/
example (method : Method) :
    classContextOf (fixtureTable (some [method]))
        (wellFormedClassHierarchy_eraseEmbed_reverse (fixtureErasedStructure (some [method]))) =
      classContextOf (fixtureTable (some [method])) (fixtureStructure (some [method])) :=
  congrArg (classContextOf (fixtureTable (some [method]))) (Subsingleton.elim _ _)

open FwPython.Examples.Static.Subtyping in
/-- This program declares the four builtin classes and returns True. -/
private def literalProgram : Program := { classes := fixtureTable none, main := .constTrue }

open FwPython.Examples.Static.Subtyping in
/-- The program's selected classes contain no methods. -/
private theorem literalProgram_method_impossible
    (lookup : findClass literalProgram.classes name = some declaration)
    (member : method ∈ declaration.methods) : False := by
  have selected := findClass_mem lookup
  simp [literalProgram, fixtureTable] at selected
  rcases selected with rfl | rfl | rfl | rfl <;> cases member

open FwPython.Examples.Static.Subtyping in
/-- This constructs the typing proofs required to translate the True program. -/
private def literalProgram_bridge : BridgeableStaticProgram literalProgram := by
  let classes : EmbeddableStaticClassTable literalProgram.classes := {
    hwf := fixtureWellFormed
    methodSigChecked := fun _ _ _ lookup member =>
      (literalProgram_method_impossible lookup member).elim }
  let core := wellFormedGClassTableCore_embedClassTable classes
  exact {
    classTable := classes
    mainTy := booleanType
    core := core
    mainBridge := {
      producerTy := booleanType
      srcTy := .class_ boolClass
      hsrc := .constTrue
      core := .constTrue (.refl fixtureBoolValid) }
    methodBodiesBridge := fun _ _ _ lookup member =>
      (literalProgram_method_impossible lookup member).elim }

/-- Compiling the True program supplies the proof data required by the theorem that runtime checks do not reject it. -/
example : EmbeddedStaticElaboration literalProgram :=
  embedded_static_program_elaborates literalProgram_bridge

/-! ## A Boolean result passed to a function that requires Boolean -/

open FwPython.Examples.Static.Subtyping

/-- Translating a valid type from the builtin fixture gives a valid gradual annotation. -/
private theorem fixtureEmbeddedValid (valid : WellFormedTy (fixtureTable none) T) :
    WellFormedGTy (embedClassTable (fixtureTable none)) (embedTy T) :=
  wellFormedGTy_embedTy fixtureWellFormed.toWellFormedClassHierarchy valid

/-- The function has types `Bool -> Bool` and `bottom -> NoneType`. -/
private abbrev precisionCallee : Ty :=
  .intersection (.callable booleanType booleanType) (.callable .bottom noneType)

/-- The variables `f` and `consume` have the types used by this test. -/
private abbrev precisionEnvironment : TyEnv :=
  [("consume", .callable booleanType booleanType), ("f", precisionCallee)]

/-- Pass `f(True)` to `consume`, which requires Bool. -/
private abbrev precisionExpression : Expr := .call (.var "consume") (.call (.var "f") .constTrue)

/-- The builtin class table satisfies the required typing and inheritance rules. -/
private abbrev precisionCore := literalProgram_bridge.core

/-- The class names in both function types are valid. -/
private theorem precisionCallee_wellFormed : WellFormedTy literalProgram.classes precisionCallee :=
  .intersection
    (.callable fixtureBoolValid fixtureBoolValid)
    (.callable .bottom fixtureNoneValid)

/-- Calling `f` on True has result type Bool. -/
private theorem precisionInner_result :
    callSourceTy? (embedClassTable literalProgram.classes) (embedTy precisionCallee) (.class_ boolClass)
      precisionCore = some (.class_ boolClass) := by
  decide +kernel

/-- This constructs the proofs that connect the static and gradual types of `f(True)`. -/
private abbrev precisionInner_bridge :
    EmbeddedExprBridge literalProgram.classes precisionCore precisionEnvironment
      (.call (.var "f") .constTrue) booleanType := by
  let calleeInference : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv precisionEnvironment) (.var "f") (embedTy precisionCallee) :=
    .var (embedTyEnv_lookupBinding (Γ := precisionEnvironment) (x := "f") (T := precisionCallee) rfl)
  let calleeBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore
      precisionEnvironment (.var "f") precisionCallee (embedTy precisionCallee)
      calleeInference precisionCallee :=
    .var rfl (.refl precisionCallee_wellFormed)
  let literalBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore
      precisionEnvironment .constTrue booleanType (.class_ boolClass) .constTrue booleanType :=
    .constTrue (.refl fixtureBoolValid)
  exact {
    producerTy := booleanType
    srcTy := .class_ boolClass
    hsrc := .call calleeInference .constTrue precisionInner_result
    core := .call (callee := .var "f") (arg := .constTrue) calleeInference calleeBridge .constTrue literalBridge
      (.inter_left .callable) (.refl fixtureBoolValid) precisionInner_result .embed
      (.refl fixtureBoolValid) }

/-- This constructs the translation proofs for `consume(f(True))`. -/
private abbrev precisionNested_bridge :
    EmbeddedExprBridge literalProgram.classes precisionCore precisionEnvironment precisionExpression booleanType := by
  let consumerWf : WellFormedTy literalProgram.classes (.callable booleanType booleanType) :=
    .callable fixtureBoolValid fixtureBoolValid
  let consumerInference : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv precisionEnvironment) (.var "consume") (embedTy (.callable booleanType booleanType)) :=
    .var (embedTyEnv_lookupBinding (Γ := precisionEnvironment) (x := "consume") (T := .callable booleanType booleanType) rfl)
  let consumerBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore precisionEnvironment
      (.var "consume") (.callable booleanType booleanType) (embedTy (.callable booleanType booleanType))
      consumerInference (.callable booleanType booleanType) :=
    .var rfl (.refl consumerWf)
  have result : callSourceTy? (embedClassTable literalProgram.classes)
      (embedTy (.callable booleanType booleanType))
      (.class_ boolClass) precisionCore = some (.class_ boolClass) :=
    by decide +kernel
  exact {
    producerTy := booleanType
    srcTy := .class_ boolClass
    hsrc := .call consumerInference precisionInner_bridge.hsrc result
    core := .call (callee := .var "consume") (arg := .call (.var "f") .constTrue) consumerInference consumerBridge precisionInner_bridge.hsrc precisionInner_bridge.core
      .callable (.refl fixtureBoolValid) result .embed
      (.refl fixtureBoolValid) }

/-- The source checker accepts `consume(f(True))` and gives it type Bool. -/
example : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
    (embedTyEnv precisionEnvironment) (embedExpr precisionExpression) (.class_ boolClass) :=
  precisionNested_bridge.hsrc

/-- The compiled environment assigns `any` to `f`. Its two function types are not an allowed type for a runtime check. -/
private abbrev precisionCheckedEnvironment : GTyEnv :=
  [("consume", .callable (.class_ boolClass) (.class_ boolClass)), ("f", .any)]

/-- The compiled variable types satisfy the translation requirements. -/
private theorem precisionCheckedEnvironment_ok :
    ElabEnvOk (embedClassTable literalProgram.classes) precisionCore.toWellFormedClassHierarchy (embedTyEnv precisionEnvironment) precisionCheckedEnvironment :=
  .cons ⟨rfl, .callable (.classFormula .class_) (.classFormula .class_),
      fixtureEmbeddedValid (.callable fixtureBoolValid fixtureBoolValid),
      .refl (.callable fixtureBoolValid fixtureBoolValid)⟩
    (.cons ⟨rfl, .classFormula .any, .any, IsSubtype.objectTop precisionCallee_wellFormed⟩ .nil)

/-- The compiled `consume(f(True))` expression has type Bool. -/
example (site : SourceExpressionSite) :
    CheckedHasType (embedClassTable literalProgram.classes) precisionCore.toWellFormedClassHierarchy precisionCheckedEnvironment
      (compileCheck precisionNested_bridge.hsrc precisionCheckedEnvironment (.class_ boolClass) site)
      (.class_ boolClass) :=
  compileCheck_checked precisionCore precisionCheckedEnvironment_ok
    (.classFormula .class_) (fixtureEmbeddedValid fixtureBoolValid)
    precisionNested_bridge.hsrc site

/-! ## A source result with two function requirements -/

/-- The returned function must accept Bool with a Bool result and NoneType with a NoneType result. -/
private abbrev returnedFunctionRequirements : Ty :=
  .intersection (.callable booleanType booleanType) (.callable noneType noneType)

/-- The source function returns a function with both requirements when given Bool. -/
private abbrev functionReturningTwoRequirements : Ty :=
  .callable booleanType returnedFunctionRequirements

/-- Calling `f(True)` compiles even when its inferred function result cannot be a runtime target.
The checked environment gives `f` type `any`, and the call is compiled at target `any`. -/
example (site : SourceExpressionSite) :
    ∃ sourceTyping : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
        (embedTyEnv [("f", functionReturningTwoRequirements)])
        (.call (.var "f") .constTrue) (embedTy returnedFunctionRequirements),
      ¬ CheckedTargetTy (embedClassTable literalProgram.classes) (embedTy returnedFunctionRequirements) ∧
      CheckedHasType (embedClassTable literalProgram.classes) precisionCore.toWellFormedClassHierarchy
        [("f", .any)] (compileCheck sourceTyping [("f", .any)] .any site) .any := by
  let sourceTyping : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv [("f", functionReturningTwoRequirements)])
      (.call (.var "f") .constTrue) (embedTy returnedFunctionRequirements) :=
    .call (.var rfl) .constTrue (by decide +kernel)
  have resultCannotBeChecked :
      ¬ CheckedTargetTy (embedClassTable literalProgram.classes) (embedTy returnedFunctionRequirements) := by
    intro runtimeTarget
    cases runtimeTarget with
    | classFormula formula =>
        cases formula with
        | intersection left _ => cases left
    | interCallableLeft _ _ compatible => cases compatible.1
    | interCallableRight compatible _ _ => cases compatible.1
  have environmentOk : ElabEnvOk (embedClassTable literalProgram.classes)
      precisionCore.toWellFormedClassHierarchy
      (embedTyEnv [("f", functionReturningTwoRequirements)]) [("f", .any)] :=
    .cons ⟨rfl, .classFormula .any, .any, IsSubtype.objectTop
      (.callable fixtureBoolValid
        (.intersection (.callable fixtureBoolValid fixtureBoolValid)
          (.callable fixtureNoneValid fixtureNoneValid)))⟩ .nil
  refine ⟨sourceTyping, resultCannotBeChecked, ?_⟩
  exact compileCheck_checked precisionCore environmentOk
    (.classFormula .any) .any sourceTyping site

/-! ## A result that satisfies two requirements -/

/-- Both result types include Bool. One also includes NoneType; the other also includes BoundMethod. -/
private abbrev precisionSharedReturn : Ty :=
  .intersection (.union booleanType noneType) (.union booleanType methodType)

/-- A Bool argument fits both parameter types. -/
private abbrev precisionSharedCallee : Ty :=
  .intersection (.callable booleanType (.union booleanType noneType))
    (.callable objectType (.union booleanType methodType))

/-- This constructs the translation proofs for a result that must satisfy both result types. -/
example : EmbeddedExprBridge literalProgram.classes precisionCore [("f", precisionSharedCallee)]
    (.call (.var "f") .constTrue) precisionSharedReturn := by
  let returnWf : WellFormedTy literalProgram.classes precisionSharedReturn := .intersection
    (.union fixtureBoolValid fixtureNoneValid) (.union fixtureBoolValid fixtureMethodValid)
  let calleeWf : WellFormedTy literalProgram.classes precisionSharedCallee :=
    .intersection (.callable fixtureBoolValid (.union fixtureBoolValid fixtureNoneValid))
      (.callable fixtureObjectValid (.union fixtureBoolValid fixtureMethodValid))
  let calleeInference : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv [("f", precisionSharedCallee)]) (.var "f") (embedTy precisionSharedCallee) :=
    .var (embedTyEnv_lookupBinding (Γ := [("f", precisionSharedCallee)]) (x := "f") (T := precisionSharedCallee) rfl)
  let calleeBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore
      [("f", precisionSharedCallee)] (.var "f") precisionSharedCallee (embedTy precisionSharedCallee)
      calleeInference precisionSharedCallee :=
    .var rfl (.refl calleeWf)
  let literalBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore
      [("f", precisionSharedCallee)] .constTrue booleanType (.class_ boolClass) .constTrue booleanType :=
    .constTrue (.refl fixtureBoolValid)
  let selection : CallSelection precisionCore.toOriginalWellFormedClassHierarchy precisionSharedCallee
      (.intersection booleanType objectType) precisionSharedReturn :=
    .inter_shared (.inter_left .callable) (.inter_right .callable)
  have argumentSubtype : IsSubtype precisionCore.toOriginalWellFormedClassHierarchy booleanType (.intersection booleanType objectType) :=
    .interIntro (.refl fixtureBoolValid) (.objectTop fixtureBoolValid)
  have result : callSourceTy? (embedClassTable literalProgram.classes)
      (embedTy precisionSharedCallee)
      (.class_ boolClass) precisionCore = some (embedTy precisionSharedReturn) := by
    decide +kernel
  exact {
    producerTy := precisionSharedReturn
    srcTy := embedTy precisionSharedReturn
    hsrc := .call calleeInference .constTrue result
    core := .call (callee := .var "f") (arg := .constTrue) calleeInference calleeBridge .constTrue literalBridge
      selection argumentSubtype result .embed
      (.refl returnWf) }

/-- An input of type `P & Q` uses both result requirements. The result must have types R and S. -/
example (ct : ClassTable) (structural : WellFormedClassHierarchy ct) (P Q R S : Ty)
    (validP : WellFormedTy ct P) (validQ : WellFormedTy ct Q)
    (validR : WellFormedTy ct R) (validS : WellFormedTy ct S) :
    IsSubtype structural (.intersection (.callable P R) (.callable Q S))
      (.callable (.intersection P Q) (.intersection R S)) :=
  callSelection_subtype_callable (.inter_shared (.inter_left .callable) (.inter_right .callable))
    (.intersection (.callable validP validR) (.callable validQ validS)) (.intersection validP validQ)

example (ct : ClassTable) (R S : Ty) :
    CoreViewOnSrc ct (.intersection R S) (embedTy (.intersection R S)) :=
  CoreViewOnSrc.embed

example
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (value : CheckedValue)
    (T : Ty)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy T))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy .any) :=
  coreViewOnSrc_satisfies (CoreViewOnSrc.any (T := T)) hsat

example
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (value : CheckedValue)
    (T : Ty)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy T))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy (embedTy T)) :=
  coreViewOnSrc_satisfies .embed hsat

example
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (value : CheckedValue)
    (T U : Ty)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy (.union T U)))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy (.union (embedTy T) (embedTy U))) :=
  coreViewOnSrc_satisfies (.union .embed .embed) hsat

example
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (value : CheckedValue)
    (T : Ty)
    (hsat :
      CheckedValueSatisfies (embedClassTable ct) cct heap value
        (checkedTargetOfGTy (embedTy (.intersection T T)))) :
    CheckedValueSatisfies (embedClassTable ct) cct heap value
      (checkedTargetOfGTy (embedTy T)) :=
  coreViewOnSrc_satisfies (.interIntro .embed .embed) hsat

example
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState =
      some (heap', CheckedResult.blame info)) :
    Checked.CauseSatisfiesObligation
      (embedClassTable p.classes)
      helab.cp.classes
      heap'
      info.cause
      info.obligation :=
  embedded_static_final_blame_satisfies_obligation helab hsteps hfinal

example
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState =
      some (heap', CheckedResult.blame info)) :
    False :=
  embedded_static_no_blame helab hsteps hfinal

example
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', result)) :
    ∃ v, result = CheckedResult.success v :=
  embedded_static_success helab hsteps hfinal

/-- Bool and NoneType are disjoint builtin classes. -/
private theorem booleanNone_empty :
    IsSubtype precisionCore.toOriginalWellFormedClassHierarchy (.intersection booleanType noneType) .bottom := by
  have excluded : IsSubtype precisionCore.toOriginalWellFormedClassHierarchy booleanType (.negClass noneClass) :=
    .sealedClassNegClass (by simp [sealedClasses])
      (fixtureStructure none).boolExists.hfind (fixtureStructure none).boolExists.hmro
      (by
        change noneClass ∉ [boolClass, objectClass]
        simp [noneClass, boolClass, objectClass])
      fixtureNoneValid
  exact .trans
    (.interIntro (.interRight (.refl fixtureNoneValid)
      fixtureBoolValid)
      (.interLeft excluded fixtureNoneValid))
    (.classSelfNegClassBottom fixtureNoneValid)

/-- A function with an empty alternative has a call bridge.
The alternative can be bottom or Bool & NoneType. -/
example (emptyTy : Ty)
    (shape : emptyTy = .bottom ∨ emptyTy = .intersection booleanType noneType) :
    EmbeddedExprBridge literalProgram.classes precisionCore
    [("f", .union (.callable booleanType booleanType) emptyTy)]
    (.call (.var "f") .constTrue) booleanType := by
  let environment : TyEnv := [("f", .union (.callable booleanType booleanType) emptyTy)]
  have emptyValid : WellFormedTy literalProgram.classes emptyTy := by
    rcases shape with rfl | rfl
    · exact .bottom
    · exact .intersection fixtureBoolValid fixtureNoneValid
  let functionValid : WellFormedTy literalProgram.classes
      (.union (.callable booleanType booleanType) emptyTy) :=
    .union (.callable fixtureBoolValid fixtureBoolValid) emptyValid
  let functionInference : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv environment) (.var "f") (embedTy (.union (.callable booleanType booleanType) emptyTy)) :=
    .var (embedTyEnv_lookupBinding (Γ := environment) (x := "f")
      (T := .union (.callable booleanType booleanType) emptyTy) rfl)
  let functionBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore environment
      (.var "f") (.union (.callable booleanType booleanType) emptyTy)
      (embedTy (.union (.callable booleanType booleanType) emptyTy)) functionInference
      (.union (.callable booleanType booleanType) emptyTy) :=
    .var rfl (.refl functionValid)
  let argumentBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore environment
      .constTrue booleanType (.class_ boolClass) .constTrue booleanType :=
    .constTrue (.refl fixtureBoolValid)
  have result : callSourceTy? (embedClassTable literalProgram.classes)
      (embedTy (.union (.callable booleanType booleanType) emptyTy))
      (.class_ boolClass) precisionCore =
      some (.class_ boolClass) := by
    rcases shape with rfl | rfl <;> decide +kernel
  have emptySubtype : IsSubtype precisionCore.toOriginalWellFormedClassHierarchy emptyTy .bottom := by
    rcases shape with rfl | rfl
    · exact .refl .bottom
    · exact booleanNone_empty
  exact {
    producerTy := booleanType
    srcTy := .class_ boolClass
    hsrc := .call functionInference .constTrue result
    core := .call (callee := .var "f") (arg := .constTrue)
      functionInference functionBridge .constTrue argumentBridge
      (.union_empty_right emptySubtype .callable) (.refl fixtureBoolValid) result .embed (.refl fixtureBoolValid) }

/-- Bottom, a function intersected with bottom, and Bool & NoneType all have call bridges with result bottom. -/
example (calleeTy : Ty)
    (shape : calleeTy = .bottom ∨
      calleeTy = .intersection (.callable booleanType booleanType) .bottom ∨
      calleeTy = .intersection .bottom (.callable booleanType booleanType) ∨
      calleeTy = .intersection booleanType (.class_ noneClass)) :
    EmbeddedExprBridge literalProgram.classes precisionCore [("f", calleeTy)]
      (.call (.var "f") .constTrue) .bottom := by
  have functionValid : WellFormedTy literalProgram.classes calleeTy := by
    rcases shape with rfl | rfl | rfl | rfl
    · exact .bottom
    · exact .intersection (.callable fixtureBoolValid fixtureBoolValid) .bottom
    · exact .intersection .bottom (.callable fixtureBoolValid fixtureBoolValid)
    · exact .intersection fixtureBoolValid fixtureNoneValid
  have selection : CallSelection precisionCore.toOriginalWellFormedClassHierarchy calleeTy objectType .bottom :=
    .empty (by
      rcases shape with rfl | rfl | rfl | rfl
      · exact .refl .bottom
      · exact .interRight (.refl .bottom) (.callable fixtureBoolValid fixtureBoolValid)
      · exact .interLeft (.refl .bottom) (.callable fixtureBoolValid fixtureBoolValid)
      · exact booleanNone_empty)
  let functionInference : GSrcInfer (embedClassTable literalProgram.classes) precisionCore
      (embedTyEnv [("f", calleeTy)]) (.var "f") (embedTy calleeTy) :=
    .var (embedTyEnv_lookupBinding (Γ := [("f", calleeTy)]) (x := "f") (T := calleeTy) rfl)
  let functionBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore [("f", calleeTy)]
      (.var "f") calleeTy (embedTy calleeTy) functionInference calleeTy :=
    .var rfl (.refl functionValid)
  let argumentBridge : EmbeddedExprBridgeCore literalProgram.classes precisionCore [("f", calleeTy)]
      .constTrue booleanType (.class_ boolClass) .constTrue booleanType :=
    .constTrue (.refl fixtureBoolValid)
  have result : callSourceTy? (embedClassTable literalProgram.classes)
      (embedTy calleeTy)
      (.class_ boolClass) precisionCore = some .bottom := by
    rcases shape with rfl | rfl | rfl | rfl
    all_goals decide +kernel
  exact {
    producerTy := .bottom
    srcTy := .bottom
    hsrc := .call functionInference .constTrue result
    core := .call (callee := .var "f") (arg := .constTrue)
      functionInference functionBridge .constTrue argumentBridge selection
      (.objectTop fixtureBoolValid) result .embed (.refl .bottom) }

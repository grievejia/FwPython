import FwPython.Static

open FwPython.Static.Subtyping

set_option autoImplicit false

/-! # Tests for function types and subtype checks

These tests check subtype comparisons and expression call inference, including
functions passed as inputs or returned as results, combined requirements,
repeated class names, and rejection of annotations with unknown class names.
The result-inversion example types the preallocated None reference directly,
establishing that the input type is not below bottom. A separate runtime example
decomposes a class-union typing of that reference. `OpenWorld.lean` checks
hierarchy extensions and rejection of incompatible inherited methods. -/

namespace FwPython.Examples.Static.Subtyping

/-- This test table contains Object, the three sealed builtin classes, and the unrelated user classes A and B. -/
def fixture : ClassContext where
  names := [objectClass, boolClass, noneClass, boundMethodClass, "A", "B"]
  ancestors name := if name = objectClass then [objectClass] else [name, objectClass]

/-- This smaller test table contains only the four builtin classes. -/
def builtinFixture : ClassContext := { fixture with names := [objectClass, boolClass, noneClass, boundMethodClass] }

/-- Repeating a class name keeps the same class membership meaning. -/
def repeatedFixture : ClassContext := { fixture with names := fixture.names ++ [boolClass] }

/-- The test table satisfies inheritance, sealing, and distinct MRO orders. -/
theorem fixture_valid : ValidContext fixture := by
  constructor <;> simp [fixture, sealedClasses, objectClass, boolClass, noneClass, boundMethodClass] <;> decide

/-- The table with only builtin classes also satisfies these rules. -/
theorem builtinFixture_valid : ValidContext builtinFixture := by
  constructor <;> simp [builtinFixture, fixture, sealedClasses, objectClass, boolClass, noneClass, boundMethodClass] <;> decide

/-- The builtin test table with its context validity proof. -/
abbrev builtinContext : ValidatedClassContext := ⟨builtinFixture, builtinFixture_valid⟩

/-- Repeating a class name preserves the table rules. -/
theorem repeatedFixture_valid : ValidContext repeatedFixture := by
  constructor <;> simp [repeatedFixture, fixture, sealedClasses, objectClass, boolClass, noneClass, boundMethodClass] <;> decide

/-- The class fixture with its context validity proof. -/
abbrev fixtureContext : ValidatedClassContext := ⟨fixture, fixture_valid⟩

/-- The repeated-name fixture with its context validity proof. -/
abbrev repeatedContext : ValidatedClassContext := ⟨repeatedFixture, repeatedFixture_valid⟩

/-- The Bool class type used in the tests. -/
abbrev booleanType : Ty := .class_ boolClass
/-- The NoneType class type used in the tests. -/
abbrev noneType : Ty := .class_ noneClass
/-- The Object type, which contains every value. -/
abbrev objectType : Ty := .class_ objectClass
/-- The BoundMethod class type, which contains every callable value. -/
abbrev methodType : Ty := .class_ boundMethodClass

/-- The function must satisfy both `Bool -> Bool` and `NoneType -> NoneType`. -/
abbrev correlated : Ty := .intersection (.callable booleanType booleanType) (.callable noneType noneType)
/-- The function requirement has Bool-or-NoneType input and Bool-and-NoneType result. -/
abbrev fused : Ty := .callable (.union booleanType noneType) (.intersection booleanType noneType)
/-- The function requirement has Bool-or-NoneType input and Bool-or-NoneType result. -/
abbrev correlatedSummary : Ty := .callable (.union booleanType noneType) (.union booleanType noneType)

/-- The separate requirements are not below a target requiring both result classes. -/
example : checkSubtypeBool builtinContext
    ⟨correlated, by decide +kernel⟩ ⟨fused, by decide +kernel⟩ = false := by
  decide +kernel

/-- The two requirements together are below the function type with union input and union result. -/
example : checkSubtypeBool builtinContext
    ⟨correlated, by decide +kernel⟩ ⟨correlatedSummary, by decide +kernel⟩ = true := by
  decide +kernel

/-- A union input and intersected result satisfy each separate function requirement. -/
example : checkSubtypeBool builtinContext
    ⟨fused, by decide +kernel⟩ ⟨correlated, by decide +kernel⟩ = true := by
  decide +kernel

/-- A function with a union result is not below the union of separately typed functions. -/
example : checkSubtypeBool builtinContext
    ⟨.callable noneType (.union booleanType noneType), by decide +kernel⟩
    ⟨.union (.callable noneType booleanType) (.callable noneType noneType), by decide +kernel⟩ = false := by
  decide +kernel

/-- The union of Bool-result and NoneType-result functions is below the union-result function type. -/
example : checkSubtypeBool builtinContext
    ⟨.union (.callable noneType booleanType) (.callable noneType noneType), by decide +kernel⟩
    ⟨.callable noneType (.union booleanType noneType), by decide +kernel⟩ = true := by
  decide +kernel

/-- No valid function type is below bottom, even when its result type is bottom. -/
example (context : ValidatedClassContext) (parameter result : WellFormedType context.names) :
    ¬ TypeEquivalence.Subtype context (WellFormedType.callable parameter result).raw .bottom := by
  intro included
  have compared := (checkSubtypeBool_iff_intersections context (.callable parameter result) .bottom).mp
    (checkSubtypeBool_of_subtype context (.callable parameter result) .bottom included)
  obtain ⟨_, member, _, _⟩ := compared _
    (by rw [splitIntoIntersections_callable]; exact List.mem_singleton_self _)
  rw [splitIntoIntersections_bottom] at member
  cases member

/-- A bottom result does not make the function type bottom. -/
example : checkSubtypeBool builtinContext
    (.callable builtinContext.objectType .bottom) .bottom = false := by
  decide +kernel

/-- BoundMethod alone is not below a function type accepting Object-to-bottom function inputs. -/
example : checkSubtypeBool builtinContext builtinContext.boundMethodType
    (.callable (.callable builtinContext.objectType .bottom) builtinContext.objectType) = false := by
  decide +kernel

/-- Every BoundMethod satisfies a function requirement with input bottom. -/
example : checkSubtypeBool builtinContext
    ⟨methodType, by decide +kernel⟩ ⟨.callable .bottom noneType, by decide +kernel⟩ = true := by
  decide +kernel

/-- A function requirement with input bottom still requires BoundMethod membership. -/
example : checkSubtypeBool builtinContext
    ⟨.callable .bottom noneType, by decide +kernel⟩ ⟨methodType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Accepting NoneType inputs does not establish the requirement to accept Bool inputs. -/
example : checkSubtypeBool builtinContext
    ⟨.callable noneType objectType, by decide +kernel⟩
    ⟨.callable booleanType objectType, by decide +kernel⟩ = false := by
  decide +kernel

/-- The intersected requirements give a Bool result for Bool inputs; neither requirement alone does. -/
example : checkSubtypeBool builtinContext
    ⟨.intersection
      (.callable (.union booleanType noneType) (.union booleanType noneType))
      (.callable (.union booleanType methodType) (.union booleanType methodType)), by decide +kernel⟩
    ⟨.callable booleanType booleanType, by decide +kernel⟩ = true := by
  decide +kernel

/-- The first requirement includes NoneType in its result, so it is not below the Bool-result target. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (.union booleanType noneType) (.union booleanType noneType), by decide +kernel⟩
    ⟨.callable booleanType booleanType, by decide +kernel⟩ = false := by
  decide +kernel

/-- The second requirement includes BoundMethod in its result, so it is not below the Bool-result target. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (.union booleanType methodType) (.union booleanType methodType), by decide +kernel⟩
    ⟨.callable booleanType booleanType, by decide +kernel⟩ = false := by
  decide +kernel

/-- BoundMethod is not below a function type with Bool input and Object result. -/
example : checkSubtypeBool builtinContext
    ⟨methodType, by decide +kernel⟩
    ⟨.callable booleanType objectType, by decide +kernel⟩ = false := by
  decide +kernel

/-- The nested Bool-result function type is below the otherwise identical Object-result type. -/
example : checkSubtypeBool builtinContext
    ⟨.callable booleanType (.callable booleanType booleanType), by decide +kernel⟩
    ⟨.callable booleanType (.callable booleanType objectType), by decide +kernel⟩ = true := by
  decide +kernel

/-- A NoneType-input, bottom-result function type is not below the Bool-input target. -/
example : checkSubtypeBool builtinContext
    ⟨.callable noneType .bottom, by decide +kernel⟩
    ⟨.callable booleanType .bottom, by decide +kernel⟩ = false := by
  decide +kernel

/-- The correlated source is not below a target also requiring NoneType results for Bool inputs. -/
example : checkSubtypeBool builtinContext
    ⟨correlated, by decide +kernel⟩
    ⟨.intersection (.callable (.union booleanType noneType) (.union booleanType noneType))
      (.callable booleanType noneType), by decide +kernel⟩ = false := by
  decide +kernel

/-- The Bool-input, bottom-result requirement is below the Bool-input, Object-result target. -/
example : checkSubtypeBool builtinContext
    ⟨.callable booleanType .bottom, by decide +kernel⟩
    ⟨.callable booleanType objectType, by decide +kernel⟩ = true := by
  decide +kernel

/-- BoundMethod is below the function type whose Bool-and-NoneType input is empty. -/
example : checkSubtypeBool builtinContext
    ⟨methodType, by decide +kernel⟩
    ⟨.callable (.intersection booleanType noneType) objectType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Repeating a function requirement does not change its meaning. -/
example : checkSubtypeBool builtinContext
    ⟨.intersection (.callable booleanType booleanType) (.callable booleanType booleanType), by decide +kernel⟩
    ⟨.callable booleanType booleanType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Excluding Bool from `Bool | BoundMethod` leaves only callable values. -/
example : checkSubtypeBool builtinContext
    ⟨.intersection (.negClass boolClass) (.union methodType booleanType), by decide +kernel⟩
    ⟨.callable .bottom objectType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Two input reversals permit changing the nested input from Bool to Object. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (.callable booleanType objectType) objectType, by decide +kernel⟩
    ⟨.callable (.callable objectType objectType) objectType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Reversing this subtype comparison fails when its inner input requires Object below Bool. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (.callable objectType objectType) objectType, by decide +kernel⟩
    ⟨.callable (.callable booleanType objectType) objectType, by decide +kernel⟩ = false := by
  decide +kernel

/-- Build nested function inputs and results, using the supplied type at each leaf. -/
def nestedType (depth : Nat) (leaf : Ty := booleanType) : Ty :=
  match depth with
  | 0 => leaf
  | depth + 1 => .callable (nestedType depth leaf) (nestedType depth leaf)

/-- The comparison is reflexive on this one-level function type. -/
example : checkSubtypeBool builtinContext
    ⟨nestedType 1, by decide +kernel⟩ ⟨nestedType 1, by decide +kernel⟩ = true := by
  decide +kernel

/-- The comparison is reflexive on this four-level function type. -/
example : checkSubtypeBool builtinContext
    ⟨nestedType 4, by decide +kernel⟩ ⟨nestedType 4, by decide +kernel⟩ = true := by
  decide +kernel

/-- Swap the two leaf types on each function input and keep them on each result. -/
private def polarType {names : List Identifier} :
    Nat → WellFormedType names → WellFormedType names → WellFormedType names
  | 0, resultLeaf, _ => resultLeaf
  | height + 1, resultLeaf, inputLeaf =>
      .callable (polarType height inputLeaf resultLeaf) (polarType height resultLeaf inputLeaf)

/-- Four nested levels compare Bool below Object at every leaf after reversing each input comparison. -/
example : checkSubtypeBool builtinContext
    (polarType 4 (.class_ boolClass (by decide +kernel)) builtinContext.objectType)
    (polarType 4 builtinContext.objectType (.class_ boolClass (by decide +kernel))) = true := by
  decide +kernel

/-- Reversing the four-level comparison requires Object below Bool and is rejected. -/
example : checkSubtypeBool builtinContext
    (polarType 4 builtinContext.objectType (.class_ boolClass (by decide +kernel)))
    (polarType 4 (.class_ boolClass (by decide +kernel)) builtinContext.objectType) = false := by
  decide +kernel

/-- At four levels, eight leaf positions require Object below Bool, so the comparison fails. -/
example : checkSubtypeBool builtinContext
    ⟨nestedType 4 booleanType, by decide +kernel⟩
    ⟨nestedType 4 objectType, by decide +kernel⟩ = false := by
  decide +kernel

/-- A three-level function result does not satisfy this two-level result annotation. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (nestedType 4) (nestedType 3), by decide +kernel⟩
    ⟨.callable (nestedType 4) (nestedType 2), by decide +kernel⟩ = false := by
  decide +kernel

/-- The same five-level source is accepted when its required result is BoundMethod. -/
example : checkSubtypeBool builtinContext
    ⟨.callable (nestedType 4) (nestedType 3), by decide +kernel⟩
    ⟨.callable (nestedType 4) methodType, by decide +kernel⟩ = true := by
  decide +kernel

/-- A compatible conjunction of unrelated user classes is distinct from bottom. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection (.class_ "A") (.class_ "B"), by decide +kernel⟩ .bottom = false := by
  decide +kernel

/-- Sharing two unrelated user classes does not force BoundMethod membership. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection (.class_ "A") (.class_ "B"), by decide +kernel⟩
    ⟨methodType, by decide +kernel⟩ = false := by
  decide +kernel

/-- Excluding A from A-or-BoundMethod leaves a nonempty type below BoundMethod. -/
example :
    let callee : WellFormedType fixtureContext.names :=
      .intersection (.union (.class_ "A" (by decide +kernel)) fixtureContext.boundMethodType)
        (.negClass "A" (by decide +kernel))
    checkSubtypeBool fixtureContext callee .bottom = false ∧
      checkSubtypeBool fixtureContext callee fixtureContext.boundMethodType = true := by
  decide +kernel

/-- Repeating a class name preserves the distinction between membership and exclusion. -/
example : checkSubtypeBool repeatedContext
    ⟨booleanType, by decide +kernel⟩ ⟨.negClass boolClass, by decide +kernel⟩ = false := by
  decide +kernel

/-- Bool excludes NoneType when its class name appears more than once. -/
example : checkSubtypeBool repeatedContext
    (.class_ boolClass (by decide +kernel)) (.negClass noneClass (by decide +kernel)) = true := by
  decide +kernel

/-- A repeated class name does not duplicate the complete Bool intersection. -/
example :
    let classes := ClassIntersection.ofClassMro repeatedContext
      boolClass (by decide +kernel)
    (splitIntoIntersections repeatedContext classes.toType).intersections.length = 1 := by
  decide +kernel

/-- Every instance of a known class also has type Object. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection (.class_ "A") (.negClass objectClass), by decide +kernel⟩ .bottom = true := by
  decide +kernel

/-- A sealed Bool class cannot share membership with the unrelated user class A. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection booleanType (.class_ "A"), by decide +kernel⟩ .bottom = true := by
  decide +kernel

/-- A sealed NoneType class cannot share membership with the unrelated user class B. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection noneType (.class_ "B"), by decide +kernel⟩ .bottom = true := by
  decide +kernel

/-- Bool and BoundMethod have disjoint membership. -/
example : checkSubtypeBool fixtureContext
    ⟨.intersection methodType booleanType, by decide +kernel⟩ .bottom = true := by
  decide +kernel

/-- Function requirements with input bottom place no restrictions on returned results. -/
example : checkSubtypeBool builtinContext
    ⟨.callable .bottom booleanType, by decide +kernel⟩
    ⟨.callable .bottom noneType, by decide +kernel⟩ = true := by
  decide +kernel

/-- Bool is not below the distinct sealed NoneType class. -/
example : checkSubtypeBool builtinContext
    ⟨booleanType, by decide +kernel⟩ ⟨noneType, by decide +kernel⟩ = false := by
  decide +kernel

section Project

variable (table : ClassTable) (wellFormed : WellTypedClassHierarchy table)

/-- A Bool-input function type is not below a NoneType-input function type in any well-formed table. -/
example : ¬ IsSubtype wellFormed.toWellFormedClassHierarchy
    (.callable booleanType booleanType) (.callable noneType noneType) := by
  intro included
  have inherited := class_subtype_mem_mro wellFormed.toWellFormedClassHierarchy
    (callable_domain_subtype included)
    wellFormed.noneExists.hfind wellFormed.noneExists.hmro
  have impossible := wellFormed.sealedLeaf boolClass (by simp [sealedClasses])
    noneClass _ _ wellFormed.noneExists.hfind wellFormed.noneExists.hmro inherited
  exact (by decide +kernel : noneClass ≠ boolClass) impossible

/-- The source result is below the target result when the target input is NoneType.
Typing the preallocated None reference at NoneType establishes that this input is nonempty. -/
example (P R S : Ty)
    (included : IsSubtype wellFormed.toWellFormedClassHierarchy (.callable P R) (.callable noneType S)) :
    IsSubtype wellFormed.toWellFormedClassHierarchy R S := by
  have heapWellFormed := Heap.initial_wellFormed wellFormed
  have noneTyped : ValueHasType wellFormed.toWellFormedClassHierarchy Heap.initial (.objRef noneOid) noneType :=
    .objRef heapWellFormed.initialNone (.refl (WellFormedTy.none wellFormed.toWellFormedClassHierarchy))
  exact callable_return_subtype included
    (valueHasType_nonempty wellFormed heapWellFormed noneTyped)

end Project

/-- Correlated summaries also accept a higher-order function input. -/
example : checkSubtypeBool builtinContext
    ⟨.intersection (.callable (.callable objectType .bottom) booleanType)
      (.callable noneType noneType), by decide +kernel⟩
    ⟨.callable (.union (.callable objectType .bottom) noneType)
      (.union booleanType noneType), by decide +kernel⟩ = true := by
  decide +kernel

/-- A builtin class declaration with the given methods and implicit Object inheritance. -/
def fixtureClass (name : Identifier) (methods : List Method := []) : Class :=
  { name, baseClasses := [], methods }

/-- The table has four builtin declarations. It can also contain a later Bool declaration. -/
def fixtureTable (shadow : Option (List Method) := none) : ClassTable :=
  [fixtureClass objectClass, fixtureClass boolClass, fixtureClass noneClass,
    fixtureClass boundMethodClass] ++
    match shadow with
    | none => []
    | some methods => [fixtureClass boolClass methods]

/-- Every declaration in this test table has no explicit parent classes. -/
theorem fixtureTable_noBases {declaration : Class} {shadow : Option (List Method)} (member : declaration ∈ fixtureTable shadow) :
    declaration.baseClasses = [] := by
  cases shadow <;> simp [fixtureTable] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A class without explicit parents has an MRO containing itself and Object. Object has only itself. -/
def fixtureMro {table : ClassTable} (objectLookup : findClass table objectClass = some (fixtureClass objectClass))
    (declaration : Class) (noBases : declaration.baseClasses = []) :
    ClassMroWitness table declaration where
  mro := if declaration.name = objectClass then [objectClass] else [declaration.name, objectClass]
  hmro := by
    split
    · rename_i root
      simpa [root] using ComputeMro.root (ct := table)
        (c := declaration) (by simp [ClassDecl.resolvedBases, noBases, root])
    · rename_i notRoot
      exact .step (by simp [ClassDecl.resolvedBases, noBases, notRoot]) (by simp)
        (.cons objectLookup (.root rfl) .nil) rfl

/-- If every declaration has no explicit parents, no class can inherit a sealed builtin. -/
theorem fixtureSealedLeaf {table : ClassTable}
    (objectLookup : findClass table objectClass = some (fixtureClass objectClass))
    (noBases : ∀ {declaration}, declaration ∈ table → declaration.baseClasses = []) :
    ∀ builtin, builtin ∈ sealedClasses → ∀ name declaration mro,
      findClass table name = some declaration → ComputeMro table declaration mro →
      builtin ∈ mro → name = builtin := by
  intro builtin sealed name declaration mro lookup computed member
  have notObject : builtin ≠ objectClass := by
    rintro rfl
    revert sealed
    decide +kernel
  have same := determinism computed (fixtureMro objectLookup declaration (noBases (findClass_mem lookup))).hmro
  rw [same] at member
  change builtin ∈ (if declaration.name = objectClass then [objectClass]
    else [declaration.name, objectClass]) at member
  split at member <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  · exact (notObject member).elim
  · rcases member with self | root
    · exact (findClass_name lookup).symm.trans self.symm
    · exact (notObject root).elim

/-- The selected declarations satisfy the inheritance rules when the table contains a later Bool declaration. -/
def fixtureStructure (shadow : Option (List Method) := none) :
    WellFormedClassHierarchy (fixtureTable shadow) := by
  have objectLookup : findClass (fixtureTable shadow) objectClass = some (fixtureClass objectClass) := by
    cases shadow <;> rfl
  let allMros : ∀ name declaration, findClass (fixtureTable shadow) name = some declaration →
      ClassMroWitness (fixtureTable shadow) declaration :=
    fun _ declaration lookup => fixtureMro objectLookup declaration
      (fixtureTable_noBases (findClass_mem lookup))
  exact {
    objectExists := ⟨fixtureClass objectClass, objectLookup, rfl⟩
    boolExists := ⟨fixtureClass boolClass, [boolClass, objectClass], by cases shadow <;> rfl,
      (allMros boolClass _ (by cases shadow <;> rfl)).hmro⟩
    noneExists := ⟨fixtureClass noneClass, [noneClass, objectClass], by cases shadow <;> rfl,
      (allMros noneClass _ (by cases shadow <;> rfl)).hmro⟩
    boundMethodExists := ⟨fixtureClass boundMethodClass, [boundMethodClass, objectClass], by cases shadow <;> rfl,
      (allMros boundMethodClass _ (by cases shadow <;> rfl)).hmro⟩
    allMrosExist := allMros
    sealedLeaf := fixtureSealedLeaf objectLookup fixtureTable_noBases }

/-- A shadowed declaration does not duplicate the selected Bool intersection. -/
example :
    let context := (fixtureStructure (some [])).typeContext
    let classes := ClassIntersection.ofClassMro context boolClass (by decide +kernel)
    (splitIntoIntersections context classes.toType).intersections.length = 1 := by
  decide +kernel

/-- The four builtin declarations contain no methods, overrides, duplicate names, or explicit parents. -/
def fixtureWellFormed : WellTypedClassHierarchy (fixtureTable none) := by
  have emptyMethods : ∀ name declaration, findClass (fixtureTable none) name = some declaration →
      declaration.methods = [] := by
    intro name declaration lookup
    have member := findClass_mem lookup
    simp [fixtureTable] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  refine {
    toWellFormedClassHierarchy := fixtureStructure none
    allMethodsWellTyped := ?_
    liskovCondition := ?_
    allMethodNamesDistinct := ?_
    allMethodSignaturesWellFormed := ?_
    classNamesUnique := ?_
    baseClassesDistinct := ?_ }
  · intro name declaration method lookup member
    rw [emptyMethods name declaration lookup] at member
    cases member
  · intro name ancestor declaration ancestorDeclaration mro ancestorMro methodName method ancestorMethod
      _ _ _ _ _ found _
    obtain ⟨owner, ownerDeclaration, _, ownerLookup, methodMember⟩ := findMethodInMro_provenance found
    rw [emptyMethods owner ownerDeclaration ownerLookup] at methodMember
    cases methodMember
  · intro name declaration lookup
    simp [emptyMethods name declaration lookup]
  · intro name declaration method lookup member
    rw [emptyMethods name declaration lookup] at member
    cases member
  · intro first second firstMember secondMember sameName
    simp [fixtureTable] at firstMember secondMember
    rcases firstMember with rfl | rfl | rfl | rfl <;>
      rcases secondMember with rfl | rfl | rfl | rfl <;>
      simp_all [fixtureClass, objectClass, boolClass, noneClass, boundMethodClass]
  · intro name declaration lookup
    simp [fixtureTable_noBases (findClass_mem lookup)]

/-- Bool names a declaration in the builtin fixture. -/
theorem fixtureBoolValid : WellFormedTy (fixtureTable none) booleanType :=
  WellFormedTy.bool (fixtureStructure none)

/-- NoneType names a declaration in the builtin fixture. -/
theorem fixtureNoneValid : WellFormedTy (fixtureTable none) noneType :=
  WellFormedTy.none (fixtureStructure none)

/-- Object names a declaration in the builtin fixture. -/
theorem fixtureObjectValid : WellFormedTy (fixtureTable none) objectType :=
  WellFormedTy.object (fixtureStructure none)

/-- BoundMethod names a declaration in the builtin fixture. -/
theorem fixtureMethodValid : WellFormedTy (fixtureTable none) methodType :=
  WellFormedTy.boundMethod (fixtureStructure none)

/-- The fused input and result annotation uses only the builtin class names. -/
theorem fixtureFusedValid : WellFormedTy (fixtureTable none) fused :=
  .callable (.union fixtureBoolValid fixtureNoneValid) (.intersection fixtureBoolValid fixtureNoneValid)

/-- The correlated summary uses only the builtin class names. -/
theorem fixtureCorrelatedSummaryValid : WellFormedTy (fixtureTable none) correlatedSummary :=
  .callable (.union fixtureBoolValid fixtureNoneValid) (.union fixtureBoolValid fixtureNoneValid)

/-- The Bool and NoneType names in both function requirements are valid. -/
theorem fixtureCorrelatedValid : WellFormedTy (fixtureTable none) correlated :=
  .intersection (.callable fixtureBoolValid fixtureBoolValid)
    (.callable fixtureNoneValid fixtureNoneValid)

/-- An empty target input permits subtyping without requiring the source result below the target result. -/
example :
    IsSubtype (fixtureStructure none)
      (.callable booleanType booleanType) (.callable .bottom noneType) ∧
    ¬ IsSubtype (fixtureStructure none) booleanType noneType := by
  constructor
  · exact @of_decide_eq_true _
      (WellFormedType.subtypeDecidable (fixtureStructure none)
        (.callable fixtureBoolValid.toType fixtureBoolValid.toType)
        (.callable .bottom fixtureNoneValid.toType))
      (by decide +kernel)
  · exact @of_decide_eq_false _
      (WellFormedType.subtypeDecidable (fixtureStructure none)
        fixtureBoolValid.toType fixtureNoneValid.toType)
      (by decide +kernel)

/-- The subtype decision on valid packages rejects the correlated source against
a target requiring both result types. -/
example : @decide (IsSubtype (fixtureStructure none) correlated fused)
    (WellFormedType.subtypeDecidable (fixtureStructure none)
      fixtureCorrelatedValid.toType fixtureFusedValid.toType) = false := by
  decide +kernel

/-- The subtype decision accepts the correlated source below the Bool-or-NoneType input and result type. -/
example : @decide (IsSubtype (fixtureStructure none) correlated correlatedSummary)
    (WellFormedType.subtypeDecidable (fixtureStructure none)
      fixtureCorrelatedValid.toType fixtureCorrelatedSummaryValid.toType) = true := by
  decide +kernel

/-- Lookup selects the first Bool declaration when the name occurs twice. -/
example : findClass (fixtureTable (some [])) boolClass = some (fixtureClass boolClass) := rfl

/-- A later Bool declaration does not affect lookup or MRO data, even when its methods differ. -/
example (method : Method) :
    findClass (fixtureTable (some [method])) boolClass = some (fixtureClass boolClass) := rfl

/-- A repeated builtin name satisfies the class context rules. -/
example : ValidContext (classContextOf (fixtureTable (some [])) (fixtureStructure (some []))) :=
  classContextOf_valid _ _

/-- Different methods in a later declaration do not affect those class context rules. -/
example (method : Method) :
    ValidContext (classContextOf (fixtureTable (some [method])) (fixtureStructure (some [method]))) :=
  classContextOf_valid _ _

/-- A value of type `Bool | BoundMethod` can be an ordinary Bool object. The checker cannot call every such value. -/
example : (callableSummaries fixtureWellFormed.toWellFormedClassHierarchy
    (.union fixtureBoolValid.toType fixtureMethodValid.toType)).pairs = [] := by
  decide +kernel

/-- For function type bottom, the checker gives the requirement `Object -> bottom`. -/
example : (callableSummaries fixtureWellFormed.toWellFormedClassHierarchy .bottom).pairs = [(objectType, .bottom)] := by
  decide +kernel

/-- For BoundMethod alone, the checker includes an input type with no values. -/
example : (.intersection .bottom objectType, .union .bottom .bottom) ∈
    (callableSummaries fixtureWellFormed.toWellFormedClassHierarchy
      fixtureMethodValid.toType).pairs := by
  decide +kernel

/-- The checker includes the bottom input case for an explicitly typed function. -/
example : (.intersection .bottom objectType, .union .bottom .bottom) ∈
    (callableSummaries fixtureWellFormed.toWellFormedClassHierarchy
      (.callable fixtureBoolValid.toType fixtureBoolValid.toType)).pairs := by
  decide +kernel

/-- The subset list retains repeated entries, including two identical function requirements. -/
example : [[(booleanType, booleanType)], [(booleanType, booleanType), (booleanType, booleanType)]] ∈
    subsequences (nonemptySubsets [(booleanType, booleanType), (booleanType, booleanType)]) := by
  decide +kernel

/-- The supplied valid annotation for f and builtin Bool annotation for x form a valid environment. -/
theorem fixtureCallEnvironment_wellFormed (source : Ty)
    (sourceValid : WellFormedTy (fixtureTable none) source) :
    WellFormedTyEnv (fixtureTable none) [("f", source), ("x", booleanType)] := by
  intro name type lookup
  by_cases functionName : "f" = name
  · simp [NamedEnv.lookup, functionName] at lookup
    cases lookup
    exact sourceValid
  · by_cases argumentName : "x" = name
    · simp [NamedEnv.lookup, functionName, argumentName] at lookup
      cases lookup
      exact fixtureBoolValid
    · simp [NamedEnv.lookup, functionName, argumentName] at lookup

/-- Combining both argument requirements makes the argument below the requested Bool-to-Bool input type. -/
example : checkHasType? fixtureWellFormed
    (wellFormedTyEnv_update
      (fixtureCallEnvironment_wellFormed _
        (.callable (.callable fixtureBoolValid fixtureBoolValid) fixtureBoolValid))
      (x := "x") (by rfl)
      (.intersection
        (.callable (.union fixtureBoolValid fixtureNoneValid)
          (.union fixtureBoolValid fixtureNoneValid))
        (.callable (.union fixtureBoolValid fixtureMethodValid)
          (.union fixtureBoolValid fixtureMethodValid))))
    (.call (.var "f") (.var "x")) booleanType = true := by
  decide +kernel

/-- The call is rejected when the argument has only the first requirement. -/
example : checkHasType? fixtureWellFormed
    (wellFormedTyEnv_update
      (fixtureCallEnvironment_wellFormed _
        (.callable (.callable fixtureBoolValid fixtureBoolValid) fixtureBoolValid))
      (x := "x") (by rfl)
      (.callable (.union fixtureBoolValid fixtureNoneValid)
        (.union fixtureBoolValid fixtureNoneValid)))
    (.call (.var "f") (.var "x")) booleanType = false := by
  decide +kernel

/-- The call is rejected when the argument has only the second requirement. -/
example : checkHasType? fixtureWellFormed
    (wellFormedTyEnv_update
      (fixtureCallEnvironment_wellFormed _
        (.callable (.callable fixtureBoolValid fixtureBoolValid) fixtureBoolValid))
      (x := "x") (by rfl)
      (.callable (.union fixtureBoolValid fixtureMethodValid)
        (.union fixtureBoolValid fixtureMethodValid)))
    (.call (.var "f") (.var "x")) booleanType = false := by
  decide +kernel

/-- The correlated callee and union-typed argument use only builtin class names. -/
private theorem unionArgumentEnvironmentValid :
    WellFormedTyEnv (fixtureTable none)
      (TyEnv.update [("f", correlated), ("x", booleanType)] "x" (.union booleanType noneType)) :=
  wellFormedTyEnv_update (fixtureCallEnvironment_wellFormed correlated fixtureCorrelatedValid)
    (x := "x") rfl (.union fixtureBoolValid fixtureNoneValid)

/-- Covering both argument alternatives gives a Bool-or-NoneType result. -/
example : checkHasType? fixtureWellFormed unionArgumentEnvironmentValid
    (.call (.var "f") (.var "x")) (.union booleanType noneType) = true := by
  decide +kernel

/-- The call is rejected when its requested result is Bool & NoneType. -/
example : checkHasType? fixtureWellFormed unionArgumentEnvironmentValid
    (.call (.var "f") (.var "x")) (.intersection booleanType noneType) = false := by
  decide +kernel

/-- Repeating `Bool -> Bool` lets the expression checker infer Bool for a Bool input. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.intersection
        (.callable fixtureBoolValid fixtureBoolValid)
        (.callable fixtureBoolValid fixtureBoolValid)))
    (.call (.var "f") (.var "x")) booleanType = true := by
  decide +kernel

/-- The expression checker rejects passing Bool to a function that requires NoneType. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.callable fixtureNoneValid fixtureNoneValid))
    (.call (.var "f") (.var "x")) noneType = false := by
  decide +kernel

/-- The same NoneType-input function accepts a None argument and gives a NoneType result. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _ (.callable fixtureNoneValid fixtureNoneValid))
    (.call (.var "f") .constNone) noneType = true := by
  decide +kernel

/-- A Bool input gives Bool when the other function requirement has input bottom. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.intersection
        (.callable fixtureBoolValid fixtureBoolValid)
        (.callable .bottom fixtureNoneValid)))
    (.call (.var "f") (.var "x")) booleanType = true := by
  decide +kernel

/-- The requirement `bottom -> NoneType` does not permit assigning NoneType to this Bool call. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.intersection
        (.callable fixtureBoolValid fixtureBoolValid)
        (.callable .bottom fixtureNoneValid)))
    (.call (.var "f") (.var "x")) noneType = false := by
  decide +kernel

/-- The result type `Bool | NoneType` cannot be passed to a function that requires Bool. -/
example : @decide (IsSubtype (fixtureStructure none) (.union booleanType noneType) booleanType)
    (WellFormedType.subtypeDecidable (fixtureStructure none)
      (.union fixtureBoolValid.toType fixtureNoneValid.toType) fixtureBoolValid.toType) = false := by
  decide +kernel

/-- A Bool input gives Bool when both the Bool and Object parameter types accept it. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.intersection
        (.callable fixtureBoolValid fixtureBoolValid)
        (.callable fixtureObjectValid fixtureObjectValid)))
    (.call (.var "f") (.var "x")) booleanType = true := by
  decide +kernel

/-- Either of the two possible functions accepts Bool. The checker keeps Bool as the result type. -/
example : checkHasType? fixtureWellFormed
    (fixtureCallEnvironment_wellFormed _
      (.union fixtureCorrelatedValid
        (.intersection
          (.callable fixtureBoolValid fixtureBoolValid)
          (.callable fixtureObjectValid fixtureObjectValid))))
    (.call (.var "f") (.var "x")) booleanType = true := by
  decide +kernel

section PendingCalls

variable {table : ClassTable} {heap : Heap} {environment : TyEnv}
  {receiverOid : Nat} {receiverObject : HeapObject} {method : Method}

/-- A pending call with required input bottom can be typed without comparing the declared and requested result types. -/
example (wellFormed : WellTypedClassHierarchy table)
    (lookup : heap.lookup receiverOid = some receiverObject)
    (origin : MethodInReceiverMro table receiverObject.className method) :
    SmallStep.FrameHasType wellFormed.toWellFormedClassHierarchy heap environment .bottom environment (.class_ noneClass)
      (.awaitArgument receiverOid method) := by
  have signatureValid := methodInReceiverMro_wellFormed wellFormed origin
  exact .awaitArgument lookup origin
    (.trans (.callableBoundMethod signatureValid.callable_param signatureValid.callable_return)
      (.boundMethodEmptyDomain (WellFormedTy.none wellFormed.toWellFormedClassHierarchy)))

/-- An argument expression of type bottom can run forever. The pending call does not require it to return. -/
example {callee argument : Expr}
    (wellFormed : WellTypedClassHierarchy table)
    (calleeTyped : HasType wellFormed.toWellFormedClassHierarchy environment callee methodType)
    (argumentTyped : HasType wellFormed.toWellFormedClassHierarchy environment argument .bottom) :
    HasType wellFormed.toWellFormedClassHierarchy environment (.call callee argument) noneType :=
  HasType.call_direct
    (.sub calleeTyped (.boundMethodEmptyDomain (WellFormedTy.none wellFormed.toWellFormedClassHierarchy)))
    argumentTyped .bottom

end PendingCalls

/-- The pre-allocated None and Boolean objects satisfy every static heap rule. -/
example : HeapWellFormed (fixtureTable none) Heap.initial :=
  Heap.initial_wellFormed fixtureWellFormed

/-- The preallocated None reference's class-union type decomposes into one of its class typings. -/
example (first second : Identifier)
    (typed : ValueHasType fixtureWellFormed.toWellFormedClassHierarchy Heap.initial
      (.objRef noneOid) (.union (.class_ first) (.class_ second))) :
    ValueHasType fixtureWellFormed.toWellFormedClassHierarchy Heap.initial (.objRef noneOid) (.class_ first) ∨
      ValueHasType fixtureWellFormed.toWellFormedClassHierarchy Heap.initial (.objRef noneOid) (.class_ second) := by
  have heapWellFormed := Heap.initial_wellFormed fixtureWellFormed
  have alternatives := objRef_union_class_decompose fixtureWellFormed heapWellFormed typed
    heapWellFormed.initialNone fixtureWellFormed.noneExists.hfind fixtureWellFormed.noneExists.hmro
  rcases alternatives with firstType | secondType
  · exact .inl (.objRef heapWellFormed.initialNone firstType)
  · exact .inr (.objRef heapWellFormed.initialNone secondType)

/-- A typed program that starts from the initial heap returns a typed value. -/
example : ∃ heap value,
    Result.success (.objRef trueOid) = .success value ∧
    ValueHasType fixtureWellFormed.toWellFormedClassHierarchy heap value booleanType := by
  exact SmallStep.program_soundness
    (p := { classes := fixtureTable none, main := .constTrue })
    fixtureWellFormed .constTrue
    ⟨{ heap := Heap.initial, env := [], control := .val (.objRef trueOid), continuation := [] },
      Heap.initial, RuntimeSteps.single .constTrue, rfl⟩

/-- An unknown class name prevents a source class annotation from having a subtype proof. -/
example : ¬ IsSubtype (fixtureStructure none) (.class_ "Unknown") .bottom := by
  have unknownName : "Unknown" ∉ (classContextOf (fixtureTable none) (fixtureStructure none)).names := by
    decide +kernel
  intro included
  cases included.sourceWellFormed with
  | class_ known => exact unknownName known

/-- Run the subtype decision on raw annotations, including its class-name validation. -/
private def subtypeCheck (source target : Ty) : Bool :=
  @decide (IsSubtype (fixtureStructure none) source target) (isSubtype_decidable (fixtureStructure none))

/-- The correlated function type is below the combined union-input, union-result requirement. -/
example : subtypeCheck correlated correlatedSummary = true := by
  decide +kernel

/-- The subtype decision rejects an unknown class name in the target exclusion. -/
example : subtypeCheck objectType (.negClass "Unknown") = false := by
  decide +kernel

/-- An unknown class name is rejected even when both annotations are identical. -/
example : subtypeCheck (.class_ "Unknown") (.class_ "Unknown") = false := by
  decide +kernel

/-- An empty source does not allow an unknown class name in the target. -/
example : subtypeCheck .bottom (.class_ "Unknown") = false := by
  decide +kernel

/-- The validity check reaches unknown class names inside a function input. -/
example : subtypeCheck
    (.callable (.class_ "Unknown") booleanType) methodType = false := by
  decide +kernel

/-- An empty intersection requires known class names in both operands. -/
example : subtypeCheck
    (.intersection .bottom (.class_ "Unknown")) .bottom = false := by
  decide +kernel

/-- A nonempty intersection with known Bool and Object names passes the subtype decision. -/
example : subtypeCheck (.intersection booleanType objectType) booleanType = true := by
  decide +kernel

/-- Expression checking rejects a requested type with an unknown class name. -/
example : checkHasType? fixtureWellFormed (Γ := [])
    (fun _ _ found => by cases found) .constTrue (.class_ "Unknown") = false := by
  decide +kernel

/-- The True expression is accepted at a requested intersection with known Bool and Object names. -/
example : checkHasType? fixtureWellFormed (Γ := [])
    (fun _ _ found => by cases found) .constTrue (.intersection booleanType objectType) = true := by
  decide +kernel

/-- Lookup sees the first x binding. Its later invalid binding is hidden. -/
private abbrev hiddenInvalidEnvironment : TyEnv :=
  [("x", booleanType), ("x", .class_ "Unknown")]

/-- Visible environment validity checks the first binding of each variable. -/
private theorem hiddenInvalidEnvironment_valid :
    WellFormedTyEnv (fixtureTable none) hiddenInvalidEnvironment := by
  intro name type found
  simp only [NamedEnv.lookup] at found
  split at found
  · cases found
    exact fixtureBoolValid
  · simp_all

/-- Inference uses the first binding when a variable name occurs twice. -/
example : checkHasType? fixtureWellFormed hiddenInvalidEnvironment_valid
    (.var "x") booleanType = true := by
  decide +kernel

/-- Reordering or repeating included names gives the same class-type expression. -/
example :
    (ClassIntersection.mk ["B", objectClass, "A", "A"]
      (by decide +kernel) (by decide +kernel) : ClassIntersection fixtureContext).toType.raw =
    (ClassIntersection.mk [objectClass, "A", "B"]
      (by decide +kernel) (by decide +kernel) : ClassIntersection fixtureContext).toType.raw := by
  decide +kernel

/-- The outer function type has a Bool-input, Bool-result function as its result type. -/
private def returnedBoolEnvironment : TyEnv :=
  [("f", .callable booleanType (.callable booleanType booleanType))]

/-- The returned function annotation uses only builtin class names. -/
private theorem returnedBoolEnvironmentValid :
    WellFormedTyEnv (fixtureTable none) returnedBoolEnvironment := by
  intro name type lookup
  simp only [returnedBoolEnvironment, NamedEnv.lookup] at lookup
  split at lookup
  · cases lookup
    decide +kernel
  · cases lookup

/-- Two calls preserve the single returned function's Bool result. -/
example : checkHasType? fixtureWellFormed returnedBoolEnvironmentValid
    (.call (.call (.var "f") .constTrue) .constTrue) booleanType = true := by
  decide +kernel

/-- The same two calls cannot be assigned NoneType. -/
example : checkHasType? fixtureWellFormed returnedBoolEnvironmentValid
    (.call (.call (.var "f") .constTrue) .constTrue) noneType = false := by
  decide +kernel

/-- The returned function type contains separate Bool and NoneType requirements. -/
private def returnedCorrelatedEnvironment : TyEnv :=
  [("f", .callable booleanType correlated)]

/-- Both returned requirements use only builtin class names. -/
private theorem returnedCorrelatedEnvironmentValid :
    WellFormedTyEnv (fixtureTable none) returnedCorrelatedEnvironment := by
  intro name type lookup
  simp only [returnedCorrelatedEnvironment, NamedEnv.lookup] at lookup
  split at lookup
  · cases lookup
    decide +kernel
  · cases lookup

/-- The second call uses the returned function's Bool-input requirement. -/
example : checkHasType? fixtureWellFormed returnedCorrelatedEnvironmentValid
    (.call (.call (.var "f") .constTrue) .constTrue) booleanType = true := by
  decide +kernel

/-- A None argument uses the returned function's NoneType-input requirement. -/
example : checkHasType? fixtureWellFormed returnedCorrelatedEnvironmentValid
    (.call (.call (.var "f") .constTrue) .constNone) noneType = true := by
  decide +kernel

/-- A NoneType argument is rejected when the second call's requested result is Bool. -/
example : checkHasType? fixtureWellFormed returnedCorrelatedEnvironmentValid
    (.call (.call (.var "f") .constTrue) .constNone) booleanType = false := by
  decide +kernel

/-- The returned correlated function and union-typed argument use only builtin class names. -/
private theorem returnedCorrelatedUnionEnvironmentValid :
    WellFormedTyEnv (fixtureTable none)
      (TyEnv.update [("f", .callable booleanType correlated), ("x", booleanType)]
        "x" (.union booleanType noneType)) :=
  wellFormedTyEnv_update
    (fixtureCallEnvironment_wellFormed _ (.callable fixtureBoolValid fixtureCorrelatedValid))
    (x := "x") rfl (.union fixtureBoolValid fixtureNoneValid)

/-- Covering both possible x inputs preserves both correlated result alternatives. -/
example : checkHasType? fixtureWellFormed returnedCorrelatedUnionEnvironmentValid
    (.call (.call (.var "f") .constTrue) (.var "x")) (.union booleanType noneType) = true := by
  decide +kernel

/-- The returned function's call is rejected at an intersected Bool-and-NoneType result. -/
example : checkHasType? fixtureWellFormed returnedCorrelatedUnionEnvironmentValid
    (.call (.call (.var "f") .constTrue) (.var "x")) (.intersection booleanType noneType) = false := by
  decide +kernel

/-- Combine two Bool-input function requirements.
Their result types are Bool -> (Bool | NoneType) and Bool -> (Bool | BoundMethod). -/
private def overlappingReturns
    (combine : WellFormedType ((fixtureTable none).map ClassDecl.name) →
      WellFormedType ((fixtureTable none).map ClassDecl.name) →
      WellFormedType ((fixtureTable none).map ClassDecl.name)) :
    WellFormedType ((fixtureTable none).map ClassDecl.name) :=
  combine
    (.callable fixtureBoolValid.toType
      (.callable fixtureBoolValid.toType (.union fixtureBoolValid.toType fixtureNoneValid.toType)))
    (.callable fixtureBoolValid.toType
      (.callable fixtureBoolValid.toType (.union fixtureBoolValid.toType fixtureMethodValid.toType)))

/-- Both intersected requirements in f and the Bool annotation on x use known builtin names. -/
private theorem overlappingIntersectionValid :
    WellFormedTyEnv (fixtureTable none)
      [("f", (overlappingReturns .intersection).raw), ("x", booleanType)] :=
  fixtureCallEnvironment_wellFormed _ (overlappingReturns .intersection).namesKnown

/-- Both union alternatives in f and the Bool annotation on x use known builtin names. -/
private theorem overlappingUnionValid :
    WellFormedTyEnv (fixtureTable none)
      [("f", (overlappingReturns .union).raw), ("x", booleanType)] :=
  fixtureCallEnvironment_wellFormed _ (overlappingReturns .union).namesKnown

/-- The intersected returned-function requirements give Bool as the second call's result. -/
example : checkHasType? fixtureWellFormed overlappingIntersectionValid
    (.call (.call (.var "f") .constTrue) .constTrue) booleanType = true := by
  decide +kernel

/-- The union callee's second Bool call is accepted at Bool | NoneType | BoundMethod. -/
example : checkHasType? fixtureWellFormed overlappingUnionValid
    (.call (.call (.var "f") .constTrue) .constTrue)
    (.union booleanType (.union noneType methodType)) = true := by
  decide +kernel

/-- The second alternative also permits BoundMethod results, so Bool-or-NoneType is insufficient. -/
example : checkHasType? fixtureWellFormed overlappingUnionValid
    (.call (.call (.var "f") .constTrue) .constTrue) (.union booleanType noneType) = false := by
  decide +kernel

/-- The first alternative also permits NoneType results, so Bool-or-BoundMethod is insufficient. -/
example : checkHasType? fixtureWellFormed overlappingUnionValid
    (.call (.call (.var "f") .constTrue) .constTrue) (.union booleanType methodType) = false := by
  decide +kernel

/-- These two direct call-result stages produce a candidate below Bool and skip
intersection closure for both calls. In full expression checking, the first
call's seven candidates expand to 127 before serving as callees for the second
call, whose results are also closed under intersection. This example isolates
call-result generation from those closures. -/
example :
    ((callResultsFromTy fixtureWellFormed.toWellFormedClassHierarchy (overlappingReturns .intersection)
      [fixtureBoolValid.toType]).flatMap fun callee =>
        callResultsFromTy fixtureWellFormed.toWellFormedClassHierarchy callee [fixtureBoolValid.toType]).any
      (fun result => @decide _
        (WellFormedType.subtypeDecidable fixtureWellFormed.toWellFormedClassHierarchy result fixtureBoolValid.toType))
      = true := by
  decide +kernel

/-- The same two stages produce no candidate below NoneType and skip intersection
closure for both call results. A full `checkHasType?` test at this target runs
past 300 seconds in kernel evaluation, so this example isolates call-result
generation. -/
example :
    ((callResultsFromTy fixtureWellFormed.toWellFormedClassHierarchy (overlappingReturns .intersection)
      [fixtureBoolValid.toType]).flatMap fun callee =>
        callResultsFromTy fixtureWellFormed.toWellFormedClassHierarchy callee [fixtureBoolValid.toType]).any
      (fun result => @decide _
        (WellFormedType.subtypeDecidable fixtureWellFormed.toWellFormedClassHierarchy result fixtureNoneValid.toType))
      = false := by
  decide +kernel

end FwPython.Examples.Static.Subtyping

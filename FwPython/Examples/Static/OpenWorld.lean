import FwPython.Static
import FwPython.Common

set_option autoImplicit false

/-! # Compatible and conflicting future class hierarchies

These examples check future inheritance through two classes with conflicting
MROs, a three-class order cycle, and a consistent diamond. They construct
extensions for independent classes and check that sealed Bool uses its existing
declaration. One comparison checks A's object lower bound against an exclusion
of B.
The subtype comparisons and class-table constructions are checked by Lean's kernel.

These hierarchy checks use `WellFormedClassHierarchy`: computed MROs and
builtin sealing. The method-conflict example also checks program requirements.
Its constructed common subclass has a valid MRO, but the selected method fails
LiskovCondition; therefore the extended declarations cannot have a
WellTypedClassHierarchy proof.
-/

namespace FwPython.Examples.Static.OpenWorld

open FwPython.Static.Subtyping

/-- An empty-method class with the supplied direct parent order. -/
private def declaration (name : Identifier) (parents : List Identifier := []) : Class :=
  ⟨name, parents, []⟩

/-- The four builtin classes. User declarations follow this prefix. -/
private def builtins : ClassTable :=
  [declaration objectClass, declaration boolClass, declaration noneClass, declaration boundMethodClass]

/-- A class without explicit parents has itself and Object as its MRO. -/
private def ordinaryMro (name : Identifier) : List Identifier :=
  if name = objectClass then [objectClass] else [name, objectClass]

/-- Certify an explicit expected MRO using the executable MRO search's soundness. -/
private def checkedMro {table : ClassTable} (expected : Identifier → List Identifier)
    (allComputed : ∀ declaration, declaration ∈ table →
      Common.MRO.computeMro? table declaration.name = some (expected declaration.name))
    (name : Identifier) (selected : Class) (lookup : findClass table name = some selected) :
    ClassMroWitness table selected := by
  refine ⟨expected name, ?_⟩
  have computed := allComputed selected (findClass_mem lookup)
  rw [findClass_name lookup] at computed
  obtain ⟨actual, actualLookup, proof⟩ := Common.MRO.computeMro?_sound computed
  rw [lookup] at actualLookup
  cases actualLookup
  exact proof

/-- Validate explicit MROs and sealing for a concrete builtin-prefix table. -/
private def checkedStructure (users : ClassTable) (expected : Identifier → List Identifier)
    (allComputed : ∀ selected, selected ∈ builtins ++ users →
      Common.MRO.computeMro? (builtins ++ users) selected.name = some (expected selected.name))
    (sealing : ∀ selected, selected ∈ builtins ++ users → ∀ builtin, builtin ∈ sealedClasses →
      builtin ∈ expected selected.name → selected.name = builtin) : WellFormedClassHierarchy (builtins ++ users) := by
  let mros := checkedMro expected allComputed
  refine
    { objectExists := ⟨declaration objectClass, rfl, rfl⟩
      boolExists := ⟨declaration boolClass, (mros boolClass _ rfl).mro, rfl, (mros boolClass _ rfl).hmro⟩
      noneExists := ⟨declaration noneClass, (mros noneClass _ rfl).mro, rfl, (mros noneClass _ rfl).hmro⟩
      boundMethodExists := ⟨declaration boundMethodClass, (mros boundMethodClass _ rfl).mro, rfl,
        (mros boundMethodClass _ rfl).hmro⟩
      allMrosExist := mros
      sealedLeaf := ?_ }
  intro builtin sealed name selected mro lookup computed present
  rw [determinism computed (mros name selected lookup).hmro] at present
  change builtin ∈ expected name at present
  rw [← findClass_name lookup] at present
  exact (findClass_name lookup).symm.trans (sealing selected (findClass_mem lookup) builtin sealed present)

/-- Reduce the recursive MRO search before the kernel checks a fixture's expected MROs. -/
local macro "checkFixtureMros" users:ident : tactic =>
  `(tactic| (simp [$users:ident, builtins, declaration, ordinaryMro,
      Common.MRO.computeMro?, Common.MRO.computeMroFuel?, Common.MRO.computeAllParentMrosFuel?,
      findClass, findByName, ClassDecl.resolvedBases, objectClass, boolClass, noneClass, boundMethodClass]
    <;> decide +kernel))

/-- A and B order their common parents in opposite ways. Each class itself is valid. -/
private def conflictingUsers : ClassTable :=
  [declaration "X", declaration "Y", declaration "A" ["X", "Y"], declaration "B" ["Y", "X"]]

/-- The current hierarchy contains both individually valid conflicting classes. -/
private def conflictingTable : ClassTable := builtins ++ conflictingUsers

/-- Every declared class has a valid MRO, and no user class inherits a sealed builtin. -/
private def conflictingStructure : WellFormedClassHierarchy conflictingTable :=
  checkedStructure conflictingUsers
    (fun name => if name = "A" then ["A", "X", "Y", objectClass]
      else if name = "B" then ["B", "Y", "X", objectClass] else ordinaryMro name)
    (by checkFixtureMros conflictingUsers)
    (by decide +kernel)

/-- A, B, and C form a three-way order cycle through X, Y, and Z. -/
private def cycleUsers : ClassTable :=
  [declaration "X", declaration "Y", declaration "Z", declaration "A" ["X", "Y"],
    declaration "B" ["Y", "Z"], declaration "C" ["Z", "X"]]

/-- The current hierarchy contains A, B, and C with the cyclic parent orders. -/
private def cycleTable : ClassTable := builtins ++ cycleUsers

/-- Every declared class has a valid MRO, and no user class inherits a sealed builtin. -/
private def cycleStructure : WellFormedClassHierarchy cycleTable :=
  checkedStructure cycleUsers
    (fun name => if name = "A" then ["A", "X", "Y", objectClass]
      else if name = "B" then ["B", "Y", "Z", objectClass]
      else if name = "C" then ["C", "Z", "X", objectClass] else ordinaryMro name)
    (by checkFixtureMros cycleUsers)
    (by decide +kernel)

/-- A and B have no parent relationship with each other. -/
private def independentUsers : ClassTable := [declaration "A", declaration "B"]

/-- The current hierarchy has no declared common subclass of A and B. -/
private def independentTable : ClassTable := builtins ++ independentUsers

/-- The independent classes and builtins have valid MROs. -/
private def independentStructure : WellFormedClassHierarchy independentTable :=
  checkedStructure independentUsers ordinaryMro
    (by checkFixtureMros independentUsers)
    (by decide +kernel)

/-- D forms a diamond through X and Y, with their common Object ancestor. -/
private def diamondUsers : ClassTable :=
  [declaration "X", declaration "Y", declaration "D" ["X", "Y"]]

/-- The diamond has a consistent MRO. -/
private def diamondTable : ClassTable := builtins ++ diamondUsers

/-- All diamond classes satisfy the MRO and sealing rules. -/
private def diamondStructure : WellFormedClassHierarchy diamondTable :=
  checkedStructure diamondUsers
    (fun name => if name = "D" then ["D", "X", "Y", objectClass] else ordinaryMro name)
    (by checkFixtureMros diamondUsers)
    (by decide +kernel)

/-- The type requiring both classes with conflicting MRO orders. -/
private def conflictingIntersection : WellFormedType (conflictingTable.map ClassDecl.name) :=
  .intersection (.class_ "A" (by decide +kernel)) (.class_ "B" (by decide +kernel))

/-- A and B each have a valid MRO, but those orders cannot be combined. -/
example : hasValidClassOrder (classContextOf conflictingTable conflictingStructure) ["A", "B"] = false := by
  decide +kernel

/-- The Boolean comparison accepts the impossible A-and-B intersection below bottom. -/
example : checkSubtypeBool conflictingStructure.typeContext conflictingIntersection .bottom = true := by
  decide +kernel

/-- `WellFormedType.subtypeDecidable` supplies the decision used by `of_decide_eq_true`.
The latter converts the computed true answer into an `IsSubtype` proof for the
incompatible-class intersection. -/
example : IsSubtype conflictingStructure (.intersection (.class_ "A") (.class_ "B")) .bottom := by
  exact @of_decide_eq_true _
    (WellFormedType.subtypeDecidable conflictingStructure conflictingIntersection .bottom)
    (by decide +kernel)

/-- No selected class in any valid extension can inherit both conflicting classes. -/
example (extension : ValidExtension conflictingTable) (selected : extension.SelectedClass) :
    ¬ ("A" ∈ selected.2.mro ∧ "B" ∈ selected.2.mro) := by
  intro included
  apply ValidExtension.noCommonClass conflictingStructure ["A", "B"]
    (by decide +kernel) extension selected
  intro name member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · exact included.1
  · exact included.2

/-- The conflicting-class input is empty, so BoundMethod is below this function requirement. -/
example : checkSubtypeBool conflictingStructure.typeContext (WellFormedTy.boundMethod conflictingStructure).toType
    (.callable conflictingIntersection (WellFormedTy.bool conflictingStructure).toType) = true := by
  decide +kernel

/-- Independent A and B make a nonempty input; BoundMethod alone is not below the same function requirement. -/
example : checkSubtypeBool independentStructure.typeContext (WellFormedTy.boundMethod independentStructure).toType
    (.callable (.intersection (.class_ "A" (by decide +kernel)) (.class_ "B" (by decide +kernel)))
      (WellFormedTy.bool independentStructure).toType) = false := by
  decide +kernel

/-- Each pair in the three-class cycle has a common order. -/
example :
    hasValidClassOrder (classContextOf cycleTable cycleStructure) ["A", "B"] = true ∧
    hasValidClassOrder (classContextOf cycleTable cycleStructure) ["B", "C"] = true ∧
    hasValidClassOrder (classContextOf cycleTable cycleStructure) ["C", "A"] = true := by
  decide +kernel

/-- Each pair in the three-class cycle remains a nonempty type intersection. -/
example :
    checkSubtypeBool cycleStructure.typeContext
      (.intersection (.class_ "A" (by decide +kernel)) (.class_ "B" (by decide +kernel))) .bottom = false ∧
    checkSubtypeBool cycleStructure.typeContext
      (.intersection (.class_ "B" (by decide +kernel)) (.class_ "C" (by decide +kernel))) .bottom = false ∧
    checkSubtypeBool cycleStructure.typeContext
      (.intersection (.class_ "C" (by decide +kernel)) (.class_ "A" (by decide +kernel))) .bottom = false := by
  decide +kernel

/-- The whole three-class cycle has no common order, despite its valid pairs. -/
example : hasValidClassOrder (classContextOf cycleTable cycleStructure) ["A", "B", "C"] = false := by
  decide +kernel

/-- The simultaneous three-class requirements in the order cycle compare below bottom. -/
example : checkSubtypeBool cycleStructure.typeContext
    (.intersection (.class_ "A" (by decide +kernel))
      (.intersection (.class_ "B" (by decide +kernel)) (.class_ "C" (by decide +kernel)))) .bottom = true := by
  decide +kernel

/-- Independent user classes can have a future common subclass; their intersection is not empty. -/
example : checkSubtypeBool independentStructure.typeContext
    (.intersection (.class_ "A" (by decide +kernel)) (.class_ "B" (by decide +kernel))) .bottom = false := by
  decide +kernel

/-- Class A is below B or A-without-B but below neither alternative alone.
The exact A object's lower bound excludes B. -/
example :
    checkSubtypeBool independentStructure.typeContext
      (.class_ "A" (by decide +kernel))
      (.union (.class_ "B" (by decide +kernel))
        (.intersection (.class_ "A" (by decide +kernel)) (.negClass "B" (by decide +kernel)))) = true ∧
    checkSubtypeBool independentStructure.typeContext
      (.class_ "A" (by decide +kernel)) (.class_ "B" (by decide +kernel)) = false ∧
    checkSubtypeBool independentStructure.typeContext
      (.class_ "A" (by decide +kernel))
      (.intersection (.class_ "A" (by decide +kernel)) (.negClass "B" (by decide +kernel))) = false ∧
    checkSubtypeBool independentStructure.typeContext
      (objectTypeLowerBound independentStructure "A" (by decide +kernel))
      (.negClass "B" (by decide +kernel)) = true := by
  decide +kernel

/-- The complete class conjunction includes both independent classes and Object. -/
private def bothClasses : ClassIntersection independentStructure.typeContext :=
  ⟨[objectClass, "A", "B"], by decide +kernel, by decide +kernel⟩

/-- The complete class conjunction includes A and Object and excludes B. -/
private def onlyAClasses : ClassIntersection independentStructure.typeContext :=
  ⟨[objectClass, "A"], by decide +kernel, by decide +kernel⟩

/-- A valid extension with a selected class whose original ancestors include both A and B. -/
private def bothRealization := extendWithClassIntersection independentStructure bothClasses

/-- A separate valid extension whose selected class includes A and excludes B among original names. -/
private def onlyARealization := extendWithClassIntersection independentStructure onlyAClasses

/-- The computed fresh-class MROs place their included ancestors in C3 order. -/
example :
    bothRealization.val.2.2.mro = bothRealization.val.2.1 :: ["A", "B", objectClass] ∧
    onlyARealization.val.2.2.mro = onlyARealization.val.2.1 :: ["A", objectClass] := by
  decide +kernel

/-- A conjunction containing sealed Bool selects the existing Bool class without adding declarations. -/
example :
    let realization := extendWithClassIntersection independentStructure
      (ClassIntersection.ofClassMro independentStructure.typeContext
        boolClass (by decide +kernel))
    realization.val.1.added = [] ∧ realization.val.2.1 = boolClass := by
  decide +kernel

/-- The constructed common subclass has no declared methods. -/
example : bothRealization.val.2.2.cls.methods = [] := by
  decide +kernel

/-- The original table does not declare the constructed common subclass. -/
example : findClass independentTable bothRealization.val.2.1 = none := by
  decide +kernel

/-- The constructed common-subclass extension appends exactly its selected class declaration. -/
example : bothRealization.val.1.added = [bothRealization.val.2.2.cls] := by
  decide +kernel

/-- Reordering or repeating included names preserves the conjunction's hierarchy constraints. -/
example : Admissible independentStructure.typeContext ["B", "A", objectClass, "A"] :=
  bothClasses.constraints.of_membership
    (fun name => by simp [bothClasses, List.mem_cons, or_comm, or_left_comm])

/-- Bool remains sealed; no future subclass can combine it with user class A. -/
example : checkSubtypeBool independentStructure.typeContext
    (.intersection (WellFormedTy.bool independentStructure).toType (.class_ "A" (by decide +kernel)))
    .bottom = true := by
  decide +kernel

/-- The diamond's own MRO keeps X before Y and lists Object once. -/
example : (classContextOf diamondTable diamondStructure).ancestors "D" = ["D", "X", "Y", objectClass] := rfl

/-- The diamond's ancestor conjunction passes the common-order check. -/
example : hasValidClassOrder (classContextOf diamondTable diamondStructure) [objectClass, "X", "Y", "D"] = true := by
  decide +kernel

/-- A Boolean identity method declared by A. -/
private def boolIdentityMethod : Method :=
  ⟨"m", "self", "x", .class_ boolClass, .class_ boolClass, .var "x"⟩

/-- A None identity method with the same name, declared independently by B. -/
private def noneIdentityMethod : Method :=
  ⟨"m", "self", "x", .class_ noneClass, .class_ noneClass, .var "x"⟩

/-- Independent classes with incompatible signatures for the same method name. -/
private def methodConflictUsers : ClassTable :=
  [⟨"A", [], [boolIdentityMethod]⟩, ⟨"B", [], [noneIdentityMethod]⟩]

/-- The methods do not alter the independent classes' valid MROs. -/
private def methodConflictStructure : WellFormedClassHierarchy (builtins ++ methodConflictUsers) :=
  checkedStructure methodConflictUsers ordinaryMro
    (by checkFixtureMros methodConflictUsers)
    (by decide +kernel)

/-- The class-membership conjunction admits a structurally valid common subclass. -/
private def methodConflictClasses : ClassIntersection methodConflictStructure.typeContext :=
  ⟨[objectClass, "A", "B"], by decide +kernel, by decide +kernel⟩

/-- The constructed empty-method subclass selects A's Bool-input method, which
does not accept the NoneType input required by B. This violates LiskovCondition.
WellTypedClassHierarchy requires that condition, so the extended table has no such proof. -/
example :
    let realization := (extendWithClassIntersection methodConflictStructure methodConflictClasses).val
    ¬ LiskovCondition realization.1.structural ∧
      ¬ Nonempty (WellTypedClassHierarchy ((builtins ++ methodConflictUsers) ++ realization.1.added)) := by
  dsimp only
  let realization := (extendWithClassIntersection methodConflictStructure methodConflictClasses).val
  let originalB := methodConflictStructure.lookupKnown "B" (by decide +kernel)
  have bLookup := findClass_append_preserved (builtins ++ methodConflictUsers) realization.1.added
    "B" originalB.cls originalB.hfind
  have bMro := ComputeMro.transport
    (findClass_append_preserved (builtins ++ methodConflictUsers) realization.1.added) originalB.hmro
  have selectedB : "B" ∈ realization.2.2.mro := by decide +kernel
  have methodFromA : findMethodInMro ((builtins ++ methodConflictUsers) ++ realization.1.added)
      realization.2.2.mro "m" = some boolIdentityMethod := by decide +kernel
  have methodFromB : findMethodInMro ((builtins ++ methodConflictUsers) ++ realization.1.added)
      originalB.mro "m" = some noneIdentityMethod := by decide +kernel
  have rejectsLiskov : ¬ LiskovCondition realization.1.structural := by
    intro condition
    have incompatible := (condition realization.2.1 "B"
      realization.2.2.cls originalB.cls realization.2.2.mro originalB.mro "m"
      boolIdentityMethod noneIdentityMethod realization.2.2.hfind realization.2.2.hmro
      selectedB bLookup bMro methodFromA methodFromB).1
    let originalNone := methodConflictStructure.noneExists
    have noneLookup := findClass_append_preserved (builtins ++ methodConflictUsers) realization.1.added
      noneClass originalNone.cls originalNone.hfind
    have noneMro := ComputeMro.transport
      (findClass_append_preserved (builtins ++ methodConflictUsers) realization.1.added) originalNone.hmro
    have wrongAncestor := class_subtype_mem_mro realization.1.structural incompatible noneLookup noneMro
    have equal := realization.1.structural.sealedLeaf boolClass (by simp [sealedClasses])
      noneClass originalNone.cls originalNone.mro noneLookup noneMro wrongAncestor
    exact (by decide +kernel : noneClass ≠ boolClass) equal

  refine ⟨rejectsLiskov, ?_⟩
  intro ⟨wellFormed⟩
  apply rejectsLiskov
  have equal : wellFormed.toWellFormedClassHierarchy = realization.1.structural := Subsingleton.elim _ _
  exact equal ▸ wellFormed.liskovCondition

/-- D inherits both diamond parents; their intersection also permits future classes other than D. -/
example :
    checkSubtypeBool diamondStructure.typeContext
      (.class_ "D" (by decide +kernel))
      (.intersection (.class_ "X" (by decide +kernel)) (.class_ "Y" (by decide +kernel))) = true ∧
    checkSubtypeBool diamondStructure.typeContext
      (.intersection (.class_ "X" (by decide +kernel)) (.class_ "Y" (by decide +kernel)))
      (.class_ "D" (by decide +kernel)) = false := by
  decide +kernel

end FwPython.Examples.Static.OpenWorld

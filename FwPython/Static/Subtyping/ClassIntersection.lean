import FwPython.Static.Subtyping.ClassContext
import FwPython.Common.ListSubsets

set_option autoImplicit false

/-! # Complete class conjunctions

A complete class conjunction includes some known class names and excludes every
other known name. Its constraints require Object, each included class's ancestors,
builtin sealing, and a common MRO order. The enumeration lists every complete
class conjunction satisfying these constraints. It uses each known name once to
avoid repeating identical conjunctions when declarations share a name.
-/

namespace FwPython.Static.Subtyping

/-- Included class names respect Object, inheritance, sealing and a common MRO order. -/
structure Admissible (context : ClassContext) (members : List Identifier) : Prop where
  /-- Object is among the included names. -/
  objectMember : objectClass ∈ members
  /-- Including a known class also includes every ancestor in its MRO. -/
  inheritance : ∀ name, name ∈ context.names → name ∈ members →
    ∀ ancestor, ancestor ∈ context.ancestors name → ancestor ∈ members
  /-- Including a sealed builtin requires every name in its MRO and excludes every other known name. -/
  sealing : ∀ builtin, builtin ∈ sealedClasses → builtin ∈ members →
    ∀ name, name ∈ context.names → (name ∈ members ↔ name ∈ context.ancestors builtin)
  /-- One order without repeated names can contain every included known class's MRO as a sublist. -/
  orderCompatible : hasValidClassOrder context members = true

/-- Decide the Object, inheritance, sealing, and common MRO constraints on the included names. -/
instance (context : ClassContext) (members : List Identifier) :
    Decidable (Admissible context members) :=
  decidable_of_iff
    (objectClass ∈ members ∧
      (∀ name, name ∈ context.names → name ∈ members →
        ∀ ancestor, ancestor ∈ context.ancestors name → ancestor ∈ members) ∧
      (∀ builtin, builtin ∈ sealedClasses → builtin ∈ members →
        ∀ name, name ∈ context.names → (name ∈ members ↔ name ∈ context.ancestors builtin)) ∧
      hasValidClassOrder context members = true)
    ⟨fun ⟨objectMember, inheritance, sealing, orderCompatible⟩ =>
        ⟨objectMember, inheritance, sealing, orderCompatible⟩,
      fun permitted => ⟨permitted.objectMember, permitted.inheritance, permitted.sealing, permitted.orderCompatible⟩⟩

/-- Equal included names preserve the class conjunction constraints. -/
theorem Admissible.of_membership {context : ClassContext} {first second : List Identifier}
    (permitted : Admissible context first) (same : ∀ name, name ∈ first ↔ name ∈ second) :
    Admissible context second :=
  { objectMember := (same objectClass).mp permitted.objectMember
    inheritance := by simpa only [same] using permitted.inheritance
    sealing := by simpa only [same] using permitted.sealing
    orderCompatible := hasValidClassOrder_of_subset permitted.orderCompatible
      (fun name _ present => (same name).mpr present) }

/-- List every subset of distinct known names that satisfies the class conjunction constraints. -/
private def classIntersectionLists (context : ClassContext) : List (List Identifier) :=
  (subsequences context.names.eraseDups).filter (fun members => decide (Admissible context members))

/-- A complete class conjunction includes some known names and excludes the rest.
The included names satisfy the Object, inheritance, sealing and common-MRO constraints.
For example, including A and B requires their ancestors, including Object, and
a common order for their MROs. The included list is not itself an MRO. -/
structure ClassIntersection (context : ClassContext) where
  /-- Included class names; all other known names occur as class exclusions. -/
  includedClasses : List Identifier
  /-- All included class names belong to the context. -/
  namesKnown : ∀ {name}, name ∈ includedClasses → name ∈ context.names
  /-- Object, inheritance, sealing and common MRO-order constraints on the included names. -/
  constraints : Admissible context includedClasses

/-- Check whether the named class is included in the conjunction. -/
def ClassIntersection.includesClass {context : ClassContext} (conjunction : ClassIntersection context)
    (name : Identifier) : Bool := conjunction.includedClasses.contains name

/-- A class is included exactly when its name occurs in the included-name list. -/
theorem ClassIntersection.includesClass_iff_mem {context : ClassContext}
    (conjunction : ClassIntersection context) (name : Identifier) :
    conjunction.includesClass name = true ↔ name ∈ conjunction.includedClasses :=
  List.contains_iff_mem

/-- Both complete class conjunctions include the same known class names.
List order and repeated names do not affect this comparison. Keeping the
predicate transparent lets Lean infer its finite decision procedure. -/
abbrev ClassIntersection.sameClasses {context : ClassContext}
    (first second : ClassIntersection context) : Prop :=
  ∀ name, name ∈ context.names → first.includesClass name = second.includesClass name

/-- Attach class conjunction constraints to one enumerated included-name list. -/
private def ClassIntersection.ofEnumeration (context : ClassContext)
    (entry : {members : List Identifier // members ∈ classIntersectionLists context}) : ClassIntersection context :=
  ⟨entry.1, (fun h => List.mem_eraseDups.mp ((mem_subsequences.mp (List.mem_filter.mp entry.2).1).subset h)),
    of_decide_eq_true (List.mem_filter.mp entry.2).2⟩

/-- All complete class conjunctions allowed by the context's constraints. -/
def classIntersections (context : ClassContext) : List (ClassIntersection context) :=
  (classIntersectionLists context).attach.map (ClassIntersection.ofEnumeration context)

/-- Every inclusion function satisfying the conjunction constraints has an enumerated
conjunction including exactly the same known names. Enumeration lists each name once in context order. -/
theorem classIntersections_complete (context : ClassContext) (includes : Identifier → Bool)
    (constraints : Admissible context (context.names.eraseDups.filter includes)) :
    ∃ enumerated, enumerated ∈ classIntersections context ∧
      ∀ name, name ∈ context.names → enumerated.includesClass name = includes name := by
  let members := context.names.eraseDups.filter includes
  let entry : {members // members ∈ classIntersectionLists context} :=
    ⟨members, List.mem_filter.mpr
      ⟨mem_subsequences.mpr (List.filter_sublist ..), decide_eq_true constraints⟩⟩
  refine ⟨ClassIntersection.ofEnumeration context entry,
    List.mem_map.mpr ⟨entry, List.mem_attach _ _, rfl⟩, ?_⟩
  intro name known
  apply Bool.eq_iff_iff.mpr
  rw [ClassIntersection.includesClass_iff_mem]
  change name ∈ context.names.eraseDups.filter includes ↔ includes name = true
  simp only [List.mem_filter, List.mem_eraseDups, known, true_and]

/-- Include the known class's MRO names in their method resolution order. -/
def ClassIntersection.ofClassMro (context : ValidatedClassContext)
    (name : Identifier) (known : name ∈ context.names) : ClassIntersection context :=
  let valid := context.valid
  ⟨context.ancestors name, (fun h => valid.ancestorsKnown name known _ h),
    ⟨valid.objectAncestor name known,
      fun ancestor _ present higher higherPresent =>
        (valid.ancestorOrder name known ancestor present).subset higherPresent,
      fun builtin sealed present ancestor _ => by
        rw [valid.sealed builtin sealed name known present],
      hasValidClassOrder_of_sublist (context.ancestors name) (valid.ancestorDistinct name known)
        (fun ancestor _ present => valid.ancestorOrder name known ancestor present)⟩⟩

/-- The constructed conjunction includes exactly the class's MRO names. -/
theorem ClassIntersection.ofClassMro_includesClass (context : ValidatedClassContext)
    (name : Identifier) (known : name ∈ context.names) (ancestor : Identifier) :
    (ClassIntersection.ofClassMro context name known).includesClass ancestor = true ↔
      ancestor ∈ context.ancestors name :=
  ClassIntersection.includesClass_iff_mem _ ancestor

/-- The complete class conjunction from BoundMethod's MRO includes BoundMethod itself. -/
theorem ClassIntersection.boundMethod_includesSelf (context : ValidatedClassContext) :
    (ClassIntersection.ofClassMro context boundMethodClass
      context.valid.boundMethodKnown).includesClass boundMethodClass = true :=
  (ClassIntersection.ofClassMro_includesClass context
    boundMethodClass context.valid.boundMethodKnown boundMethodClass).mpr
    (context.valid.selfAncestor boundMethodClass context.valid.boundMethodKnown)

/-- A conjunction including sealed BoundMethod includes exactly the names in its MRO. -/
theorem ClassIntersection.boundMethod_includesClass {context : ValidatedClassContext}
    (conjunction : ClassIntersection context) (isMethod : conjunction.includesClass boundMethodClass = true)
    (name : Identifier) :
    conjunction.includesClass name =
      (ClassIntersection.ofClassMro context boundMethodClass context.valid.boundMethodKnown).includesClass name := by
  apply Bool.eq_iff_iff.mpr
  rw [conjunction.includesClass_iff_mem name, ClassIntersection.ofClassMro_includesClass]
  by_cases known : name ∈ context.names
  · exact conjunction.constraints.sealing _ (by simp [sealedClasses])
      ((conjunction.includesClass_iff_mem boundMethodClass).mp isMethod) name known
  · exact ⟨fun h => (known (conjunction.namesKnown h)).elim, fun h =>
      (known (context.valid.ancestorsKnown _ context.valid.boundMethodKnown _ h)).elim⟩

end FwPython.Static.Subtyping

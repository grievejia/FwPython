import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.Equations
import FwPython.Static.Subtyping.Normalization

set_option autoImplicit false

/-! # Algebraic lower bounds for object references

An object's actual MRO determines a complete class conjunction. For BoundMethod,
the lower-bound type also includes Object -> bottom, which lies below every valid
function annotation. For a well-formed static class table and heap,
`valueHasType_lowerBound` proves that the bound lies below every type assigned
to a reference of that exact object.

`objectTypeLowerBound_negClass_iff` says that the bound is below a known class's
exclusion exactly when that class is outside the object's MRO. The object's own
class is in its MRO, so the bound cannot be below its own exclusion. A bound below
bottom would be below that exclusion, giving a contradiction. This proves nonemptiness.
-/

namespace FwPython.Static.Subtyping

open TypeEquivalence

variable {ct : ClassTable}

/-- The lower-bound intersection for an object class follows its actual MRO.
For BoundMethod, its function list contains Object -> bottom, which lies below
every valid function annotation. -/
private def objectLowerIntersection (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) : TypeIntersection structural.typeContext :=
  let context := structural.typeContext
  let conjunction := ClassIntersection.ofClassMro context name known
  let functions : List (WellFormedType context.names × WellFormedType context.names) :=
    if name = boundMethodClass then [(context.objectType, .bottom)] else []
  ⟨conjunction, functions, fun nonempty => by
    by_cases method : name = boundMethodClass
    · subst name
      exact ClassIntersection.boundMethod_includesSelf context
    · exact (nonempty (by simp only [functions, if_neg method])).elim⟩

/-- Include the classes in the exact heap class's MRO and exclude every other
known class name. For BoundMethod, intersect this conjunction with Object -> bottom.
In a well-formed static class table and heap, `valueHasType_lowerBound` proves that
this type lies below every type assigned to a reference whose object has exactly
this class. -/
def objectTypeLowerBound (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) : WellFormedType (ct.map ClassDecl.name) :=
  (objectLowerIntersection structural name known).toType

/-- An intersection is below a known class type or exclusion exactly when its
complete class conjunction includes or excludes that name. -/
private theorem intersection_classLiteral_iff {context : ValidatedClassContext}
    (source : TypeIntersection context) (name : Identifier) (known : name ∈ context.names) (positive : Bool) :
    Subtype context source.toType.raw (WellFormedType.classLiteral name known positive).raw ↔
      source.classIntersection.includesClass name = positive := by
  constructor
  · intro included
    obtain ⟨intersection, member⟩ := (splitIntoIntersections_of_intersection context source).1
    have assigned := (splitIntoIntersections_of_intersection context source).2 intersection member
    exact (assigned.1 name known).symm.trans
      (classLiteral_includesClass_of_subtype context source.toType name known positive included intersection member)
  · intro answer
    simpa only [answer] using source.subtype_classLiteral name known

/-- The lower bound lies below a class type exactly when that name is in the object's actual MRO. -/
theorem objectTypeLowerBound_class_iff (structural : WellFormedClassHierarchy ct)
    (name target : Identifier) (known : name ∈ ct.map ClassDecl.name) :
    IsSubtype structural (objectTypeLowerBound structural name known).raw (.class_ target) ↔
      target ∈ structural.typeContext.ancestors name := by
  have classAnswer := ClassIntersection.ofClassMro_includesClass structural.typeContext name known target
  constructor
  · intro included
    have targetKnown : target ∈ ct.map ClassDecl.name := by
      cases included.targetWellFormed
      assumption
    exact classAnswer.mp ((intersection_classLiteral_iff (objectLowerIntersection structural name known)
      target targetKnown true).mp included)
  · intro inherited
    exact (intersection_classLiteral_iff (objectLowerIntersection structural name known)
      target (structural.typeContext.valid.ancestorsKnown name known target inherited) true).mpr
        (classAnswer.mpr inherited)

/-- The object's lower bound lies below the type of its own exact heap class. -/
theorem objectTypeLowerBound_ownClass (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) :
    IsSubtype structural (objectTypeLowerBound structural name known).raw (.class_ name) :=
  (objectTypeLowerBound_class_iff structural name name known).mpr
    (structural.typeContext.valid.selfAncestor name known)

/-- A positive class requirement of the object's lower bound occurs in its computed MRO. -/
theorem objectTypeLowerBound_mem_mro (structural : WellFormedClassHierarchy ct)
    {name target : Identifier} {declaration : Class} {linearization : List Identifier}
    (lookup : findClass ct name = some declaration)
    (computed : ComputeMro ct declaration linearization)
    (included : IsSubtype structural
      (objectTypeLowerBound structural name (findClass_name_known lookup)).raw (.class_ target)) :
    target ∈ linearization := by
  have inherited := (objectTypeLowerBound_class_iff structural name target (findClass_name_known lookup)).mp included
  simpa only [structural.typeContext_mro lookup computed] using inherited

/-- The lower bound excludes precisely the known class names absent from the object's actual MRO. -/
theorem objectTypeLowerBound_negClass_iff (structural : WellFormedClassHierarchy ct)
    (name target : Identifier) (known : name ∈ ct.map ClassDecl.name)
    (targetKnown : target ∈ ct.map ClassDecl.name) :
    IsSubtype structural (objectTypeLowerBound structural name known).raw (.negClass target) ↔
      target ∉ structural.typeContext.ancestors name :=
  (intersection_classLiteral_iff (objectLowerIntersection structural name known) target targetKnown false).trans
    (Bool.eq_false_iff.trans
      (not_congr (ClassIntersection.ofClassMro_includesClass structural.typeContext name known target)))

/-- The lower-bound type of an object with a known class is not a subtype of bottom. -/
theorem objectTypeLowerBound_nonempty (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) :
    ¬ IsSubtype structural (objectTypeLowerBound structural name known).raw .bottom := by
  intro included
  have excluded := (objectTypeLowerBound_negClass_iff structural name name known known).mp
    (.trans included (.bottom (.negClass known)))
  exact excluded (structural.typeContext.valid.selfAncestor name known)

/-- The object's lower bound is below a valid union exactly when it is below one alternative. -/
theorem objectTypeLowerBound_union_iff (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) {left right : Ty}
    (unionValid : WellFormedTy ct (.union left right)) :
    IsSubtype structural (objectTypeLowerBound structural name known).raw (.union left right) ↔
      IsSubtype structural (objectTypeLowerBound structural name known).raw left ∨
      IsSubtype structural (objectTypeLowerBound structural name known).raw right := by
  let source := objectLowerIntersection structural name known
  let leftType : WellFormedType structural.typeContext.names := ⟨left, unionValid.union_left⟩
  let rightType : WellFormedType structural.typeContext.names := ⟨right, unionValid.union_right⟩
  simpa only [splitIntoIntersections_union, List.mem_append, or_and_right, exists_or,
    ← source.subtype_iff leftType, ← source.subtype_iff rightType] using
      source.subtype_iff (.union leftType rightType)

/-- The object's lower bound is a subtype of a valid function type exactly when
its heap class is BoundMethod. -/
theorem objectTypeLowerBound_callable_iff (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) {parameter result : Ty}
    (functionValid : WellFormedTy ct (.callable parameter result)) :
    IsSubtype structural (objectTypeLowerBound structural name known).raw (.callable parameter result) ↔
      name = boundMethodClass := by
  constructor
  · intro included
    have inherited := (objectTypeLowerBound_class_iff structural name boundMethodClass known).mp
        (.trans included (.callableBoundMethod functionValid.callable_param functionValid.callable_return))
    exact structural.typeContext.valid.sealed boundMethodClass (by simp [sealedClasses]) name known inherited
  · intro same
    subst name
    let context := structural.typeContext
    let intersection := objectLowerIntersection structural boundMethodClass known
    exact .trans
      (toSubtype (intersection.functionIntersection_equation
        (ClassIntersection.boundMethod_includesSelf context)))
      (.trans (WellFormedType.functionIntersection_subtype List.mem_cons_self)
        (.callable (.objectTop functionValid.callable_param) (.bottom functionValid.callable_return)))

end FwPython.Static.Subtyping

import FwPython.Static.Subtyping.SubtypeCheck

set_option autoImplicit false

/-! # Algebraic derivations from subtype comparison

On the intersection of a nonempty subset's inputs, all of its result requirements
apply. Unions of these inputs describe the coverage available from a collection
of subsets. Induction on function nesting turns accepted coverage comparisons into
algebraic subtype derivations, because the recursive input and result comparisons
have shallower function types.

`checkSubtypeBool_iff_subtype` proves that the comparison accepts exactly the
pairs with subtype derivations. For one `TypeIntersection` record, `TypeIntersection.subtype_iff`
identifies a matching target intersection and its input coverage requirements.
`functionIntersection_subtype_iff` specializes this to an intersection of function requirements
and one requested function type.
-/

namespace FwPython.Static.Subtyping

open TypeEquivalence

/-- A function on a finite union of inputs equals BoundMethod intersected with
the functions on each input. For the empty union, both sides equal BoundMethod. -/
private theorem equational_input_union (context : ValidatedClassContext)
    (inputs : List (WellFormedType context.names)) (result : WellFormedType context.names) :
    TypeEquivalence context (.callable (.joinTypes inputs) result)
      (.intersection context.boundMethodType
        (.meetTypes context.valid.objectKnown (inputs.map fun input => .callable input result))) := by
  induction inputs with
  | nil => exact .trans .functionEmptyInput intersectionObject.symm
  | cons head tail inductionHypothesis =>
      exact .trans .functionUnionInput (.trans (.intersection .refl inductionHypothesis)
        (.trans intersectionAssociative.symm
          (.trans (.intersection .intersectionCommutative .refl) .intersectionAssociative)))

/-- Function types on one input with a nonempty list of results intersect to the
function type whose result is the meet of those results. -/
private theorem equational_result_intersection (context : ValidatedClassContext)
    (input first : WellFormedType context.names) (rest : List (WellFormedType context.names)) :
    TypeEquivalence context
      (.meetTypes context.valid.objectKnown ((first :: rest).map (WellFormedType.callable input)))
      (.callable input (.meetTypes context.valid.objectKnown (first :: rest))) := by
  induction rest generalizing first with
  | nil => exact .trans .intersectionObject (.callable .refl intersectionObject.symm)
  | cons next rest inductionHypothesis =>
      exact .trans (.intersection .refl (inductionHypothesis next)) functionIntersectionResult.symm

/-- The source function intersection is below a function with the union of the
listed subsets' input meets as its input, provided each listed subset is a
nonempty subset of the source and its result meet is below the required result. -/
theorem subsetCollection_subtype (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (collection : List (List (WellFormedType context.names × WellFormedType context.names)))
    (result : WellFormedType context.names)
    (members : ∀ subset ∈ collection, subset ∈ nonemptySubsets source)
    (results : ∀ subset ∈ collection, Subtype context
      (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)).raw result.raw) :
    Subtype context (WellFormedType.functionIntersection context source).raw
      (WellFormedType.callable (WellFormedType.joinTypes (collection.map fun subset =>
        .meetTypes context.valid.objectKnown (subset.map Prod.fst))) result).raw := by
  let inputs := collection.map fun subset => WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst)
  refine .trans (.interIntro (WellFormedType.functionIntersection_boundMethod source)
    (subtype_meetTypes ?_)) (toSubtype (equational_input_union context inputs result).symm)
  intro type member
  obtain ⟨_, inputMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨subset, subsetMember, rfl⟩ := List.mem_map.mp inputMember
  let input := WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst)
  have selected := mem_nonemptySubsets.mp (members subset subsetMember)
  cases subset with
  | nil => exact (selected.2 rfl).elim
  | cons first rest =>
      refine .trans (.trans (subtype_meetTypes
        (types := (first :: rest).map fun signature => .callable input signature.2) ?_) ?_)
        (.callable (.refl input.namesKnown) (results (first :: rest) subsetMember))
      · intro type typeMember
        obtain ⟨signature, signatureMember, rfl⟩ := List.mem_map.mp typeMember
        exact .trans
          (WellFormedType.functionIntersection_subtype
            ((mem_subsequences.mp selected.1).subset signatureMember))
          (.callable (meetTypes_subtype (List.mem_map.mpr ⟨signature, signatureMember, rfl⟩))
            (.refl signature.2.namesKnown))
      · simpa only [List.map_cons, List.map_map] using
          toSubtype (equational_result_intersection context input first.2 (rest.map Prod.snd))

/-- Function-nesting induction turns an accepted comparison into an equation-derived subtype. -/
private theorem subtype_of_checkSubtypeBool (context : ValidatedClassContext) (height : Nat)
    (source target : WellFormedType context.names)
    (sourceHeight : callableHeight source.raw ≤ height) (targetHeight : callableHeight target.raw ≤ height)
    (accepted : checkSubtypeBool context source target = true) :
    Subtype context source.raw target.raw := by
  induction height using Nat.strongRecOn generalizing source target with
  | ind height inductionHypothesis =>
      let sourceSplit := splitIntoIntersections context source
      let targetSplit := splitIntoIntersections context target
      refine Subtype.trans (toSubtype sourceSplit.equivalentToSource)
        (joinTypes_subtype fun type member => ?_)
      obtain ⟨first, firstMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨second, secondMember, same, covers⟩ :=
        (checkSubtypeBool_iff_intersections context source target).mp accepted first firstMember
      have firstHeights := sourceSplit.retainedWithinHeight (height := height - 1) (by omega) firstMember
      have classBound := second.classIntersection.subtype_toType fun name known => by
        rw [← same name known]
        exact first.subtype_classLiteral name known
      have functionBounds (requirement : WellFormedType context.names × WellFormedType context.names)
          (required : requirement ∈ second.functionTypes) :
          Subtype context first.toType.raw (WellFormedType.callable requirement.1 requirement.2).raw := by
        have secondHeight := targetSplit.functionHeights second secondMember requirement required
        refine .trans (toSubtype (first.functionIntersection_equation
          ((same boundMethodClass context.valid.boundMethodKnown).trans
            (second.functionsRequireBoundMethod (List.ne_nil_of_mem required)))))
          (.trans (U := (WellFormedType.callable
            (inputTypeForResult context first.functionTypes requirement.2) requirement.2).raw)
            ?_ (.callable ?_ (.refl requirement.2.namesKnown)))
        · rw [inputTypeForResult_eq_join, subsetsWithResultBelow_eq_filter]
          apply subsetCollection_subtype context first.functionTypes _ requirement.2
          · intro subset listed
            exact (List.mem_filter.mp listed).1
          · intro subset selected
            obtain ⟨listed, accepted⟩ := List.mem_filter.mp selected
            exact inductionHypothesis (height - 1) (by omega) _ _
              (WellFormedType.projectedMeet_height Prod.snd (mem_nonemptySubsets.mp listed).1
                (fun pair member => (firstHeights pair member).2)) (by omega) accepted
        · exact inductionHypothesis (height - 1) (by omega) _ _ (by omega)
            (inputTypeForResult_height context first.functionTypes requirement.2 (height - 1) firstHeights)
            (covers requirement required)
      exact .trans (second.subtype_toType classBound functionBounds)
        (.trans (subtype_joinTypes (List.mem_map.mpr ⟨second, secondMember, rfl⟩))
          (toSubtype targetSplit.equivalentToSource.symm))

/-- A valid type pair is accepted exactly when the source is a subtype of the target. -/
theorem checkSubtypeBool_iff_subtype (context : ValidatedClassContext)
    (source target : WellFormedType context.names) :
    checkSubtypeBool context source target = true ↔
      Subtype context source.raw target.raw :=
  ⟨subtype_of_checkSubtypeBool context (max (callableHeight source.raw) (callableHeight target.raw))
      source target (Nat.le_max_left _ _) (Nat.le_max_right _ _),
    checkSubtypeBool_of_subtype context source target⟩

/-- The type represented by one `TypeIntersection` record is below a valid target exactly
when one target intersection has the same included class names and the source functions
cover each target input for its result. -/
theorem TypeIntersection.subtype_iff {context : ValidatedClassContext}
    (source : TypeIntersection context) (target : WellFormedType context.names) :
    Subtype context source.toType.raw target.raw ↔
      ∃ intersection, intersection ∈ (splitIntoIntersections context target).intersections ∧
        ClassIntersection.sameClasses source.classIntersection intersection.classIntersection ∧
        ∀ requirement ∈ intersection.functionTypes,
          Subtype context requirement.1.raw (inputTypeForResult context source.functionTypes requirement.2).raw := by
  have represented := splitIntoIntersections_of_intersection context source
  rw [← checkSubtypeBool_iff_subtype, checkSubtypeBool_iff_intersections]
  constructor
  · intro compared
    obtain ⟨produced, producedMember⟩ := represented.1
    obtain ⟨selected, selectedMember, same, covered⟩ := compared produced producedMember
    have assigned := represented.2 produced producedMember
    rw [assigned.2] at covered
    exact ⟨selected, selectedMember, fun name known => (assigned.1 name known).symm.trans (same name known),
      fun requirement required => (checkSubtypeBool_iff_subtype context _ _).mp (covered requirement required)⟩
  · rintro ⟨selected, selectedMember, same, covered⟩ produced producedMember
    have assigned := represented.2 produced producedMember
    rw [assigned.2]
    exact ⟨selected, selectedMember, fun name known => (assigned.1 name known).trans (same name known),
      fun requirement required => (checkSubtypeBool_iff_subtype context _ _).mpr (covered requirement required)⟩

/-- The simultaneous result of a selected source subset is below the requested result. -/
theorem subsetsWithResultBelow_result_subtype (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names)
    (subset : List (WellFormedType context.names × WellFormedType context.names))
    (selected : subset ∈ subsetsWithResultBelow context source result) :
    Subtype context (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)).raw result.raw := by
  rw [subsetsWithResultBelow_eq_filter] at selected
  exact (checkSubtypeBool_iff_subtype context _ result).mp (List.mem_filter.mp selected).2

/-- A subtype of a class literal has that literal in every entry of its normal form. -/
theorem classLiteral_includesClass_of_subtype (context : ValidatedClassContext)
    (source : WellFormedType context.names) (name : Identifier) (known : name ∈ context.names) (positive : Bool)
    (included : Subtype context source.raw (WellFormedType.classLiteral name known positive).raw) :
    ∀ intersection, intersection ∈ (splitIntoIntersections context source).intersections →
      intersection.classIntersection.includesClass name = positive :=
  (checkSubtypeBool_classLiteral_iff context source name known positive).mp
    (checkSubtypeBool_of_subtype context source _ included)

/-- The source function intersection is below the target function exactly when its
input coverage for the target result is above the target input. -/
theorem functionIntersection_subtype_iff (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (parameter result : WellFormedType context.names) :
    Subtype context (WellFormedType.functionIntersection context source).raw
        (WellFormedType.callable parameter result).raw ↔
      Subtype context parameter.raw (inputTypeForResult context source result).raw := by
  constructor
  · intro included
    let intersection := TypeIntersection.ofFunctions context source
    obtain ⟨_, member, _, covered⟩ :=
      (intersection.subtype_iff (.callable parameter result)).mp
        (.trans (toSubtype (intersection.functionIntersection_equation
          (ClassIntersection.boundMethod_includesSelf context))) included)
    rw [splitIntoIntersections_callable] at member
    cases List.mem_singleton.mp member
    exact covered (parameter, result) (List.mem_singleton_self _)
  · intro coverageBound
    rw [inputTypeForResult_eq_join] at coverageBound
    exact .trans (subsetCollection_subtype context source
      (subsetsWithResultBelow context source result) result
      (fun subset member => by
        rw [subsetsWithResultBelow_eq_filter] at member
        exact (List.mem_filter.mp member).1)
      (subsetsWithResultBelow_result_subtype context source result))
      (.callable coverageBound (.refl result.namesKnown))

end FwPython.Static.Subtyping

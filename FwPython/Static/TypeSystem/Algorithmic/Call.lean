import FwPython.Static.TypeSystem.Typing
import FwPython.Static.Subtyping.Decision
import FwPython.Static.Subtyping.Equations
import FwPython.Static.Subtyping.Normalization
import FwPython.Static.Subtyping.SubtypeCheck
import FwPython.Static.Subtyping.Lattice
import FwPython.Common.ListSubsets

/-! # Input and result types for call checking

Each function requirement stores valid input and result types.
The checker combines requirements to cover every statically accepted call.
The package operations preserve validity while constructing these combinations.
-/

open FwPython.Static.Subtyping

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- Valid input and result pairs that cover every function requirement of the source. -/
structure CallableSummaries {ct : ClassTable} (structural : WellFormedClassHierarchy ct)
    (source : WellFormedType (ct.map ClassDecl.name)) where
  /-- The input and result types considered by call checking. -/
  requirements : List (WellFormedType (ct.map ClassDecl.name) × WellFormedType (ct.map ClassDecl.name))
  /-- The source type lies below the function type described by each listed pair. -/
  sound : ∀ pair ∈ requirements, IsSubtype structural source.raw (.callable pair.1.raw pair.2.raw)
  /-- Every required function type has a pair covering its inputs with a result below the required result. -/
  complete : ∀ P R, IsSubtype structural source.raw (.callable P R) →
    ∃ pair, pair ∈ requirements ∧ IsSubtype structural P pair.1.raw ∧ IsSubtype structural pair.2.raw R

/-- Transport callable requirements along an equation between their source types. -/
private def CallableSummaries.ofEquation
    (equation : TypeEquivalence structural.typeContext source target)
    (summaries : CallableSummaries structural target) : CallableSummaries structural source where
  requirements := summaries.requirements
  sound := fun pair member => .trans (TypeEquivalence.toSubtype equation) (summaries.sound pair member)
  complete := fun P R included => summaries.complete P R
    (.trans (TypeEquivalence.toSubtype equation.symm) included)

/-- The input and result annotations represented by the packaged requirements. -/
def CallableSummaries.pairs (summaries : CallableSummaries structural source) : List (Ty × Ty) :=
  summaries.requirements.map fun pair => (pair.1.raw, pair.2.raw)

/-- Enumerate input and result pairs for a function intersection. The source is
below each listed function type. For any function type above the source, a listed
pair accepts all its required inputs and has a result below its required result type. -/
private def functionSummaries (structural : WellFormedClassHierarchy ct)
    (source : List (WellFormedType (ct.map ClassDecl.name) × WellFormedType (ct.map ClassDecl.name))) :
    CallableSummaries structural (WellFormedType.functionIntersection structural.typeContext source) := by
  let context := structural.typeContext
  -- Union the subsets' input intersections and their result intersections separately.
  let summarize (collection : List (List (WellFormedType context.names × WellFormedType context.names))) :
      WellFormedType context.names × WellFormedType context.names :=
    (.joinTypes (collection.map fun subset => .meetTypes context.valid.objectKnown (subset.map Prod.fst)),
     .joinTypes (collection.map fun subset => .meetTypes context.valid.objectKnown (subset.map Prod.snd)))
  refine
    { requirements := (subsequences (nonemptySubsets source)).map summarize
      sound := ?_
      complete := ?_ }
  · intro pair member
    obtain ⟨collection, collectionMember, rfl⟩ := List.mem_map.mp member
    apply subsetCollection_subtype context source collection (summarize collection).2
    · exact fun subset member => (mem_subsequences.mp collectionMember).subset member
    · exact fun subset member => subtype_joinTypes (List.mem_map.mpr ⟨subset, member, rfl⟩)
  · intro P R included
    let parameter : WellFormedType context.names := ⟨P, included.targetWellFormed.callable_param⟩
    let result : WellFormedType context.names := ⟨R, included.targetWellFormed.callable_return⟩
    let collection := subsetsWithResultBelow context source result
    have collectionMember : collection ∈ subsequences (nonemptySubsets source) := by
      dsimp only [collection]
      rw [subsetsWithResultBelow_eq_filter]
      exact mem_subsequences.mpr (List.filter_sublist ..)
    refine ⟨summarize collection, List.mem_map.mpr ⟨collection, collectionMember, rfl⟩, ?_, ?_⟩
    · simpa only [inputTypeForResult_eq_join] using
        (functionIntersection_subtype_iff context source parameter result).mp included
    · refine joinTypes_subtype (target := result) fun type member => ?_
      obtain ⟨subset, subsetMember, rfl⟩ := List.mem_map.mp member
      exact subsetsWithResultBelow_result_subtype context source result subset subsetMember

/-- Intersect inputs and union results for two possible source alternatives. -/
private def combineCallableSummaries
    (left : CallableSummaries structural first) (right : CallableSummaries structural second) :
    CallableSummaries structural (.union first second) where
  requirements := left.requirements.flatMap fun l => right.requirements.map fun r =>
    (.intersection l.1 r.1, .union l.2 r.2)
  sound := by
    intro pair member
    obtain ⟨l, hl, r, hr, rfl⟩ := (by simpa using member :
      ∃ l ∈ left.requirements, ∃ r ∈ right.requirements,
        (.intersection l.1 r.1, .union l.2 r.2) = pair)
    exact .unionElim
      (.trans (left.sound l hl) (.callable
        (.interLeft (.refl l.1.namesKnown) r.1.namesKnown)
        (.unionLeft (.refl l.2.namesKnown) r.2.namesKnown)))
      (.trans (right.sound r hr) (.callable
        (.interRight (.refl r.1.namesKnown) l.1.namesKnown)
        (.unionRight (.refl r.2.namesKnown) l.2.namesKnown)))
  complete := by
    intro P R included
    obtain ⟨leftIncluded, rightIncluded⟩ := subtype_union_iff.mp included
    obtain ⟨l, hl, ld, lr⟩ := left.complete P R leftIncluded
    obtain ⟨r, hr, rd, rr⟩ := right.complete P R rightIncluded
    exact ⟨(.intersection l.1 r.1, .union l.2 r.2),
      List.mem_flatMap.mpr ⟨l, hl, List.mem_map.mpr ⟨r, hr, rfl⟩⟩,
      .interIntro ld rd, .unionElim lr rr⟩

/-- Combine summaries for produced intersections whose class conjunctions include BoundMethod. -/
private def intersectionSummaries (structural : WellFormedClassHierarchy ct) :
    (intersections : List (TypeIntersection structural.typeContext)) →
    (∀ intersection ∈ intersections, intersection.classIntersection.includesClass boundMethodClass = true) →
    CallableSummaries structural (.joinTypes (intersections.map TypeIntersection.toType))
  | [], _ =>
      { requirements := [((WellFormedTy.object structural).toType, .bottom)]
        sound := by
          intro pair member
          cases List.mem_singleton.mp member
          exact .bottom (.callable (WellFormedTy.object structural) .bottom)
        complete := fun _ _ included => ⟨_, List.mem_singleton.mpr rfl,
          .objectTop included.targetWellFormed.callable_param, .bottom included.targetWellFormed.callable_return⟩ }
  | intersection :: rest, included =>
      combineCallableSummaries
        (CallableSummaries.ofEquation
          (intersection.functionIntersection_equation (included intersection List.mem_cons_self))
          (functionSummaries structural intersection.functionTypes))
        (intersectionSummaries structural rest
          (fun intersection member => included intersection (List.mem_cons_of_mem _ member)))

/-- Enumerate valid input/result pairs covering every `P -> R` with `source <: P -> R`.
For one normalized intersection with m listed function requirements, enumeration
builds 2^m - 1 nonempty subsets and then 2^(2^m - 1) collections of those subsets.
These counts include repeated entries. A summary can combine several subsets.
When those combined results are function types, retained repetitions and
intersections formed during inference can make the next callee's function list
larger. The next call enumerates all subsets and collections of that larger
callee list before checking arguments. This enumeration can exhaust evaluation
time or memory on repeated calls. -/
def callableSummaries (structural : WellFormedClassHierarchy ct)
    (source : WellFormedType (ct.map ClassDecl.name)) : CallableSummaries structural source := by
  let context := structural.typeContext
  match WellFormedType.subtypeDecidable structural source (WellFormedTy.boundMethod structural).toType with
  | .isFalse rejected =>
      exact { requirements := [], sound := by intro pair member; cases member
              complete := by
                intro P R included
                exact (rejected (.trans included
                  (.callableBoundMethod included.targetWellFormed.callable_param
                    included.targetWellFormed.callable_return))).elim }
  | .isTrue callable =>
      let normalized := splitIntoIntersections context source
      exact CallableSummaries.ofEquation normalized.equivalentToSource
        (intersectionSummaries structural normalized.intersections
          (classLiteral_includesClass_of_subtype context source boundMethodClass
            context.valid.boundMethodKnown true callable))

/-- Results of listed requirements that accept at least one inferred argument type. -/
def callResultsFromTy (structural : WellFormedClassHierarchy ct)
    (callee : WellFormedType (ct.map ClassDecl.name))
    (arguments : List (WellFormedType (ct.map ClassDecl.name))) : List (WellFormedType (ct.map ClassDecl.name)) :=
  (callableSummaries structural callee).requirements.flatMap fun signature =>
    arguments.flatMap fun argument =>
      letI := WellFormedType.subtypeDecidable structural argument signature.1
      if IsSubtype structural argument.raw signature.1.raw then [signature.2] else []

/-- Every enumerated result has a typed callee requirement and an accepted argument. -/
theorem callResultsFromTy_sound
    (callee : WellFormedType (ct.map ClassDecl.name))
    (hmem : result ∈ callResultsFromTy structural callee arguments)
    (hcallee : HasType structural Γ expression callee.raw)
    (harg : ∀ argument ∈ arguments, HasType structural Γ arg argument.raw) :
    HasType structural Γ (.call expression arg) result.raw := by
  simp only [callResultsFromTy, List.mem_flatMap] at hmem
  obtain ⟨signature, hs, argument, ha, accepted⟩ := hmem
  haveI := WellFormedType.subtypeDecidable structural argument signature.1
  split at accepted
  · rename_i included
    cases List.mem_singleton.mp accepted
    exact .call (.sub hcallee ((callableSummaries structural callee).sound signature hs)) (harg argument ha) included
  · cases accepted

/-- Every declarative call has an enumerated result below its required result. -/
theorem callResultsFromTy_complete
    (callee : WellFormedType (ct.map ClassDecl.name))
    (hcallee : IsSubtype structural callee.raw (.callable P R))
    (hA : argument ∈ arguments) (harg : IsSubtype structural argument.raw P) :
    ∃ result, result ∈ callResultsFromTy structural callee arguments ∧ IsSubtype structural result.raw R := by
  obtain ⟨signature, hs, inputSubtype, resultSubtype⟩ := (callableSummaries structural callee).complete P R hcallee
  have accepted : IsSubtype structural argument.raw signature.1.raw := .trans harg inputSubtype
  refine ⟨signature.2, List.mem_flatMap.mpr ⟨signature, hs, List.mem_flatMap.mpr ⟨argument, hA, ?_⟩⟩, resultSubtype⟩
  simp [accepted]

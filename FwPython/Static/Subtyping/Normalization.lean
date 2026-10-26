import FwPython.Static.Subtyping.Algebra
import FwPython.Static.Subtyping.ClassIntersection

set_option autoImplicit false

/-! # Algebraic normalization of valid types

A class literal is a class type or its exclusion. A complete class conjunction
chooses one of those literals for every known name. A normal form is a union of
`TypeIntersection` records, each combining one complete class conjunction with
function requirements. The normalizer computes this form from a valid type;
distribution and the class equations prove that it represents the source.
The normalizer carries that equation and preserves validity in every component.
Bounds on function nesting ensure that recursive subtype queries fit within the
comparison's depth limit.
-/

namespace FwPython.Static.Subtyping

open TypeEquivalence

variable {context : ValidatedClassContext}

/-- The type requiring every included class and excluding every other known class name. -/
def ClassIntersection.toType {context : ValidatedClassContext}
    (conjunction : ClassIntersection context) : WellFormedType context.names :=
  WellFormedType.meetTypes context.valid.objectKnown
    (context.names.attach.map fun entry =>
      .classLiteral entry.val entry.property (conjunction.includesClass entry.val))

/-- Function nesting; lattice combinations take the maximum of their children. -/
def callableHeight : Ty → Nat
  | .class_ _ | .negClass _ | .bottom => 0
  | .union left right | .intersection left right => max (callableHeight left) (callableHeight right)
  | .callable parameter result => max (callableHeight parameter) (callableHeight result) + 1

/-- Every listed function input and result has function nesting at most the height.
The transparent predicate lets proofs use those inequalities directly. -/
abbrev functionTypesWithinHeight {context : ValidatedClassContext}
    (functions : List (WellFormedType context.names × WellFormedType context.names))
    (height : Nat) : Prop :=
  ∀ requirement ∈ functions,
    callableHeight requirement.1.raw ≤ height ∧ callableHeight requirement.2.raw ≤ height

/-- Finite meets of valid types preserve a common function-nesting bound. -/
theorem WellFormedType.meetTypes_height (types : List (WellFormedType context.names))
    {height : Nat} (heights : ∀ type ∈ types, callableHeight type.raw ≤ height) :
    callableHeight (WellFormedType.meetTypes context.valid.objectKnown types).raw ≤ height := by
  induction types with
  | nil => exact Nat.zero_le height
  | cons head tail inductionHypothesis =>
      exact Nat.max_le.mpr ⟨heights head (List.mem_cons_self),
        inductionHypothesis (fun type member => heights type (List.mem_cons_of_mem _ member))⟩

/-- Projected meets of a source subsequence preserve the source projection's function-nesting bound. -/
theorem WellFormedType.projectedMeet_height {α : Type} {source subset : List α} {height : Nat}
    (project : α → WellFormedType context.names) (listed : subset ∈ subsequences source)
    (heights : ∀ entry ∈ source, callableHeight (project entry).raw ≤ height) :
    callableHeight (WellFormedType.meetTypes context.valid.objectKnown (subset.map project)).raw ≤ height :=
  WellFormedType.meetTypes_height _ fun type member => by
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact heights entry ((mem_subsequences.mp listed).subset present)

/-- Finite unions of valid types preserve a common function-nesting bound. -/
theorem WellFormedType.joinTypes_height (types : List (WellFormedType context.names))
    {height : Nat} (heights : ∀ type ∈ types, callableHeight type.raw ≤ height) :
    callableHeight (WellFormedType.joinTypes types).raw ≤ height := by
  induction types with
  | nil => exact Nat.zero_le height
  | cons head tail inductionHypothesis =>
      exact Nat.max_le.mpr ⟨heights head (List.mem_cons_self),
        inductionHypothesis (fun type member => heights type (List.mem_cons_of_mem _ member))⟩

/-- The intersection of the listed function types, with input then result in each pair.
An empty list gives Object, because it imposes no requirement. -/
def WellFormedType.functionMeet (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names)) :
    WellFormedType context.names :=
  .meetTypes context.valid.objectKnown (source.map fun pair => .callable pair.1 pair.2)

/-- BoundMethod intersected with the listed function requirements.
An empty list gives BoundMethod intersected with Object, which is equivalent to BoundMethod. -/
def WellFormedType.functionIntersection (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names)) :
    WellFormedType context.names :=
  .intersection context.boundMethodType (.functionMeet context source)

/-- Each listed valid type is below the join of the valid types. -/
theorem subtype_joinTypes {types : List (WellFormedType context.names)}
    {type : WellFormedType context.names} (member : type ∈ types) :
    Subtype context type.raw (WellFormedType.joinTypes types).raw := by
  induction types with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .unionLeft (.refl type.namesKnown) (WellFormedType.joinTypes tail).namesKnown
      · exact .unionRight (inductionHypothesis member) head.namesKnown

/-- The meet of listed valid types is below each listed type. -/
theorem meetTypes_subtype {types : List (WellFormedType context.names)}
    {type : WellFormedType context.names} (member : type ∈ types) :
    Subtype context
      (WellFormedType.meetTypes context.valid.objectKnown types).raw type.raw := by
  induction types with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .interLeft (.refl type.namesKnown)
          (WellFormedType.meetTypes context.valid.objectKnown tail).namesKnown
      · exact .interRight (inductionHypothesis member) head.namesKnown

/-- The function intersection is below every listed function requirement. -/
theorem WellFormedType.functionIntersection_subtype
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {pair : WellFormedType context.names × WellFormedType context.names} (member : pair ∈ source) :
    Subtype context (WellFormedType.functionIntersection context source).raw
      (WellFormedType.callable pair.1 pair.2).raw :=
  .interRight (meetTypes_subtype (List.mem_map.mpr ⟨pair, member, rfl⟩)) context.boundMethodType.namesKnown

/-- The function intersection requires BoundMethod, including when its function list is empty. -/
theorem WellFormedType.functionIntersection_boundMethod
    (source : List (WellFormedType context.names × WellFormedType context.names)) :
    Subtype context (WellFormedType.functionIntersection context source).raw context.boundMethodType.raw :=
  .interLeft (.refl context.boundMethodType.namesKnown)
    (WellFormedType.functionIntersection context source).namesKnown.intersection_right

/-- A valid type below every listed valid type is below their meet. -/
theorem subtype_meetTypes {source : WellFormedType context.names}
    {types : List (WellFormedType context.names)}
    (included : ∀ entry, entry ∈ types → Subtype context source.raw entry.raw) :
    Subtype context source.raw
      (WellFormedType.meetTypes context.valid.objectKnown types).raw := by
  induction types with
  | nil => exact .objectTop source.namesKnown
  | cons head tail inductionHypothesis =>
      exact .interIntro (included head (by simp))
        (inductionHypothesis (fun entry member => included entry (List.mem_cons_of_mem _ member)))

/-- The join is below any valid type that every listed type is below. -/
theorem joinTypes_subtype {types : List (WellFormedType context.names)}
    {target : WellFormedType context.names}
    (included : ∀ entry, entry ∈ types → Subtype context entry.raw target.raw) :
    Subtype context (WellFormedType.joinTypes types).raw target.raw := by
  induction types with
  | nil => exact .bottom target.namesKnown
  | cons head tail inductionHypothesis =>
      exact .unionElim (included head (by simp))
        (inductionHypothesis (fun entry member => included entry (List.mem_cons_of_mem _ member)))

/-- Intersecting two lists' meets equals the meet of the concatenated lists. -/
private theorem meetTypes_append
    (left right : List (WellFormedType context.names)) :
    TypeEquivalence context
      (.intersection (.meetTypes context.valid.objectKnown left) (.meetTypes context.valid.objectKnown right))
      (.meetTypes context.valid.objectKnown (left ++ right)) := by
  induction left with
  | nil => exact .trans .intersectionCommutative .intersectionObject
  | cons head tail inductionHypothesis =>
      exact .trans intersectionAssociative (.intersection .refl inductionHypothesis)

/-- Joining two lists' unions equals the union of the concatenated lists. -/
private theorem joinTypes_append (left right : List (WellFormedType context.names)) :
    TypeEquivalence context (.union (.joinTypes left) (.joinTypes right)) (.joinTypes (left ++ right)) := by
  induction left with
  | nil => exact .trans .unionCommutative .unionBottom
  | cons head tail inductionHypothesis => exact .trans unionAssociative (.union .refl inductionHypothesis)

/-- A complete class conjunction is below each of its class types and exclusions. -/
private theorem ClassIntersection.subtype_classLiteral (conjunction : ClassIntersection context)
    (name : Identifier) (known : name ∈ context.names) :
    Subtype context conjunction.toType.raw
      (WellFormedType.classLiteral name known (conjunction.includesClass name)).raw :=
  meetTypes_subtype (List.mem_map.mpr ⟨⟨name, known⟩, List.mem_attach _ _, rfl⟩)

/-- A valid type below every class literal that a complete class conjunction chooses is below the conjunction. -/
theorem ClassIntersection.subtype_toType (conjunction : ClassIntersection context)
    {source : WellFormedType context.names}
    (chosen : ∀ name (known : name ∈ context.names),
      Subtype context source.raw (WellFormedType.classLiteral name known (conjunction.includesClass name)).raw) :
    Subtype context source.raw conjunction.toType.raw :=
  subtype_meetTypes fun _ member => by
    obtain ⟨⟨name, known⟩, _, rfl⟩ := List.mem_map.mp member
    exact chosen name known

/-- One complete class conjunction intersected with its function requirements. -/
structure TypeIntersection (context : ValidatedClassContext) where
  /-- Class types and exclusions required together with the function types. -/
  classIntersection : ClassIntersection context
  /-- Intersected function types; each pair stores the input package first and the result package second. -/
  functionTypes : List (WellFormedType context.names × WellFormedType context.names)
  /-- Every nonempty function list requires the included class BoundMethod. -/
  functionsRequireBoundMethod : functionTypes ≠ [] →
    classIntersection.includesClass boundMethodClass = true

/-- BoundMethod's complete class conjunction with the supplied function requirements.
An empty requirement list still describes BoundMethod. The transparent constructor
exposes its class conjunction and ordered function list to clients. -/
abbrev TypeIntersection.ofFunctions (context : ValidatedClassContext)
    (functions : List (WellFormedType context.names × WellFormedType context.names)) : TypeIntersection context :=
  ⟨ClassIntersection.ofClassMro context boundMethodClass context.valid.boundMethodKnown,
    functions, fun _ => ClassIntersection.boundMethod_includesSelf context⟩

/-- A complete class conjunction with no function types. -/
private def TypeIntersection.ofClasses (conjunction : ClassIntersection context) : TypeIntersection context :=
  ⟨conjunction, [], fun nonempty => (nonempty rfl).elim⟩

/-- The intersection of two intersections with the same included class names: the left class
conjunction with both ordered function lists. -/
private def TypeIntersection.append (left right : TypeIntersection context)
    (same : ClassIntersection.sameClasses left.classIntersection right.classIntersection) :
    TypeIntersection context :=
  ⟨left.classIntersection, left.functionTypes ++ right.functionTypes, fun nonempty =>
    if leftEmpty : left.functionTypes = [] then
      (same boundMethodClass context.valid.boundMethodKnown).trans
        (right.functionsRequireBoundMethod fun rightEmpty => nonempty (by rw [leftEmpty, rightEmpty]; rfl))
    else left.functionsRequireBoundMethod leftEmpty⟩

/-- The type expression represented by this type intersection. -/
def TypeIntersection.toType (intersection : TypeIntersection context) : WellFormedType context.names :=
  .intersection intersection.classIntersection.toType (.functionMeet context intersection.functionTypes)

/-- A type intersection is below each class literal in its complete class conjunction. -/
theorem TypeIntersection.subtype_classLiteral (intersection : TypeIntersection context)
    (name : Identifier) (known : name ∈ context.names) :
    Subtype context intersection.toType.raw
      (WellFormedType.classLiteral name known (intersection.classIntersection.includesClass name)).raw :=
  .interLeft (intersection.classIntersection.subtype_classLiteral name known)
    intersection.toType.namesKnown.intersection_right

/-- A valid type below a type intersection's class conjunction and each of its function
requirements is below the type intersection. -/
theorem TypeIntersection.subtype_toType (target : TypeIntersection context) {source : WellFormedType context.names}
    (classBound : Subtype context source.raw target.classIntersection.toType.raw)
    (functions : ∀ requirement, requirement ∈ target.functionTypes →
      Subtype context source.raw (WellFormedType.callable requirement.1 requirement.2).raw) :
    Subtype context source.raw target.toType.raw :=
  .interIntro classBound (subtype_meetTypes fun _ member => by
    obtain ⟨requirement, required, rfl⟩ := List.mem_map.mp member
    exact functions requirement required)

/-- An intersection including BoundMethod equals BoundMethod with its function requirements. -/
theorem TypeIntersection.functionIntersection_equation (intersection : TypeIntersection context)
    (methodPositive : intersection.classIntersection.includesClass boundMethodClass = true) :
    TypeEquivalence context intersection.toType
      (WellFormedType.functionIntersection context intersection.functionTypes) := by
  refine .intersection (ofSubtypes ?_
    (intersection.classIntersection.subtype_toType fun name known => ?_)) .refl
  · simpa only [methodPositive] using
      intersection.classIntersection.subtype_classLiteral boundMethodClass context.valid.boundMethodKnown
  · have classEqual := intersection.classIntersection.boundMethod_includesClass methodPositive name
    have ancestor := ClassIntersection.ofClassMro_includesClass context
      boundMethodClass context.valid.boundMethodKnown name
    cases answer : intersection.classIntersection.includesClass name with
    | true => exact .inheritance context.valid.boundMethodKnown (ancestor.mp (classEqual.symm.trans answer))
    | false =>
        exact .sealedClassNegClass (by simp [sealedClasses]) known (fun present =>
          Bool.noConfusion (answer.symm.trans (classEqual.trans (ancestor.mpr present))))

/-- A union of type intersections, with its source equation and function-nesting inequalities. -/
structure UnionOfIntersections (context : ValidatedClassContext)
    (source : WellFormedType context.names) where
  /-- Intersections whose union represents the source type. -/
  intersections : List (TypeIntersection context)
  /-- The source equals the union of the listed intersection expressions. -/
  equivalentToSource : TypeEquivalence context source
    (WellFormedType.joinTypes (intersections.map TypeIntersection.toType))
  /-- Each retained function is at most as deeply nested as the source type. -/
  functionHeights : ∀ intersection, intersection ∈ intersections →
    ∀ requirement, requirement ∈ intersection.functionTypes →
      max (callableHeight requirement.1.raw) (callableHeight requirement.2.raw) + 1 ≤
        callableHeight source.raw

/-- Every function retained from a source of nesting at most `height + 1` has
input and result nesting at most `height`. -/
theorem UnionOfIntersections.retainedWithinHeight {source : WellFormedType context.names}
    (normalized : UnionOfIntersections context source) {height : Nat}
    (sourceHeight : callableHeight source.raw ≤ height + 1)
    {intersection : TypeIntersection context} (member : intersection ∈ normalized.intersections) :
    functionTypesWithinHeight intersection.functionTypes height := by
  intro requirement present
  -- Construct the pair directly to keep the arithmetic step constructive.
  exact Nat.max_le.mp (Nat.le_of_succ_le_succ
    (Nat.le_trans (normalized.functionHeights intersection member requirement present) sourceHeight))

/-- Combine intersections with matching class inclusions, keeping all function types.
`none` means the class inclusions conflict, so the intersection is empty. -/
private def combineTypeIntersections (context : ValidatedClassContext)
    (left right : TypeIntersection context) : Option (TypeIntersection context) :=
  if same : ClassIntersection.sameClasses left.classIntersection right.classIntersection then
    some (left.append right same)
  else none

/-- The function-free enumerated class conjunctions that include `name` when
`positive` is true and exclude it otherwise. -/
private def classLiteralIntersections (context : ValidatedClassContext) (name : Identifier) (positive : Bool) :
    List (TypeIntersection context) :=
  ((classIntersections context).filter fun conjunction => conjunction.includesClass name == positive).map
    TypeIntersection.ofClasses

/-- Represent a valid type by intersections of complete class conjunctions and function types.
Their union equals the source. Structural recursion on syntax supports kernel evaluation;
the name-validity proof certifies each component. -/
private def splitTypeIntersections (context : ValidatedClassContext) (raw : Ty)
    (known : TypeNamesKnown context.names raw) : List (TypeIntersection context) :=
  match raw with
  | .bottom => []
  | .class_ name => classLiteralIntersections context name true
  | .negClass name => classLiteralIntersections context name false
  | .callable parameter result =>
      let parameters : WellFormedType context.names := ⟨parameter, known.callable_param⟩
      let results : WellFormedType context.names := ⟨result, known.callable_return⟩
      [TypeIntersection.ofFunctions context [(parameters, results)]]
  | .union left right =>
      splitTypeIntersections context left known.union_left ++
        splitTypeIntersections context right known.union_right
  | .intersection left right =>
      let leftTerms := splitTypeIntersections context left known.intersection_left
      let rightTerms := splitTypeIntersections context right known.intersection_right
      leftTerms.flatMap fun first => rightTerms.filterMap (combineTypeIntersections context first)

/-- A successful product keeps the left class conjunction and both ordered function lists. -/
private theorem combineTypeIntersections_some (left right combined : TypeIntersection context)
    (found : combineTypeIntersections context left right = some combined) :
    (ClassIntersection.sameClasses left.classIntersection right.classIntersection) ∧
    combined.classIntersection = left.classIntersection ∧
    combined.functionTypes = left.functionTypes ++ right.functionTypes := by
  unfold combineTypeIntersections at found
  split at found
  next same =>
    cases Option.some.inj found
    exact ⟨same, rfl, rfl⟩
  next _ => cases found

/-- The structural split retains only functions within the source's function nesting. -/
private theorem splitTypeIntersections_height (source : WellFormedType context.names) :
    ∀ intersection, intersection ∈ splitTypeIntersections context source.raw source.namesKnown →
      ∀ requirement, requirement ∈ intersection.functionTypes →
        max (callableHeight requirement.1.raw) (callableHeight requirement.2.raw) + 1 ≤
          callableHeight source.raw := by
  rcases source with ⟨source, known⟩
  induction known with
  | bottom => simp [splitTypeIntersections]
  | class_ _ | negClass _ =>
      intro intersection member requirement required
      simp only [splitTypeIntersections, classLiteralIntersections, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      cases required
  | callable _ _ =>
      intro intersection member requirement required
      simp only [splitTypeIntersections, List.mem_singleton] at member
      subst intersection
      simp only [List.mem_singleton] at required
      subst requirement
      exact Nat.le_refl _
  | union _ _ leftInduction rightInduction =>
      intro intersection member requirement required
      simp only [splitTypeIntersections, List.mem_append] at member
      rcases member with leftMember | rightMember
      · exact Nat.le_trans (leftInduction intersection leftMember requirement required)
          (Nat.le_max_left _ _)
      · exact Nat.le_trans (rightInduction intersection rightMember requirement required)
          (Nat.le_max_right _ _)
  | intersection _ _ leftInduction rightInduction =>
      intro intersection member requirement required
      simp only [splitTypeIntersections, List.mem_flatMap, List.mem_filterMap] at member
      obtain ⟨left, leftMember, right, rightMember, found⟩ := member
      have fields := combineTypeIntersections_some left right intersection found
      rw [fields.2.2] at required
      rcases List.mem_append.mp required with leftRequirement | rightRequirement
      · exact Nat.le_trans (leftInduction left leftMember requirement leftRequirement)
          (Nat.le_max_left _ _)
      · exact Nat.le_trans (rightInduction right rightMember requirement rightRequirement)
          (Nat.le_max_right _ _)

/-- A failed universal condition on a finite list yields a listed failure. -/
private theorem finite_failure {α : Type} {entries : List α} {condition : α → Prop}
    [DecidablePred condition] (failed : ¬ ∀ entry, entry ∈ entries → condition entry) :
    ∃ entry, entry ∈ entries ∧ ¬ condition entry :=
  Decidable.byContradiction fun noFailure => failed fun entry member =>
    Decidable.byContradiction fun wrong => noFailure ⟨entry, member, wrong⟩

/-- Bounds by a class type and by its exclusion derive bottom from the class contradiction equation. -/
private theorem opposite_classLiterals_empty (source : WellFormedType context.names) (name : Identifier)
    (known : name ∈ context.names) {first second : Bool} (different : first ≠ second)
    (firstBound : Subtype context source.raw (WellFormedType.classLiteral name known first).raw)
    (secondBound : Subtype context source.raw (WellFormedType.classLiteral name known second).raw) :
    Subtype context source.raw .bottom := by
  cases first <;> cases second
  · exact (different rfl).elim
  · exact .trans (.interIntro secondBound firstBound) (toSubtype (.classContradiction known))
  · exact .trans (.interIntro firstBound secondBound) (toSubtype (.classContradiction known))
  · exact (different rfl).elim

/-- Repeated complement splitting reduces a subtype claim to its complete class conjunctions. -/
private theorem subtype_of_class_cases (names : List Identifier)
    (knownNames : ∀ name, name ∈ names → name ∈ context.names)
    (source target : WellFormedType context.names)
    (finishCase : ∀ caseType : WellFormedType context.names,
      Subtype context caseType.raw source.raw →
      ∀ includes : Identifier → Bool,
      (∀ name (listed : name ∈ names), Subtype context caseType.raw
        (WellFormedType.classLiteral name (knownNames name listed) (includes name)).raw) →
      Subtype context caseType.raw target.raw) :
    Subtype context source.raw target.raw := by
  induction names generalizing source with
  | nil => exact finishCase source (.refl source.namesKnown) (fun _ => false) (by simp)
  | cons head tail inductionHypothesis =>
      have headKnown := knownNames head (by simp)
      let literal (positive : Bool) : WellFormedType context.names :=
        .classLiteral head headKnown positive
      have each (positive : Bool) :
          Subtype context (WellFormedType.intersection source (literal positive)).raw target.raw := by
        apply inductionHypothesis (fun name listed => knownNames name (List.mem_cons_of_mem _ listed))
        intro caseType caseSubtype includes choices
        apply finishCase caseType
          (.trans caseSubtype (.interLeft (.refl source.namesKnown) (literal positive).namesKnown))
          (fun name => if name = head then positive else includes name)
        intro name listed
        by_cases same : name = head
        · subst name
          simpa only using
            (Subtype.trans caseSubtype
              (Subtype.interRight (Subtype.refl (literal positive).namesKnown) source.namesKnown))
        · simpa only [if_neg same] using choices name ((List.mem_cons.mp listed).resolve_left same)
      exact .trans (toSubtype (.trans intersectionObject.symm
        (.trans (.intersection .refl (classComplement headKnown).symm) .intersectionDistributes)))
        (.unionElim (each true) (each false))

/-- The class equations make a complete class conjunction empty if it violates a conjunction constraint. -/
private theorem class_conjunction_admissible_or_bottom
    (source : WellFormedType context.names) (includes : Identifier → Bool)
    (chosen : ∀ name (known : name ∈ context.names), Subtype context source.raw
      (WellFormedType.classLiteral name known (includes name)).raw) :
    Admissible context (context.names.eraseDups.filter includes) ∨
      Subtype context source.raw .bottom := by
  let members := context.names.eraseDups.filter includes
  have listed (name : Identifier) :
      name ∈ members ↔ name ∈ context.names ∧ includes name = true := by
    simp only [members, List.mem_filter, List.mem_eraseDups]
  have presentBound (name : Identifier) (present : name ∈ members) :
      Subtype context source.raw (.class_ name) := by
    have facts := (listed name).mp present
    simpa only [facts.2] using chosen name facts.1
  have absentBound (name : Identifier) (known : name ∈ context.names) (absent : name ∉ members) :
      Subtype context source.raw (.negClass name) := by
    have answer : includes name = false :=
      Bool.eq_false_iff.mpr (fun present => absent ((listed name).mpr ⟨known, present⟩))
    simpa only [answer] using chosen name known
  by_cases objectMember : objectClass ∈ members
  case neg =>
    exact .inr (.trans (absentBound objectClass context.valid.objectKnown objectMember)
      (toSubtype negativeObject))
  by_cases inherited : ∀ name, name ∈ context.names → name ∈ members →
      ∀ ancestor, ancestor ∈ context.ancestors name → ancestor ∈ members
  case neg =>
    obtain ⟨name, known, failure⟩ := finite_failure inherited
    obtain ⟨present, failure⟩ := Decidable.not_imp_iff_and_not.mp failure
    obtain ⟨ancestor, ancestorMember, absent⟩ := finite_failure failure
    have ancestorKnown := context.valid.ancestorsKnown name known ancestor ancestorMember
    exact .inr (.trans
      (.interIntro (.trans (presentBound name present) (.inheritance known ancestorMember))
        (absentBound ancestor ancestorKnown absent))
      (toSubtype (.classContradiction ancestorKnown)))
  by_cases sealed : ∀ builtin, builtin ∈ sealedClasses → builtin ∈ members →
      ∀ name, name ∈ context.names → (name ∈ members ↔ name ∈ context.ancestors builtin)
  case neg =>
    obtain ⟨builtin, builtinSealed, failure⟩ := finite_failure sealed
    obtain ⟨present, failure⟩ := Decidable.not_imp_iff_and_not.mp failure
    obtain ⟨name, known, wrong⟩ := finite_failure failure
    have here : name ∈ members := Decidable.byContradiction fun absent =>
      wrong ⟨fun included => (absent included).elim,
        inherited builtin (context.valid.sealedKnown builtin builtinSealed) present name⟩
    have outside : name ∉ context.ancestors builtin :=
      fun ancestor => wrong ⟨fun _ => ancestor, fun _ => here⟩
    exact .inr (.trans (.interIntro (presentBound builtin present) (presentBound name here))
      (toSubtype (sealedExclusion builtinSealed known outside)))
  by_cases order : hasValidClassOrder context members = true
  case neg =>
    exact .inr (.trans
      (subtype_meetTypes (by
        intro type member
        obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
        exact presentBound name.val name.property))
      (toSubtype (incompatibleClasses (fun name present => ((listed name).mp present).1)
        (Bool.eq_false_iff.mpr order))))
  exact .inl ⟨objectMember, inherited, sealed, order⟩

/-- A known class type or exclusion equals the union of the function-free intersections whose
complete class conjunctions include or exclude that name as requested. -/
private theorem classLiteral_equation {name : Identifier} (known : name ∈ context.names)
    (positive : Bool) :
    TypeEquivalence context
      (WellFormedType.classLiteral name known positive)
      (WellFormedType.joinTypes ((classLiteralIntersections context name positive).map
          TypeIntersection.toType)) := by
  let intersections := classLiteralIntersections context name positive
  let target := WellFormedType.joinTypes (intersections.map TypeIntersection.toType)
  apply ofSubtypes
  · apply subtype_of_class_cases context.names (fun _ known => known)
    intro caseType sourceBound includes chosen
    rcases class_conjunction_admissible_or_bottom caseType includes chosen with permitted | empty
    · obtain ⟨intersection, intersectionMember, answers⟩ :=
        classIntersections_complete context includes permitted
      by_cases matching : includes name = positive
      · have caseSubtype : Subtype context caseType.raw (TypeIntersection.ofClasses intersection).toType.raw := by
          refine .interIntro (intersection.subtype_toType fun query queryKnown => ?_) (.objectTop caseType.namesKnown)
          simpa only [answers query queryKnown] using chosen query queryKnown
        have listedType :
            (TypeIntersection.ofClasses intersection).toType ∈ intersections.map TypeIntersection.toType := by
          refine List.mem_map.mpr ⟨_, List.mem_map.mpr
            ⟨intersection, List.mem_filter.mpr ⟨intersectionMember, ?_⟩, rfl⟩, rfl⟩
          rw [answers name known, matching]
          exact beq_self_eq_true positive
        exact .trans caseSubtype (subtype_joinTypes listedType)
      · exact .trans (opposite_classLiterals_empty caseType name known matching (chosen name known) sourceBound)
          (.bottom target.namesKnown)
    · exact .trans empty (.bottom target.namesKnown)
  · apply joinTypes_subtype
    intro type member
    obtain ⟨_, intersectionMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨intersection, filtered, rfl⟩ := List.mem_map.mp intersectionMember
    have matching := beq_iff_eq.mp (List.mem_filter.mp filtered).2
    simpa only [TypeIntersection.ofClasses, matching] using
      (TypeIntersection.ofClasses intersection).subtype_classLiteral name known

/-- Intersections with the same included class names combine the left conjunction with both
function lists; intersections with different included class names have an empty intersection. -/
private theorem combineTypeIntersections_equation (left right : TypeIntersection context) :
    TypeEquivalence context (.intersection left.toType right.toType)
      (match combineTypeIntersections context left right with
       | some combined => combined.toType
       | none => .bottom) := by
  by_cases same : ClassIntersection.sameClasses left.classIntersection right.classIntersection
  · simp only [combineTypeIntersections, dif_pos same]
    have classTypes : left.classIntersection.toType = right.classIntersection.toType := by
      apply congrArg (WellFormedType.meetTypes context.valid.objectKnown)
      apply List.map_congr_left
      intro entry _
      rw [same entry.val entry.property]
    simp only [TypeIntersection.toType, TypeIntersection.append, WellFormedType.functionMeet, List.map_append]
    rw [← classTypes]
    apply TypeEquivalence.trans
      (.trans .intersectionAssociative
        (.trans (.intersection .refl intersectionAssociative.symm)
          (.trans (.intersection .refl (.intersection .intersectionCommutative .refl))
            (.trans (.intersection .refl .intersectionAssociative) intersectionAssociative.symm))))
    exact .trans (.intersection intersectionIdempotent .refl)
      (.intersection .refl (meetTypes_append _ _))
  · simp only [combineTypeIntersections, dif_neg same]
    obtain ⟨name, known, wrong⟩ := finite_failure same
    let product := WellFormedType.intersection left.toType right.toType
    exact ofSubtypes (opposite_classLiterals_empty product name known wrong
      (.interLeft (left.subtype_classLiteral name known) right.toType.namesKnown)
      (.interRight (right.subtype_classLiteral name known) left.toType.namesKnown))
      (.bottom product.namesKnown)

/-- Intersecting one `TypeIntersection` with a finite union equals the union of its intersections
with each union entry. Pairs with different included class names are empty and are omitted. -/
private theorem intersection_distribution_equation (left : TypeIntersection context)
    (right : List (TypeIntersection context)) :
    TypeEquivalence context
      (.intersection left.toType (WellFormedType.joinTypes (right.map TypeIntersection.toType)))
      (WellFormedType.joinTypes
        ((right.filterMap (combineTypeIntersections context left)).map TypeIntersection.toType)) := by
  induction right with
  | nil => exact meetBottom
  | cons head tail inductionHypothesis =>
      have pair := combineTypeIntersections_equation left head
      cases found : combineTypeIntersections context left head <;>
        simp only [found] at pair <;>
        simp only [List.filterMap_cons, found]
      · exact .trans .intersectionDistributes
          (.trans (.union pair inductionHypothesis) (.trans .unionCommutative .unionBottom))
      · exact .trans .intersectionDistributes (.union pair inductionHypothesis)

/-- The finite filtered product represents the intersection of its operand unions. -/
private theorem intersection_product_equation (left right : List (TypeIntersection context)) :
    TypeEquivalence context
      (.intersection (WellFormedType.joinTypes (left.map TypeIntersection.toType))
        (WellFormedType.joinTypes (right.map TypeIntersection.toType)))
      (WellFormedType.joinTypes
        ((left.flatMap fun first => right.filterMap (combineTypeIntersections context first)).map
          TypeIntersection.toType)) := by
  induction left with
  | nil => exact .trans .intersectionCommutative meetBottom
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append]
      exact .trans
        (.trans .intersectionCommutative
          (.trans .intersectionDistributes (.union .intersectionCommutative .intersectionCommutative)))
        (.trans (.union (intersection_distribution_equation head right) inductionHypothesis)
          (joinTypes_append _ _))

/-- A valid type equals the union of the type intersections computed by its structural split. -/
private theorem splitTypeIntersections_equation (source : WellFormedType context.names) :
    TypeEquivalence context source
      (WellFormedType.joinTypes
        ((splitTypeIntersections context source.raw source.namesKnown).map TypeIntersection.toType)) := by
  rcases source with ⟨source, known⟩
  induction known with
  | bottom => exact .refl
  | class_ known => exact classLiteral_equation known true
  | negClass known => exact classLiteral_equation known false
  | callable inputKnown resultKnown =>
      let input : WellFormedType context.names := ⟨_, inputKnown⟩
      let result : WellFormedType context.names := ⟨_, resultKnown⟩
      exact (trans unionBottom
        (.trans ((TypeIntersection.ofFunctions context [(input, result)]).functionIntersection_equation
            (ClassIntersection.boundMethod_includesSelf context))
          (.trans (.intersection .refl intersectionObject)
            (.trans .intersectionCommutative
              ((subtype_iff_intersection (.callable input result) context.boundMethodType).mp
                (.callableBoundMethod input.namesKnown result.namesKnown)))))).symm
  | union _ _ leftInduction rightInduction =>
      simp only [splitTypeIntersections, List.map_append]
      exact .trans (.union leftInduction rightInduction) (joinTypes_append _ _)
  | intersection _ _ leftInduction rightInduction =>
      exact .trans (.intersection leftInduction rightInduction) (intersection_product_equation _ _)

/-- Convert a valid source into its equation-certified union of type intersections. -/
def splitIntoIntersections (context : ValidatedClassContext)
    (source : WellFormedType context.names) : UnionOfIntersections context source :=
  ⟨splitTypeIntersections context source.raw source.namesKnown, splitTypeIntersections_equation source,
    splitTypeIntersections_height source⟩

/-- Bottom produces no intersections. -/
theorem splitIntoIntersections_bottom :
    (splitIntoIntersections context WellFormedType.bottom).intersections = [] := rfl

/-- A class literal produces the function-free enumerated conjunctions that include
or exclude its named class as requested. -/
theorem mem_splitIntoIntersections_classLiteral (name : Identifier) (known : name ∈ context.names)
    (positive : Bool) (intersection : TypeIntersection context) :
    intersection ∈ (splitIntoIntersections context
      (WellFormedType.classLiteral name known positive)).intersections ↔
      intersection.classIntersection ∈ classIntersections context ∧
        intersection.classIntersection.includesClass name = positive ∧ intersection.functionTypes = [] := by
  have produced : (splitIntoIntersections context
      (WellFormedType.classLiteral name known positive)).intersections =
      classLiteralIntersections context name positive := by
    cases positive <;> rfl
  rw [produced]
  constructor
  · intro member
    obtain ⟨_, filtered, rfl⟩ := List.mem_map.mp member
    exact ⟨(List.mem_filter.mp filtered).1, beq_iff_eq.mp (List.mem_filter.mp filtered).2, rfl⟩
  · intro ⟨member, answer, empty⟩
    cases intersection
    cases empty
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨member, beq_iff_eq.mpr answer⟩, rfl⟩

/-- A complete class conjunction that includes or excludes the named class as requested
has a function-free intersection with the same included class names in the literal's normal form. -/
theorem splitIntoIntersections_classLiteral_matches (conjunction : ClassIntersection context)
    (name : Identifier) (known : name ∈ context.names) (positive : Bool)
    (answer : conjunction.includesClass name = positive) :
    ∃ intersection, intersection ∈ (splitIntoIntersections context
      (WellFormedType.classLiteral name known positive)).intersections ∧
      ClassIntersection.sameClasses conjunction intersection.classIntersection ∧
      intersection.functionTypes = [] := by
  have constraints : Admissible context (context.names.eraseDups.filter conjunction.includesClass) :=
    conjunction.constraints.of_membership (fun query => by
      simp only [List.mem_filter, List.mem_eraseDups, ClassIntersection.includesClass_iff_mem]
      exact ⟨fun present => ⟨conjunction.namesKnown present, present⟩, And.right⟩)
  obtain ⟨enumerated, member, answers⟩ := classIntersections_complete context conjunction.includesClass constraints
  refine ⟨.ofClasses enumerated, (mem_splitIntoIntersections_classLiteral name known positive _).mpr
    ⟨member, (answers name known).trans answer, rfl⟩,
    fun query listed => (answers query listed).symm, rfl⟩

/-- Object's normal form contains a function-free intersection with the same
included class names as the supplied `ClassIntersection`. -/
theorem splitIntoIntersections_object_matches (conjunction : ClassIntersection context) :
    ∃ intersection, intersection ∈ (splitIntoIntersections context context.objectType).intersections ∧
      ClassIntersection.sameClasses conjunction intersection.classIntersection ∧
      intersection.functionTypes = [] :=
  splitIntoIntersections_classLiteral_matches conjunction objectClass context.valid.objectKnown true
    ((conjunction.includesClass_iff_mem objectClass).mpr conjunction.constraints.objectMember)

/-- A function type produces one intersection with BoundMethod's MRO conjunction and its singleton requirement. -/
theorem splitIntoIntersections_callable (parameter result : WellFormedType context.names) :
    (splitIntoIntersections context (WellFormedType.callable parameter result)).intersections =
      [TypeIntersection.ofFunctions context [(parameter, result)]] := rfl

/-- A union appends its operand intersections without changing their class conjunctions or function lists. -/
theorem splitIntoIntersections_union (left right : WellFormedType context.names) :
    (splitIntoIntersections context (WellFormedType.union left right)).intersections =
      (splitIntoIntersections context left).intersections ++
        (splitIntoIntersections context right).intersections := rfl

/-- Intersection members combine one intersection from each operand with the same included class names. -/
theorem splitIntoIntersections_intersection_iff (left right : WellFormedType context.names)
    (intersection : TypeIntersection context) :
    intersection ∈ (splitIntoIntersections context (WellFormedType.intersection left right)).intersections ↔
      ∃ first, first ∈ (splitIntoIntersections context left).intersections ∧
      ∃ second, second ∈ (splitIntoIntersections context right).intersections ∧
        ClassIntersection.sameClasses first.classIntersection second.classIntersection ∧
        intersection.classIntersection = first.classIntersection ∧
        intersection.functionTypes = first.functionTypes ++ second.functionTypes := by
  simp only [splitIntoIntersections, splitTypeIntersections, WellFormedType.intersection,
    List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨first, firstMember, second, secondMember, found⟩
    exact ⟨first, firstMember, second, secondMember,
      combineTypeIntersections_some first second intersection found⟩
  · rintro ⟨first, firstMember, second, secondMember, same, classEqual, functionsEqual⟩
    cases intersection
    cases classEqual
    cases functionsEqual
    exact ⟨first, firstMember, second, secondMember, dif_pos same⟩

/-- Operand intersections with the same included class names produce an intersection of the
operands with the first class conjunction and both ordered function lists. -/
theorem splitIntoIntersections_intersection_of_members {left right : WellFormedType context.names}
    {first second : TypeIntersection context}
    (firstMember : first ∈ (splitIntoIntersections context left).intersections)
    (secondMember : second ∈ (splitIntoIntersections context right).intersections)
    (same : ClassIntersection.sameClasses first.classIntersection second.classIntersection) :
    ∃ combined, combined ∈ (splitIntoIntersections context (WellFormedType.intersection left right)).intersections ∧
      combined.classIntersection = first.classIntersection ∧
      combined.functionTypes = first.functionTypes ++ second.functionTypes :=
  ⟨first.append second same, (splitIntoIntersections_intersection_iff left right _).mpr
    ⟨first, firstMember, second, secondMember, same, rfl, rfl⟩, rfl, rfl⟩

/-- The meet of the literals that a complete class conjunction chooses for the listed names
has an entry in its normal form with the same included class names. Every entry
has no function types and includes or excludes each listed name as the conjunction specifies. -/
private theorem represented_class_meet (conjunction : ClassIntersection context)
    (entries : List {name : Identifier // name ∈ context.names}) :
    (∃ intersection, intersection ∈ (splitIntoIntersections context
      (WellFormedType.meetTypes context.valid.objectKnown
        (entries.map fun entry =>
          .classLiteral entry.val entry.property (conjunction.includesClass entry.val)))).intersections ∧
      ClassIntersection.sameClasses conjunction intersection.classIntersection) ∧
    (∀ intersection, intersection ∈ (splitIntoIntersections context
      (WellFormedType.meetTypes context.valid.objectKnown
        (entries.map fun entry =>
          .classLiteral entry.val entry.property (conjunction.includesClass entry.val)))).intersections →
      intersection.functionTypes = [] ∧ ∀ entry, entry ∈ entries →
        intersection.classIntersection.includesClass entry.val = conjunction.includesClass entry.val) := by
  induction entries with
  | nil =>
      obtain ⟨intersection, member, answers, _⟩ := splitIntoIntersections_object_matches conjunction
      exact ⟨⟨intersection, member, answers⟩, fun intersection member => ⟨
        ((mem_splitIntoIntersections_classLiteral objectClass context.valid.objectKnown true intersection).mp
          member).2.2,
        by simp⟩⟩
  | cons entry rest inductionHypothesis =>
      obtain ⟨⟨_, tailMember, tailAnswers⟩, tailAll⟩ := inductionHypothesis
      obtain ⟨_, headMember, headAnswers, _⟩ :=
        splitIntoIntersections_classLiteral_matches conjunction entry.val entry.property _ rfl
      have same name known := (headAnswers name known).symm.trans (tailAnswers name known)
      constructor
      · obtain ⟨combined, member, classesEqual, _⟩ :=
          splitIntoIntersections_intersection_of_members headMember tailMember same
        exact ⟨combined, member, classesEqual ▸ headAnswers⟩
      · intro intersection member
        obtain ⟨first, firstMember, second, secondMember, sameClasses, classesEqual, functionsEqual⟩ :=
          (splitIntoIntersections_intersection_iff _ _ intersection).mp member
        obtain ⟨_, answer, firstEmpty⟩ :=
          (mem_splitIntoIntersections_classLiteral entry.val entry.property _ first).mp firstMember
        have tailFacts := tailAll second secondMember
        refine ⟨by rw [functionsEqual, firstEmpty, tailFacts.1]; rfl, ?_⟩
        intro query listed
        rw [classesEqual]
        rcases List.mem_cons.mp listed with rfl | inTail
        · exact answer
        · exact (sameClasses query.val query.property).trans (tailFacts.2 query inTail)

/-- For the supplied complete class conjunction, a meet of function requirements
has an entry in its normal form with the same included class names, provided the
conjunction includes BoundMethod whenever the function list is nonempty.
Every entry retains the ordered function list. -/
private theorem represented_functions (conjunction : ClassIntersection context)
    (functions : List (WellFormedType context.names × WellFormedType context.names))
    (requiresMethod : functions ≠ [] → conjunction.includesClass boundMethodClass = true) :
    (∃ intersection, intersection ∈ (splitIntoIntersections context
      (WellFormedType.functionMeet context functions)).intersections ∧
      ClassIntersection.sameClasses conjunction intersection.classIntersection) ∧
    (∀ intersection, intersection ∈ (splitIntoIntersections context
      (WellFormedType.functionMeet context functions)).intersections →
      intersection.functionTypes = functions) := by
  induction functions with
  | nil =>
      obtain ⟨intersection, member, answers, _⟩ := splitIntoIntersections_object_matches conjunction
      exact ⟨⟨intersection, member, answers⟩, fun intersection member =>
        ((mem_splitIntoIntersections_classLiteral objectClass context.valid.objectKnown true intersection).mp
          member).2.2⟩
  | cons requirement rest inductionHypothesis =>
      obtain ⟨⟨_, tailMember, tailAnswers⟩, tailAll⟩ :=
        inductionHypothesis (fun _ => requiresMethod (by simp))
      let headIntersection := TypeIntersection.ofFunctions context [requirement]
      have headMember : headIntersection ∈
          (splitIntoIntersections context (WellFormedType.callable requirement.1 requirement.2)).intersections :=
        List.mem_singleton_self _
      have headAnswers (name : Identifier) (_known : name ∈ context.names) :
          conjunction.includesClass name = headIntersection.classIntersection.includesClass name :=
        conjunction.boundMethod_includesClass (requiresMethod (by simp)) name
      have same name known := (headAnswers name known).symm.trans (tailAnswers name known)
      constructor
      · obtain ⟨combined, member, classesEqual, _⟩ :=
          splitIntoIntersections_intersection_of_members headMember tailMember same
        exact ⟨combined, member, classesEqual ▸ headAnswers⟩
      · intro intersection member
        obtain ⟨_, firstMember, second, secondMember, _, _, functionsEqual⟩ :=
          (splitIntoIntersections_intersection_iff _ _ intersection).mp member
        rw [splitIntoIntersections_callable] at firstMember
        rw [functionsEqual, List.mem_singleton.mp firstMember, tailAll second secondMember]
        rfl

/-- The normal form of a type built from a single `TypeIntersection` record contains at least one entry.
Every entry has the record's included class names and ordered function requirements. -/
theorem splitIntoIntersections_of_intersection (context : ValidatedClassContext) (source : TypeIntersection context) :
    (∃ intersection, intersection ∈ (splitIntoIntersections context source.toType).intersections) ∧
    ∀ intersection, intersection ∈ (splitIntoIntersections context source.toType).intersections →
      ClassIntersection.sameClasses intersection.classIntersection source.classIntersection ∧
      intersection.functionTypes = source.functionTypes := by
  obtain ⟨⟨_, classMember, classAnswers⟩, classAll⟩ :=
    represented_class_meet source.classIntersection context.names.attach
  obtain ⟨⟨_, functionMember, functionAnswers⟩, functionAll⟩ :=
    represented_functions source.classIntersection source.functionTypes source.functionsRequireBoundMethod
  have same name known := (classAnswers name known).symm.trans (functionAnswers name known)
  refine ⟨(splitIntoIntersections_intersection_of_members classMember functionMember same).imp
    fun _ facts => facts.1, ?_⟩
  intro intersection member
  obtain ⟨first, firstMember, second, secondMember, _, classesEqual, functionsEqual⟩ :=
    (splitIntoIntersections_intersection_iff _ _ intersection).mp member
  have firstFacts := classAll first firstMember
  refine ⟨fun name known => ?_, ?_⟩
  · rw [classesEqual]
    exact firstFacts.2 ⟨name, known⟩ (List.mem_attach _ _)
  · rw [functionsEqual, firstFacts.1, functionAll second secondMember, List.nil_append]

end FwPython.Static.Subtyping

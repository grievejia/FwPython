import FwPython.Static.Subtyping.Normalization
set_option autoImplicit false

/-! # Subtype comparison and its algebraic laws

The Boolean comparison matches complete class conjunctions and checks function
requirements through the inputs covered by nonempty source subsets. It recurses
on a depth limit; smaller function nesting ensures that a sufficient limit never
runs out. Increasing an already sufficient limit leaves the answer unchanged.

Induction on function nesting proves reflexivity, transitivity, and the lattice
laws. Function laws and preservation under component rewrites then follow from
these results. Induction on `TypeEquivalence` then shows that every algebraic
subtype derivation is accepted.
`Equations` supplies the converse: every accepted pair has a subtype derivation.
-/

namespace FwPython.Static.Subtyping

/-- Nonempty source subsets whose result meet is accepted by the supplied comparison. -/
private def subsetsWithResultBelowUsing (context : ValidatedClassContext)
    (check : WellFormedType context.names → WellFormedType context.names → Bool)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) :
    List (List (WellFormedType context.names × WellFormedType context.names)) :=
  (nonemptySubsets source).filter fun subset =>
    check (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)) result

/-- Union the selected subsets' input meets; each selected result meet passes the supplied comparison. -/
private def inputTypeForResultUsing (context : ValidatedClassContext)
    (check : WellFormedType context.names → WellFormedType context.names → Bool)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) : WellFormedType context.names :=
  WellFormedType.joinTypes ((subsetsWithResultBelowUsing context check source result).map fun subset =>
    WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst))

/-- Compare the unions of intersections of two valid types. Each source intersection must
have the same included class names as some target intersection, and `check` must accept each target
function input against the input that the source functions cover for its result. -/
private def normalCheckUsing (context : ValidatedClassContext)
    (check : WellFormedType context.names → WellFormedType context.names → Bool)
    (source target : WellFormedType context.names) : Bool :=
  (splitIntoIntersections context source).intersections.all fun first =>
    (splitIntoIntersections context target).intersections.any fun second =>
      decide (ClassIntersection.sameClasses first.classIntersection second.classIntersection) &&
      second.functionTypes.all fun requirement =>
        check requirement.1 (inputTypeForResultUsing context check first.functionTypes requirement.2)

/-- Complete class conjunctions match, and the source functions cover each target input for its result. -/
private def IntersectionBelow {context : ValidatedClassContext}
    (check : WellFormedType context.names → WellFormedType context.names → Bool)
    (source target : TypeIntersection context) : Prop :=
  ClassIntersection.sameClasses source.classIntersection target.classIntersection ∧
  ∀ requirement, requirement ∈ target.functionTypes →
    check requirement.1 (inputTypeForResultUsing context check source.functionTypes requirement.2) = true

/-- The comparison accepts exactly when every source intersection matches an accepted target intersection. -/
private theorem normalCheckUsing_iff {context : ValidatedClassContext}
    {check : WellFormedType context.names → WellFormedType context.names → Bool}
    {source target : WellFormedType context.names} :
    normalCheckUsing context check source target = true ↔
      ∀ first, first ∈ (splitIntoIntersections context source).intersections →
        ∃ second, second ∈ (splitIntoIntersections context target).intersections ∧
          IntersectionBelow check first second := by
  simp only [normalCheckUsing, IntersectionBelow,
    List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-- Iterate the normalized comparison by the supplied depth limit. Zero accepts every type pair;
a limit exceeding both types' function nesting gives the subtype answer. -/
private def checkSubtypeWithDepth (context : ValidatedClassContext) :
    Nat → WellFormedType context.names → WellFormedType context.names → Bool
  | 0 => fun _ _ => true
  | depth + 1 => normalCheckUsing context (checkSubtypeWithDepth context depth)

/-- Each selected input meet has function nesting at most `height` when all source inputs and results do. -/
private theorem selectedInputs_height {context : ValidatedClassContext}
    {check : WellFormedType context.names → WellFormedType context.names → Bool}
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    (result : WellFormedType context.names) {height : Nat}
    (heights : functionTypesWithinHeight source height) :
    ∀ input ∈ (subsetsWithResultBelowUsing context check source result).map
      (fun subset => WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst)),
      callableHeight input.raw ≤ height := by
  intro input member
  obtain ⟨_, selected, rfl⟩ := List.mem_map.mp member
  exact WellFormedType.projectedMeet_height Prod.fst
    (mem_nonemptySubsets.mp (List.mem_filter.mp selected).1).1
    (fun requirement member => (heights requirement member).1)

/-- Input coverage stays within the common function-nesting height of the source inputs and results. -/
private theorem inputTypeForResultUsing_height {context : ValidatedClassContext}
    {check : WellFormedType context.names → WellFormedType context.names → Bool}
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    (result : WellFormedType context.names) {height : Nat}
    (heights : functionTypesWithinHeight source height) :
    callableHeight (inputTypeForResultUsing context check source result).raw ≤ height :=
  WellFormedType.joinTypes_height _ (selectedInputs_height result heights)

/-- Checks that agree below function nesting `height` give the same comparison on types
with nesting at most `height`, because each recursive check compares types with smaller function nesting. -/
private theorem normalCheckUsing_congr (context : ValidatedClassContext)
    {first second : WellFormedType context.names → WellFormedType context.names → Bool} (height : Nat)
    (same : ∀ left right : WellFormedType context.names,
      callableHeight left.raw < height → callableHeight right.raw < height → first left right = second left right)
    (source target : WellFormedType context.names)
    (sourceHeight : callableHeight source.raw ≤ height) (targetHeight : callableHeight target.raw ≤ height) :
    normalCheckUsing context first source target = normalCheckUsing context second source target := by
  apply Bool.eq_iff_iff.mpr
  rw [normalCheckUsing_iff, normalCheckUsing_iff]
  refine forall_congr' fun left => imp_congr_right fun leftMember =>
    exists_congr fun right => and_congr_right fun rightMember =>
      and_congr_right fun _ => forall_congr' fun requirement =>
        imp_congr_right fun required => Bool.eq_iff_iff.mp ?_
  have requirementHeight :=
    (splitIntoIntersections context target).functionHeights right rightMember requirement required
  have sourceHeights := (splitIntoIntersections context source).retainedWithinHeight
    (height := height - 1) (by omega) leftMember
  have coverage : inputTypeForResultUsing context first left.functionTypes requirement.2 =
      inputTypeForResultUsing context second left.functionTypes requirement.2 := by
    unfold inputTypeForResultUsing subsetsWithResultBelowUsing
    congr 2
    apply List.filter_congr
    intro subset listed
    apply same _ _ _ (by omega)
    have resultHeight :
        callableHeight (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)).raw ≤ height - 1 :=
      WellFormedType.projectedMeet_height Prod.snd (mem_nonemptySubsets.mp listed).1
        (fun pair member => (sourceHeights pair member).2)
    omega
  rw [coverage]
  apply same _ _ (by omega)
  have := inputTypeForResultUsing_height (check := second) requirement.2 sourceHeights
  omega

/-- Depths exceeding both types' function nesting give the same answer. -/
private theorem checkSubtypeWithDepth_depth_independent (context : ValidatedClassContext)
    (firstLimit secondLimit : Nat) (source target : WellFormedType context.names)
    (firstEnough : max (callableHeight source.raw) (callableHeight target.raw) < firstLimit)
    (secondEnough : max (callableHeight source.raw) (callableHeight target.raw) < secondLimit) :
    checkSubtypeWithDepth context firstLimit source target =
      checkSubtypeWithDepth context secondLimit source target := by
  induction firstLimit generalizing secondLimit source target with
  | zero => omega
  | succ first inductionHypothesis =>
      cases secondLimit with
      | zero => omega
      | succ second =>
          exact normalCheckUsing_congr context (max (callableHeight source.raw) (callableHeight target.raw))
            (fun left right _ _ => inductionHypothesis second left right (by omega) (by omega))
            source target (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Return `true` exactly for equation-derived subtype pairs. The depth limit exceeds
both types' function nesting, so every recursive check has a sufficient limit.
`checkSubtypeBool_iff_subtype` proves that this answer agrees with subtyping. -/
def checkSubtypeBool (context : ValidatedClassContext)
    (source target : WellFormedType context.names) : Bool :=
  checkSubtypeWithDepth context (max (callableHeight source.raw) (callableHeight target.raw) + 1) source target

/-- Nonempty source subsets whose result meet is below the requested result type. -/
def subsetsWithResultBelow (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) :
    List (List (WellFormedType context.names × WellFormedType context.names)) :=
  subsetsWithResultBelowUsing context (checkSubtypeBool context) source result

/-- Union of the input meets of nonempty source subsets whose result meets are below the requested result. -/
def inputTypeForResult (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) : WellFormedType context.names :=
  inputTypeForResultUsing context (checkSubtypeBool context) source result

/-- Input coverage stays within the common function-nesting height of the source inputs and results. -/
theorem inputTypeForResult_height (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) (height : Nat)
    (heights : functionTypesWithinHeight source height) :
    callableHeight (inputTypeForResult context source result).raw ≤ height :=
  inputTypeForResultUsing_height result heights

/-- Result selection filters the nonempty source requirement subsets. -/
theorem subsetsWithResultBelow_eq_filter (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) :
    subsetsWithResultBelow context source result =
      (nonemptySubsets source).filter (fun subset => checkSubtypeBool context
        (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)) result) := rfl

/-- Input coverage is the union of the selected subsets' simultaneous inputs. -/
theorem inputTypeForResult_eq_join (context : ValidatedClassContext)
    (source : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names) :
    inputTypeForResult context source result =
      WellFormedType.joinTypes ((subsetsWithResultBelow context source result).map fun subset =>
        WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst)) := rfl

/-- The comparison accepts exactly when every source intersection matches a target
with the same included class names and covers each target input for its result.
Nested function checks use the same public comparison on shallower valid types. -/
theorem checkSubtypeBool_iff_intersections (context : ValidatedClassContext)
    (source target : WellFormedType context.names) :
    checkSubtypeBool context source target = true ↔
      ∀ first, first ∈ (splitIntoIntersections context source).intersections →
        ∃ second, second ∈ (splitIntoIntersections context target).intersections ∧
          (ClassIntersection.sameClasses first.classIntersection second.classIntersection) ∧
          (∀ requirement, requirement ∈ second.functionTypes →
            checkSubtypeBool context requirement.1
              (inputTypeForResult context first.functionTypes requirement.2) = true) := by
  rw [show checkSubtypeBool context source target =
      normalCheckUsing context (checkSubtypeBool context) source target from
    normalCheckUsing_congr context (max (callableHeight source.raw) (callableHeight target.raw))
      (fun left right _ _ => checkSubtypeWithDepth_depth_independent context _ _ left right (by omega) (by omega))
      source target (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
  exact normalCheckUsing_iff

/-- Comparison into a class type or exclusion holds exactly when every source intersection
includes or excludes the named class as requested. -/
theorem checkSubtypeBool_classLiteral_iff (context : ValidatedClassContext)
    (source : WellFormedType context.names) (name : Identifier) (known : name ∈ context.names) (positive : Bool) :
    checkSubtypeBool context source
        (WellFormedType.classLiteral name known positive) = true ↔
      ∀ intersection, intersection ∈ (splitIntoIntersections context source).intersections →
        intersection.classIntersection.includesClass name = positive := by
  rw [checkSubtypeBool_iff_intersections]
  constructor
  · intro included intersection member
    obtain ⟨target, targetMember, same, _⟩ := included intersection member
    exact (same name known).trans
      ((mem_splitIntoIntersections_classLiteral name known positive target).mp targetMember).2.1
  · intro answers intersection member
    obtain ⟨target, targetMember, same, empty⟩ := splitIntoIntersections_classLiteral_matches
      intersection.classIntersection name known positive (answers intersection member)
    exact ⟨target, targetMember, same, fun _ member => nomatch (empty ▸ member)⟩

/-- The comparison accepts a function target when every source intersection has
BoundMethod's MRO names and covers the requested input for the requested result. -/
private theorem checkSubtypeBool_of_callable_coverage {context : ValidatedClassContext}
    {source parameter result : WellFormedType context.names}
    (covered : ∀ intersection, intersection ∈ (splitIntoIntersections context source).intersections →
      ClassIntersection.sameClasses intersection.classIntersection
        (ClassIntersection.ofClassMro context boundMethodClass context.valid.boundMethodKnown) ∧
      checkSubtypeBool context parameter
        (inputTypeForResult context intersection.functionTypes result) = true) :
    checkSubtypeBool context source (.callable parameter result) = true := by
  rw [checkSubtypeBool_iff_intersections, splitIntoIntersections_callable]
  simpa only [List.mem_singleton, exists_eq_left, forall_eq] using covered

section ComparisonProof

variable {context : ValidatedClassContext}

/-- Lattice laws for comparisons on valid types with function nesting at most `height`. -/
private structure LatticeLaws
    (check : WellFormedType context.names → WellFormedType context.names → Bool)
    (height : Nat) : Prop where
  /-- Every valid type with function nesting at most `height` compares below itself. -/
  refl {type : WellFormedType context.names} :
    callableHeight type.raw ≤ height → check type type = true
  /-- Accepted comparisons compose when all three types have function nesting at most `height`. -/
  trans {first middle last : WellFormedType context.names} :
    callableHeight first.raw ≤ height → callableHeight middle.raw ≤ height →
    callableHeight last.raw ≤ height →
    check first middle = true → check middle last = true → check first last = true
  /-- Bottom compares below every valid type with function nesting at most `height`. -/
  bottom {type : WellFormedType context.names} :
    callableHeight type.raw ≤ height → check .bottom type = true
  /-- Every valid type with function nesting at most `height` compares below Object. -/
  objectTop {type : WellFormedType context.names} :
    callableHeight type.raw ≤ height → check type context.objectType = true
  /-- For operands and a target with function nesting at most `height`, adding an intersection
  operand preserves an accepted comparison from the first operand. -/
  interLeft {first second target : WellFormedType context.names} :
    callableHeight first.raw ≤ height → callableHeight second.raw ≤ height →
    callableHeight target.raw ≤ height →
    check first target = true → check (.intersection first second) target = true
  /-- For operands and a target with function nesting at most `height`, adding an intersection
  operand preserves an accepted comparison from the second operand. -/
  interRight {first second target : WellFormedType context.names} :
    callableHeight first.raw ≤ height → callableHeight second.raw ≤ height →
    callableHeight target.raw ≤ height →
    check second target = true → check (.intersection first second) target = true
  /-- For a source and targets with function nesting at most `height`, accepted comparisons
  from the source to both targets give a comparison to their intersection. -/
  interIntro {source first second : WellFormedType context.names} :
    callableHeight source.raw ≤ height → callableHeight first.raw ≤ height →
    callableHeight second.raw ≤ height →
    check source first = true → check source second = true →
    check source (.intersection first second) = true
  /-- For a source and alternatives with function nesting at most `height`, adding a union
  alternative preserves an accepted comparison into the first alternative. -/
  unionLeft {source first second : WellFormedType context.names} :
    callableHeight source.raw ≤ height → callableHeight first.raw ≤ height →
    callableHeight second.raw ≤ height →
    check source first = true → check source (.union first second) = true
  /-- For a source and alternatives with function nesting at most `height`, adding a union
  alternative preserves an accepted comparison into the second alternative. -/
  unionRight {source first second : WellFormedType context.names} :
    callableHeight source.raw ≤ height → callableHeight first.raw ≤ height →
    callableHeight second.raw ≤ height →
    check source second = true → check source (.union first second) = true
  /-- For sources and a target with function nesting at most `height`, comparisons from both
  sources to the target give a comparison from their union. -/
  unionElim {first second target : WellFormedType context.names} :
    callableHeight first.raw ≤ height → callableHeight second.raw ≤ height →
    callableHeight target.raw ≤ height →
    check first target = true → check second target = true → check (.union first second) target = true
  /-- Intersection distributes over union when all operands have function nesting at most `height`. -/
  distributes {first second third : WellFormedType context.names} :
    callableHeight first.raw ≤ height → callableHeight second.raw ≤ height →
    callableHeight third.raw ≤ height →
    check (.intersection first (.union second third))
      (.union (.intersection first second) (.intersection first third)) = true

section

variable {height : Nat}
variable {check : WellFormedType context.names → WellFormedType context.names → Bool}

/-- Selection records the source subsequence, its nonemptiness, and the result comparison. -/
private theorem selected_members
    {source subset : List (WellFormedType context.names × WellFormedType context.names)}
    {result : WellFormedType context.names} :
    subset ∈ subsetsWithResultBelowUsing context check source result ↔
      subset ∈ subsequences source ∧ subset ≠ [] ∧
      check (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)) result = true := by
  simp only [subsetsWithResultBelowUsing, List.mem_filter, mem_nonemptySubsets, and_assoc]

/-- A source subsequence keeps its function inputs and results within the same nesting height. -/
private theorem subset_heights
    {source subset : List (WellFormedType context.names × WellFormedType context.names)}
    (heights : functionTypesWithinHeight source height)
    (listed : subset ∈ subsequences source) :
    functionTypesWithinHeight subset height :=
  fun requirement member => heights requirement ((mem_subsequences.mp listed).subset member)

/-- Every listed input type has function nesting at most `height`. -/
private theorem input_types_height
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    (heights : functionTypesWithinHeight source height) :
    ∀ input ∈ source.map Prod.fst, callableHeight input.raw ≤ height :=
  List.forall_mem_map.mpr (fun requirement member => (heights requirement member).1)

/-- Every listed result type has function nesting at most `height`. -/
private theorem result_types_height
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    (heights : functionTypesWithinHeight source height) :
    ∀ result ∈ source.map Prod.snd, callableHeight result.raw ≤ height :=
  List.forall_mem_map.mpr fun requirement member => (heights requirement member).2

/-- The input meet has function nesting at most `height` when every listed input does. -/
private theorem input_meet_height (source : List (WellFormedType context.names × WellFormedType context.names))
    (heights : functionTypesWithinHeight source height) :
    callableHeight (WellFormedType.meetTypes context.valid.objectKnown (source.map Prod.fst)).raw ≤ height :=
  WellFormedType.meetTypes_height _ (input_types_height heights)

/-- The result meet has function nesting at most `height` when every listed result does. -/
private theorem result_meet_height (source : List (WellFormedType context.names × WellFormedType context.names))
    (heights : functionTypesWithinHeight source height) :
    callableHeight (WellFormedType.meetTypes context.valid.objectKnown (source.map Prod.snd)).raw ≤ height :=
  WellFormedType.meetTypes_height _ (result_types_height heights)

variable (laws : LatticeLaws check height)

include laws

/-- For listed types with function nesting at most `height`, the comparison
accepts their meet below each listed type. -/
private theorem meet_member_within_height {types : List (WellFormedType context.names)}
    {type : WellFormedType context.names}
    (heights : ∀ entry ∈ types, callableHeight entry.raw ≤ height)
    (member : type ∈ types) :
    check (WellFormedType.meetTypes context.valid.objectKnown types) type = true := by
  induction types with
  | nil => cases member
  | cons first rest inductionHypothesis =>
      have firstHeight := heights first List.mem_cons_self
      have restHeights := fun entry member => heights entry (List.mem_cons_of_mem first member)
      have targetHeight := heights type member
      rcases List.mem_cons.mp member with rfl | member
      · exact laws.interLeft firstHeight (WellFormedType.meetTypes_height rest restHeights)
          firstHeight (laws.refl firstHeight)
      · exact laws.interRight firstHeight (WellFormedType.meetTypes_height rest restHeights)
          targetHeight (inductionHypothesis restHeights member)

/-- If the source and listed types have function nesting at most `height`,
accepted comparisons from the source to each listed type extend to their meet. -/
private theorem below_meet_within_height {source : WellFormedType context.names}
    {types : List (WellFormedType context.names)}
    (sourceHeight : callableHeight source.raw ≤ height)
    (heights : ∀ type ∈ types, callableHeight type.raw ≤ height)
    (each : ∀ type ∈ types, check source type = true) :
    check source (WellFormedType.meetTypes context.valid.objectKnown types) = true := by
  induction types with
  | nil => exact laws.objectTop sourceHeight
  | cons first rest inductionHypothesis =>
      have restHeights := fun entry member => heights entry (List.mem_cons_of_mem first member)
      exact laws.interIntro sourceHeight (heights first List.mem_cons_self)
        (WellFormedType.meetTypes_height rest restHeights)
        (each first List.mem_cons_self)
        (inductionHypothesis restHeights (fun entry member => each entry (List.mem_cons_of_mem first member)))

/-- For listed types with function nesting at most `height`, the comparison
accepts each listed type below their join. -/
private theorem join_member_within_height {types : List (WellFormedType context.names)}
    {type : WellFormedType context.names}
    (heights : ∀ entry ∈ types, callableHeight entry.raw ≤ height)
    (member : type ∈ types) : check type (WellFormedType.joinTypes types) = true := by
  induction types with
  | nil => cases member
  | cons first rest inductionHypothesis =>
      have firstHeight := heights first List.mem_cons_self
      have restHeights := fun entry member => heights entry (List.mem_cons_of_mem first member)
      have targetHeight := heights type member
      rcases List.mem_cons.mp member with rfl | member
      · exact laws.unionLeft firstHeight firstHeight
          (WellFormedType.joinTypes_height rest restHeights) (laws.refl firstHeight)
      · exact laws.unionRight targetHeight firstHeight
          (WellFormedType.joinTypes_height rest restHeights) (inductionHypothesis restHeights member)

/-- If the target and listed types have function nesting at most `height`,
accepted comparisons from each listed type to the target extend to their join. -/
private theorem join_below_within_height {target : WellFormedType context.names}
    {types : List (WellFormedType context.names)}
    (targetHeight : callableHeight target.raw ≤ height)
    (heights : ∀ type ∈ types, callableHeight type.raw ≤ height)
    (each : ∀ type ∈ types, check type target = true) :
    check (WellFormedType.joinTypes types) target = true := by
  induction types with
  | nil => exact laws.bottom targetHeight
  | cons first rest inductionHypothesis =>
      have restHeights := fun entry member => heights entry (List.mem_cons_of_mem first member)
      exact laws.unionElim (heights first List.mem_cons_self)
        (WellFormedType.joinTypes_height rest restHeights) targetHeight
        (each first List.mem_cons_self)
        (inductionHypothesis restHeights (fun entry member => each entry (List.mem_cons_of_mem first member)))

/-- The comparison accepts swapped intersection operands when both have
function nesting at most `height`. -/
private theorem intersection_commutative_within_height {left right : WellFormedType context.names}
    (leftHeight : callableHeight left.raw ≤ height) (rightHeight : callableHeight right.raw ≤ height) :
    check (.intersection left right) (.intersection right left) = true :=
  laws.interIntro (Nat.max_le.mpr ⟨leftHeight, rightHeight⟩) rightHeight leftHeight
    (laws.interRight leftHeight rightHeight rightHeight (laws.refl rightHeight))
    (laws.interLeft leftHeight rightHeight leftHeight (laws.refl leftHeight))

/-- Within the function-nesting bound `height`, accepted comparisons from each
intersection alternative to the target extend to the intersection with their join. -/
private theorem inter_join_below_within_height {first target : WellFormedType context.names}
    {types : List (WellFormedType context.names)}
    (firstHeight : callableHeight first.raw ≤ height) (targetHeight : callableHeight target.raw ≤ height)
    (heights : ∀ type ∈ types, callableHeight type.raw ≤ height)
    (each : ∀ type ∈ types, check (.intersection first type) target = true) :
    check (.intersection first (WellFormedType.joinTypes types)) target = true := by
  induction types with
  | nil =>
      exact laws.trans (Nat.max_le.mpr ⟨firstHeight, Nat.zero_le _⟩) (Nat.zero_le _) targetHeight
        (laws.interRight firstHeight (Nat.zero_le _) (Nat.zero_le _) (laws.refl (Nat.zero_le _)))
        (laws.bottom targetHeight)
  | cons head tail inductionHypothesis =>
      have headHeight := heights head List.mem_cons_self
      have tailHeights := fun entry member => heights entry (List.mem_cons_of_mem head member)
      have tailHeight := WellFormedType.joinTypes_height tail tailHeights
      exact laws.trans
        (middle := .union (.intersection first head) (.intersection first (WellFormedType.joinTypes tail)))
        (Nat.max_le.mpr ⟨firstHeight, Nat.max_le.mpr ⟨headHeight, tailHeight⟩⟩)
        (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨firstHeight, headHeight⟩,
          Nat.max_le.mpr ⟨firstHeight, tailHeight⟩⟩) targetHeight
        (laws.distributes firstHeight headHeight tailHeight)
        (laws.unionElim (Nat.max_le.mpr ⟨firstHeight, headHeight⟩)
          (Nat.max_le.mpr ⟨firstHeight, tailHeight⟩) targetHeight
          (each head List.mem_cons_self)
          (inductionHypothesis tailHeights (fun entry member => each entry (List.mem_cons_of_mem head member))))

/-- Within the function-nesting bound `height`, accepted comparisons from every
pairwise intersection to the target extend to the intersection of the two joins. -/
private theorem joins_inter_below_within_height {target : WellFormedType context.names}
    {left right : List (WellFormedType context.names)}
    (targetHeight : callableHeight target.raw ≤ height)
    (leftHeights : ∀ type ∈ left, callableHeight type.raw ≤ height)
    (rightHeights : ∀ type ∈ right, callableHeight type.raw ≤ height)
    (each : ∀ first ∈ left, ∀ second ∈ right, check (.intersection first second) target = true) :
    check (.intersection (WellFormedType.joinTypes left) (WellFormedType.joinTypes right)) target = true := by
  have leftHeight := WellFormedType.joinTypes_height left leftHeights
  have rightHeight := WellFormedType.joinTypes_height right rightHeights
  apply laws.trans (first := .intersection (WellFormedType.joinTypes left) (WellFormedType.joinTypes right))
    (middle := .intersection (WellFormedType.joinTypes right) (WellFormedType.joinTypes left))
    (Nat.max_le.mpr ⟨leftHeight, rightHeight⟩)
    (Nat.max_le.mpr ⟨rightHeight, leftHeight⟩) targetHeight
    (intersection_commutative_within_height laws
      leftHeight rightHeight)
  apply inter_join_below_within_height laws
    rightHeight targetHeight leftHeights
  intro first firstMember
  apply laws.trans (first := .intersection (WellFormedType.joinTypes right) first)
    (middle := .intersection first (WellFormedType.joinTypes right))
    (Nat.max_le.mpr ⟨rightHeight, leftHeights first firstMember⟩)
    (Nat.max_le.mpr ⟨leftHeights first firstMember, rightHeight⟩) targetHeight
    (intersection_commutative_within_height laws
      rightHeight (leftHeights first firstMember))
  exact inter_join_below_within_height laws
    (leftHeights first firstMember) targetHeight rightHeights (each first firstMember)

/-- A larger requested result gives larger input coverage. -/
private theorem coverage_mono
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {left right : WellFormedType context.names}
    (sourceHeights : functionTypesWithinHeight source height)
    (leftHeight : callableHeight left.raw ≤ height) (rightHeight : callableHeight right.raw ≤ height)
    (included : check left right = true) :
    check (inputTypeForResultUsing context check source left)
      (inputTypeForResultUsing context check source right) = true := by
  apply join_below_within_height laws (inputTypeForResultUsing_height right sourceHeights)
    (selectedInputs_height left sourceHeights)
  intro input member
  obtain ⟨subset, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨listed, nonempty, resultCompared⟩ := selected_members.mp selected
  exact join_member_within_height laws (selectedInputs_height right sourceHeights)
    (List.mem_map.mpr ⟨subset, selected_members.mpr ⟨listed, nonempty,
      laws.trans (result_meet_height subset (subset_heights sourceHeights listed)) leftHeight rightHeight
        resultCompared included⟩, rfl⟩)

/-- Adding listed requirements narrows their meet: the larger list's meet is below
the smaller list's meet. -/
private theorem meet_antitone {smaller larger : List (WellFormedType context.names × WellFormedType context.names)}
    (project : WellFormedType context.names × WellFormedType context.names → WellFormedType context.names)
    (smallerHeights : ∀ type ∈ smaller.map project, callableHeight type.raw ≤ height)
    (largerHeights : ∀ type ∈ larger.map project, callableHeight type.raw ≤ height)
    (included : ∀ requirement ∈ smaller, requirement ∈ larger) :
    check (WellFormedType.meetTypes context.valid.objectKnown (larger.map project))
      (WellFormedType.meetTypes context.valid.objectKnown (smaller.map project)) = true := by
  apply below_meet_within_height laws (WellFormedType.meetTypes_height _ largerHeights) smallerHeights
  intro type member
  obtain ⟨requirement, present, rfl⟩ := List.mem_map.mp member
  exact meet_member_within_height laws largerHeights (List.mem_map.mpr ⟨requirement, included _ present, rfl⟩)

/-- Nonempty listed source requirements whose results meet below `result` contribute
their input meet to the input coverage. Filtering the source by these entries gives the
selected subset. -/
private theorem chosen_below_coverage
    {source chosen : List (WellFormedType context.names × WellFormedType context.names)}
    {result : WellFormedType context.names}
    (sourceHeights : functionTypesWithinHeight source height)
    (resultHeight : callableHeight result.raw ≤ height)
    (chosenMembers : ∀ requirement ∈ chosen, requirement ∈ source) (nonempty : chosen ≠ [])
    (resultCompared :
      check (WellFormedType.meetTypes context.valid.objectKnown (chosen.map Prod.snd)) result = true) :
    check (WellFormedType.meetTypes context.valid.objectKnown (chosen.map Prod.fst))
      (inputTypeForResultUsing context check source result) = true := by
  have chosenHeights := fun requirement member => sourceHeights requirement (chosenMembers requirement member)
  let selected := source.filter fun requirement => decide (requirement ∈ chosen)
  have selectedMembers (requirement : WellFormedType context.names × WellFormedType context.names) :
      requirement ∈ selected ↔ requirement ∈ source ∧ requirement ∈ chosen := by
    simp only [selected, List.mem_filter, decide_eq_true_eq]
  have selectedHeights :=
    fun requirement member => sourceHeights requirement ((selectedMembers requirement).mp member).1
  have chosenSelected {requirement} (member : requirement ∈ chosen) : requirement ∈ selected :=
    (selectedMembers requirement).mpr ⟨chosenMembers requirement member, member⟩
  have listed : selected ∈ subsetsWithResultBelowUsing context check source result :=
    selected_members.mpr ⟨mem_subsequences.mpr (List.filter_sublist ..),
      let ⟨_, present⟩ := List.exists_mem_of_ne_nil chosen nonempty
      List.ne_nil_of_mem (chosenSelected present),
      laws.trans (result_meet_height selected selectedHeights) (result_meet_height chosen chosenHeights) resultHeight
        (meet_antitone laws Prod.snd (result_types_height chosenHeights) (result_types_height selectedHeights)
          (fun _ member => chosenSelected member))
        resultCompared⟩
  exact laws.trans (input_meet_height chosen chosenHeights) (input_meet_height selected selectedHeights)
    (inputTypeForResultUsing_height result sourceHeights)
    (meet_antitone laws Prod.fst (input_types_height selectedHeights) (input_types_height chosenHeights)
      (fun requirement member => ((selectedMembers requirement).mp member).2))
    (join_member_within_height laws (selectedInputs_height result sourceHeights)
      (List.mem_map.mpr ⟨selected, listed, rfl⟩))

/-- Every source requirement is covered by its nonempty singleton subset. -/
private theorem coverage_member
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {requirement : WellFormedType context.names × WellFormedType context.names}
    (sourceHeights : functionTypesWithinHeight source height)
    (member : requirement ∈ source) :
    check requirement.1 (inputTypeForResultUsing context check source requirement.2) = true := by
  have inputHeight := (sourceHeights requirement member).1
  have resultHeight := (sourceHeights requirement member).2
  exact laws.trans (middle := .intersection requirement.1 context.objectType)
    inputHeight (Nat.max_le.mpr ⟨inputHeight, Nat.zero_le _⟩)
    (inputTypeForResultUsing_height requirement.2 sourceHeights)
    (laws.interIntro inputHeight inputHeight (Nat.zero_le _) (laws.refl inputHeight) (laws.objectTop inputHeight))
    (chosen_below_coverage laws (chosen := [requirement]) sourceHeights resultHeight (by simpa using member) (by simp)
      (laws.interLeft resultHeight (Nat.zero_le _) resultHeight (laws.refl resultHeight)))

/-- Inputs covered for both results are covered for their simultaneous result intersection. -/
private theorem coverage_meet_right
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {left right : WellFormedType context.names}
    (sourceHeights : functionTypesWithinHeight source height)
    (leftHeight : callableHeight left.raw ≤ height) (rightHeight : callableHeight right.raw ≤ height) :
    check (.intersection (inputTypeForResultUsing context check source left)
      (inputTypeForResultUsing context check source right))
      (inputTypeForResultUsing context check source (.intersection left right)) = true := by
  apply joins_inter_below_within_height laws
    (inputTypeForResultUsing_height (.intersection left right) sourceHeights)
    (selectedInputs_height left sourceHeights) (selectedInputs_height right sourceHeights)
  intro first firstMember second secondMember
  obtain ⟨firstSubset, firstSelected, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨secondSubset, secondSelected, rfl⟩ := List.mem_map.mp secondMember
  obtain ⟨firstListed, firstNonempty, firstCompared⟩ := selected_members.mp firstSelected
  obtain ⟨secondListed, _, secondCompared⟩ := selected_members.mp secondSelected
  have firstHeights := subset_heights sourceHeights firstListed
  have secondHeights := subset_heights sourceHeights secondListed
  have bothMembers (requirement) (present : requirement ∈ firstSubset ++ secondSubset) : requirement ∈ source := by
    rcases List.mem_append.mp present with first | second
    · exact (mem_subsequences.mp firstListed).subset first
    · exact (mem_subsequences.mp secondListed).subset second
  have bothHeights := fun requirement present => sourceHeights requirement (bothMembers requirement present)
  have firstHeight := input_meet_height firstSubset firstHeights
  have secondHeight := input_meet_height secondSubset secondHeights
  let inputs := WellFormedType.intersection
    (WellFormedType.meetTypes context.valid.objectKnown (firstSubset.map Prod.fst))
    (WellFormedType.meetTypes context.valid.objectKnown (secondSubset.map Prod.fst))
  apply laws.trans (first := inputs)
    (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) (input_meet_height _ bothHeights)
    (inputTypeForResultUsing_height (.intersection left right) sourceHeights) ?_
    (chosen_below_coverage laws sourceHeights (Nat.max_le.mpr ⟨leftHeight, rightHeight⟩) bothMembers
      (fun empty => firstNonempty (List.append_eq_nil_iff.mp empty).1)
      (laws.interIntro (result_meet_height _ bothHeights) leftHeight rightHeight
        (laws.trans (result_meet_height _ bothHeights) (result_meet_height _ firstHeights) leftHeight
          (meet_antitone laws Prod.snd (result_types_height firstHeights) (result_types_height bothHeights)
            (fun _ present => List.mem_append_left _ present)) firstCompared)
        (laws.trans (result_meet_height _ bothHeights) (result_meet_height _ secondHeights) rightHeight
          (meet_antitone laws Prod.snd (result_types_height secondHeights) (result_types_height bothHeights)
            (fun _ present => List.mem_append_right _ present)) secondCompared)))
  apply below_meet_within_height laws (source := inputs)
    (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) (input_types_height bothHeights)
  intro input member
  obtain ⟨requirement, present, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp present with first | second
  · exact laws.interLeft firstHeight secondHeight ((firstHeights requirement first).1)
      (meet_member_within_height laws (input_types_height firstHeights)
        (List.mem_map.mpr ⟨requirement, first, rfl⟩))
  · exact laws.interRight firstHeight secondHeight ((secondHeights requirement second).1)
      (meet_member_within_height laws (input_types_height secondHeights)
        (List.mem_map.mpr ⟨requirement, second, rfl⟩))

/-- Nonempty result meets preserve simultaneous input coverage. -/
private theorem below_coverage_meet
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {input : WellFormedType context.names} {results : List (WellFormedType context.names)}
    (sourceHeights : functionTypesWithinHeight source height)
    (inputHeight : callableHeight input.raw ≤ height)
    (resultHeights : ∀ result ∈ results, callableHeight result.raw ≤ height)
    (nonempty : results ≠ [])
    (each : ∀ result ∈ results, check input (inputTypeForResultUsing context check source result) = true) :
    check input
      (inputTypeForResultUsing context check source
        (WellFormedType.meetTypes context.valid.objectKnown results)) = true := by
  induction results with
  | nil => exact (nonempty rfl).elim
  | cons head tail inductionHypothesis =>
      have headHeight := resultHeights head List.mem_cons_self
      cases tail with
      | nil =>
          exact laws.trans inputHeight (inputTypeForResultUsing_height head sourceHeights)
            (inputTypeForResultUsing_height (.intersection head context.objectType) sourceHeights)
            (each head List.mem_cons_self)
            (coverage_mono laws sourceHeights headHeight (Nat.max_le.mpr ⟨headHeight, Nat.zero_le _⟩)
              (laws.interIntro headHeight headHeight (Nat.zero_le _)
                (laws.refl headHeight) (laws.objectTop headHeight)))
      | cons next rest =>
          have tailHeights := fun result member => resultHeights result (List.mem_cons_of_mem head member)
          have tailHeight := WellFormedType.meetTypes_height (next :: rest) tailHeights
          exact laws.trans (middle := .intersection (inputTypeForResultUsing context check source head)
            (inputTypeForResultUsing context check source
              (WellFormedType.meetTypes context.valid.objectKnown (next :: rest))))
            inputHeight (Nat.max_le.mpr ⟨inputTypeForResultUsing_height head sourceHeights,
              inputTypeForResultUsing_height _ sourceHeights⟩)
            (inputTypeForResultUsing_height _ sourceHeights)
            (laws.interIntro inputHeight (inputTypeForResultUsing_height head sourceHeights)
              (inputTypeForResultUsing_height _ sourceHeights)
              (each head List.mem_cons_self)
              (inductionHypothesis tailHeights (by simp)
                (fun result member => each result (List.mem_cons_of_mem head member))))
            (coverage_meet_right laws sourceHeights headHeight tailHeight)

/-- Covering each middle requirement puts the middle input coverage below the source input coverage. -/
private theorem coverage_transfer
    {source middle : List (WellFormedType context.names × WellFormedType context.names)}
    {result : WellFormedType context.names}
    (sourceHeights : functionTypesWithinHeight source height)
    (middleHeights : functionTypesWithinHeight middle height)
    (resultHeight : callableHeight result.raw ≤ height)
    (covered : ∀ requirement ∈ middle,
      check requirement.1 (inputTypeForResultUsing context check source requirement.2) = true) :
    check (inputTypeForResultUsing context check middle result)
      (inputTypeForResultUsing context check source result) = true := by
  apply join_below_within_height laws (inputTypeForResultUsing_height result sourceHeights)
    (selectedInputs_height result middleHeights)
  intro input member
  obtain ⟨subset, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨listed, nonempty, resultCompared⟩ := selected_members.mp selected
  have subsetHeights := subset_heights middleHeights listed
  apply laws.trans
    (input_meet_height subset subsetHeights) (inputTypeForResultUsing_height _ sourceHeights)
    (inputTypeForResultUsing_height result sourceHeights) ?_
    (coverage_mono laws sourceHeights (result_meet_height subset subsetHeights) resultHeight resultCompared)
  apply below_coverage_meet laws sourceHeights (input_meet_height subset subsetHeights)
    (result_types_height subsetHeights)
  · exact fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  · intro result member
    obtain ⟨requirement, present, rfl⟩ := List.mem_map.mp member
    exact laws.trans
      (input_meet_height subset subsetHeights) ((subsetHeights requirement present).1)
      (inputTypeForResultUsing_height requirement.2 sourceHeights)
      (meet_member_within_height laws (input_types_height subsetHeights)
        (List.mem_map.mpr ⟨requirement, present, rfl⟩))
      (covered requirement ((mem_subsequences.mp listed).subset present))

/-- A type intersection compares below itself through singleton coverage. -/
private theorem intersection_refl (source : TypeIntersection context)
    (heights : functionTypesWithinHeight source.functionTypes height) :
    IntersectionBelow check source source :=
  ⟨fun _ _ => rfl, fun _ member => coverage_member laws heights member⟩

/-- Intersection comparisons compose through their shared complete class conjunction. -/
private theorem intersection_trans (source middle target : TypeIntersection context)
    (sourceHeights : functionTypesWithinHeight source.functionTypes height)
    (middleHeights : functionTypesWithinHeight middle.functionTypes height)
    (targetHeights : functionTypesWithinHeight target.functionTypes height)
    (first : IntersectionBelow check source middle)
    (second : IntersectionBelow check middle target) :
    IntersectionBelow check source target :=
  ⟨fun name known => (first.1 name known).trans (second.1 name known),
    fun requirement member => laws.trans
      ((targetHeights requirement member).1)
      (inputTypeForResultUsing_height requirement.2 middleHeights)
      (inputTypeForResultUsing_height requirement.2 sourceHeights)
      (second.2 requirement member)
      (coverage_transfer laws sourceHeights middleHeights (targetHeights requirement member).2 first.2)⟩

end

/-- Lattice laws for the callback up to function nesting `lower` give the normalized
comparison those laws up to `upper`, when `upper ≤ lower + 1`. -/
private theorem normal_lattice_laws {check : WellFormedType context.names → WellFormedType context.names → Bool}
    {upper lower : Nat} (laws : LatticeLaws check lower) (enough : upper ≤ lower + 1) :
    LatticeLaws (normalCheckUsing context check) upper := by
  have retainedHeights (type : WellFormedType context.names) (typeHeight : callableHeight type.raw ≤ upper) :
      ∀ intersection ∈ (splitIntoIntersections context type).intersections,
        functionTypesWithinHeight intersection.functionTypes lower := by
    intro intersection member
    exact (splitIntoIntersections context type).retainedWithinHeight
      (Nat.le_trans typeHeight enough) member
  constructor
  · intro type typeHeight
    apply normalCheckUsing_iff.mpr
    intro intersection member
    exact ⟨intersection, member,
      intersection_refl laws intersection (retainedHeights type typeHeight intersection member)⟩
  · intro first middle last firstHeight middleHeight lastHeight firstAccepted secondAccepted
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection member
    obtain ⟨middleIntersection, middleMember, firstIncluded⟩ :=
      normalCheckUsing_iff.mp firstAccepted sourceIntersection member
    obtain ⟨targetIntersection, targetMember, secondIncluded⟩ :=
      normalCheckUsing_iff.mp secondAccepted middleIntersection middleMember
    exact ⟨targetIntersection, targetMember,
      intersection_trans laws sourceIntersection middleIntersection targetIntersection
        (retainedHeights first firstHeight sourceIntersection member)
        (retainedHeights middle middleHeight middleIntersection middleMember)
        (retainedHeights last lastHeight targetIntersection targetMember) firstIncluded secondIncluded⟩
  · intro type _
    apply normalCheckUsing_iff.mpr
    rw [splitIntoIntersections_bottom]
    intro intersection member
    cases member
  · intro type _
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection _
    obtain ⟨targetIntersection, targetMember, same, empty⟩ :=
      splitIntoIntersections_object_matches sourceIntersection.classIntersection
    exact ⟨targetIntersection, targetMember, same,
      fun _ member => nomatch (empty ▸ member)⟩
  · intro first second target firstHeight secondHeight targetHeight included
    apply normalCheckUsing_iff.mpr
    intro combined member
    obtain ⟨left, leftMember, _, _, _, classes, functions⟩ :=
      (splitIntoIntersections_intersection_iff first second combined).mp member
    have combinedHeights :=
      retainedHeights (.intersection first second) (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) combined member
    obtain ⟨targetIntersection, targetMember, covered⟩ :=
      normalCheckUsing_iff.mp included left leftMember
    exact ⟨targetIntersection, targetMember,
      intersection_trans laws combined left targetIntersection
        combinedHeights (retainedHeights first firstHeight left leftMember)
        (retainedHeights target targetHeight targetIntersection targetMember)
        ⟨fun name _ => by rw [classes], fun _ required => coverage_member laws combinedHeights
          (by rw [functions]; exact List.mem_append_left _ required)⟩
        covered⟩
  · intro first second target firstHeight secondHeight targetHeight included
    apply normalCheckUsing_iff.mpr
    intro combined member
    obtain ⟨_, _, right, rightMember, same, classes, functions⟩ :=
      (splitIntoIntersections_intersection_iff first second combined).mp member
    have combinedHeights :=
      retainedHeights (.intersection first second) (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) combined member
    obtain ⟨targetIntersection, targetMember, covered⟩ :=
      normalCheckUsing_iff.mp included right rightMember
    exact ⟨targetIntersection, targetMember,
      intersection_trans laws combined right targetIntersection
        combinedHeights (retainedHeights second secondHeight right rightMember)
        (retainedHeights target targetHeight targetIntersection targetMember)
        ⟨fun name known => by rw [classes]; exact same name known,
          fun _ required => coverage_member laws combinedHeights
            (by rw [functions]; exact List.mem_append_right _ required)⟩
        covered⟩
  · intro source first second _ _ _ firstAccepted secondAccepted
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection member
    obtain ⟨left, leftMember, coveredLeft⟩ :=
      normalCheckUsing_iff.mp firstAccepted sourceIntersection member
    obtain ⟨right, rightMember, coveredRight⟩ :=
      normalCheckUsing_iff.mp secondAccepted sourceIntersection member
    have same : ClassIntersection.sameClasses left.classIntersection right.classIntersection :=
      fun name known => (coveredLeft.1 name known).symm.trans (coveredRight.1 name known)
    obtain ⟨combined, combinedMember, classesEqual, functionsEqual⟩ :=
      splitIntoIntersections_intersection_of_members leftMember rightMember same
    exact ⟨combined, combinedMember, classesEqual ▸ coveredLeft.1, fun requirement member =>
      (List.mem_append.mp (functionsEqual ▸ member)).elim
        (coveredLeft.2 requirement) (coveredRight.2 requirement)⟩
  · intro source first second _ _ _ included
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection member
    obtain ⟨targetIntersection, present, covered⟩ :=
      normalCheckUsing_iff.mp included sourceIntersection member
    refine ⟨targetIntersection, ?_, covered⟩
    rw [splitIntoIntersections_union]
    exact List.mem_append_left _ present
  · intro source first second _ _ _ included
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection member
    obtain ⟨targetIntersection, present, covered⟩ :=
      normalCheckUsing_iff.mp included sourceIntersection member
    refine ⟨targetIntersection, ?_, covered⟩
    rw [splitIntoIntersections_union]
    exact List.mem_append_right _ present
  · intro first second target _ _ _ firstAccepted secondAccepted
    apply normalCheckUsing_iff.mpr
    intro sourceIntersection member
    rw [splitIntoIntersections_union] at member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact normalCheckUsing_iff.mp firstAccepted sourceIntersection leftMember
    · exact normalCheckUsing_iff.mp secondAccepted sourceIntersection rightMember
  · intro first second third firstHeight secondHeight thirdHeight
    apply normalCheckUsing_iff.mpr
    intro combined member
    obtain ⟨left, leftMember, right, rightMember, same, classes, functions⟩ :=
      (splitIntoIntersections_intersection_iff first (WellFormedType.union second third) combined).mp member
    refine ⟨combined, ?_, intersection_refl laws combined
      (retainedHeights (.intersection first (.union second third))
        (Nat.max_le.mpr ⟨firstHeight, Nat.max_le.mpr ⟨secondHeight, thirdHeight⟩⟩) combined member)⟩
    rw [splitIntoIntersections_union] at rightMember ⊢
    rcases List.mem_append.mp rightMember with secondMember | thirdMember
    · exact List.mem_append_left _
        ((splitIntoIntersections_intersection_iff first second combined).mpr
          ⟨left, leftMember, right, secondMember, same, classes, functions⟩)
    · exact List.mem_append_right _
        ((splitIntoIntersections_intersection_iff first third combined).mpr
          ⟨left, leftMember, right, thirdMember, same, classes, functions⟩)

/-- Checks that agree on types with function nesting at most `height` satisfy the same lattice laws. -/
private theorem lattice_laws_transfer
    {firstCheck secondCheck : WellFormedType context.names → WellFormedType context.names → Bool}
    {height : Nat} (laws : LatticeLaws firstCheck height)
    (same : ∀ first second : WellFormedType context.names,
      callableHeight first.raw ≤ height → callableHeight second.raw ≤ height →
      firstCheck first second = secondCheck first second) :
    LatticeLaws secondCheck height := by
  have sameBelow (first second : WellFormedType context.names)
      (firstHeight : callableHeight first.raw ≤ height) (secondHeight : callableHeight second.raw ≤ height) :
      (firstCheck first second = true) ↔ (secondCheck first second = true) := by
    rw [same first second firstHeight secondHeight]
  constructor
  · intro type typeHeight
    exact (sameBelow type type typeHeight typeHeight).mp (laws.refl typeHeight)
  · intro first middle last firstHeight middleHeight lastHeight firstAccepted secondAccepted
    exact (sameBelow first last firstHeight lastHeight).mp
      (laws.trans firstHeight middleHeight lastHeight
        ((sameBelow first middle firstHeight middleHeight).mpr firstAccepted)
        ((sameBelow middle last middleHeight lastHeight).mpr secondAccepted))
  · intro type typeHeight
    exact (sameBelow .bottom type (Nat.zero_le _) typeHeight).mp (laws.bottom typeHeight)
  · intro type typeHeight
    exact (sameBelow type context.objectType typeHeight (Nat.zero_le _)).mp (laws.objectTop typeHeight)
  · intro first second target firstHeight secondHeight targetHeight included
    exact (sameBelow (.intersection first second) target (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) targetHeight).mp
      (laws.interLeft firstHeight secondHeight targetHeight
        ((sameBelow first target firstHeight targetHeight).mpr included))
  · intro first second target firstHeight secondHeight targetHeight included
    exact (sameBelow (.intersection first second) target (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) targetHeight).mp
      (laws.interRight firstHeight secondHeight targetHeight
        ((sameBelow second target secondHeight targetHeight).mpr included))
  · intro source first second sourceHeight firstHeight secondHeight firstAccepted secondAccepted
    exact (sameBelow source (.intersection first second) sourceHeight (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩)).mp
      (laws.interIntro sourceHeight firstHeight secondHeight
        ((sameBelow source first sourceHeight firstHeight).mpr firstAccepted)
        ((sameBelow source second sourceHeight secondHeight).mpr secondAccepted))
  · intro source first second sourceHeight firstHeight secondHeight included
    exact (sameBelow source (.union first second) sourceHeight (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩)).mp
      (laws.unionLeft sourceHeight firstHeight secondHeight
        ((sameBelow source first sourceHeight firstHeight).mpr included))
  · intro source first second sourceHeight firstHeight secondHeight included
    exact (sameBelow source (.union first second) sourceHeight (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩)).mp
      (laws.unionRight sourceHeight firstHeight secondHeight
        ((sameBelow source second sourceHeight secondHeight).mpr included))
  · intro first second target firstHeight secondHeight targetHeight firstAccepted secondAccepted
    exact (sameBelow (.union first second) target (Nat.max_le.mpr ⟨firstHeight, secondHeight⟩) targetHeight).mp
      (laws.unionElim firstHeight secondHeight targetHeight
        ((sameBelow first target firstHeight targetHeight).mpr firstAccepted)
        ((sameBelow second target secondHeight targetHeight).mpr secondAccepted))
  · intro first second third firstHeight secondHeight thirdHeight
    exact (sameBelow (.intersection first (.union second third))
      (.union (.intersection first second) (.intersection first third))
      (Nat.max_le.mpr ⟨firstHeight, Nat.max_le.mpr ⟨secondHeight, thirdHeight⟩⟩)
      (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨firstHeight, secondHeight⟩, Nat.max_le.mpr ⟨firstHeight, thirdHeight⟩⟩)).mp
      (laws.distributes firstHeight secondHeight thirdHeight)

/-- The public comparison satisfies the lattice laws on types with function nesting at most `height`. -/
private theorem global_check_lattice (height : Nat) :
    LatticeLaws (checkSubtypeBool context) height := by
  apply lattice_laws_transfer (firstCheck := checkSubtypeWithDepth context (height + 1))
  · induction height with
    | zero => exact normal_lattice_laws (by constructor <;> intros <;> rfl) (Nat.zero_le 1)
    | succ height inductionHypothesis => exact normal_lattice_laws inductionHypothesis (Nat.le_refl _)
  · intro first second firstHeight secondHeight
    apply checkSubtypeWithDepth_depth_independent <;> omega

/-- Each valid type compares below itself. -/
private theorem check_refl {type : WellFormedType context.names} :
    checkSubtypeBool context type type = true :=
  (global_check_lattice (callableHeight type.raw)).refl (Nat.le_refl _)

/-- Two accepted comparisons with a shared middle type compose. -/
private theorem check_trans {first middle last : WellFormedType context.names}
    (firstAccepted : checkSubtypeBool context first middle = true)
    (secondAccepted : checkSubtypeBool context middle last = true) :
    checkSubtypeBool context first last = true :=
  (global_check_lattice (callableHeight first.raw + callableHeight middle.raw + callableHeight last.raw)).trans
    (by omega) (by omega) (by omega) firstAccepted secondAccepted

/-- Bottom compares below every valid type. -/
private theorem check_bottom {type : WellFormedType context.names} :
    checkSubtypeBool context .bottom type = true :=
  (global_check_lattice (callableHeight type.raw)).bottom (Nat.le_refl _)

/-- Every valid type compares below Object. -/
private theorem check_object_top {type : WellFormedType context.names} :
    checkSubtypeBool context type context.objectType = true :=
  (global_check_lattice (callableHeight type.raw)).objectTop (Nat.le_refl _)

/-- Adding an intersection operand preserves an accepted comparison from the first operand. -/
private theorem check_inter_left {first second target : WellFormedType context.names}
    (included : checkSubtypeBool context first target = true) :
    checkSubtypeBool context (.intersection first second) target = true :=
  (global_check_lattice (callableHeight first.raw + callableHeight second.raw + callableHeight target.raw)).interLeft
    (by omega) (by omega) (by omega) included

/-- Adding an intersection operand preserves an accepted comparison from the second operand. -/
private theorem check_inter_right {first second target : WellFormedType context.names}
    (included : checkSubtypeBool context second target = true) :
    checkSubtypeBool context (.intersection first second) target = true :=
  (global_check_lattice (callableHeight first.raw + callableHeight second.raw + callableHeight target.raw)).interRight
    (by omega) (by omega) (by omega) included

/-- Accepted comparisons from one source to two targets give an accepted comparison to their intersection. -/
private theorem check_inter_intro {source first second : WellFormedType context.names}
    (firstAccepted : checkSubtypeBool context source first = true)
    (secondAccepted : checkSubtypeBool context source second = true) :
    checkSubtypeBool context source (.intersection first second) = true :=
  (global_check_lattice (callableHeight source.raw + callableHeight first.raw + callableHeight second.raw)).interIntro
    (by omega) (by omega) (by omega) firstAccepted secondAccepted

/-- Adding a union alternative preserves an accepted comparison to the first alternative. -/
private theorem check_union_left {source first second : WellFormedType context.names}
    (included : checkSubtypeBool context source first = true) :
    checkSubtypeBool context source (.union first second) = true :=
  (global_check_lattice (callableHeight source.raw + callableHeight first.raw + callableHeight second.raw)).unionLeft
    (by omega) (by omega) (by omega) included

/-- Adding a union alternative preserves an accepted comparison to the second alternative. -/
private theorem check_union_right {source first second : WellFormedType context.names}
    (included : checkSubtypeBool context source second = true) :
    checkSubtypeBool context source (.union first second) = true :=
  (global_check_lattice (callableHeight source.raw + callableHeight first.raw + callableHeight second.raw)).unionRight
    (by omega) (by omega) (by omega) included

/-- Comparisons from both union operands to one target give an accepted comparison from their union. -/
private theorem check_union_elim {first second target : WellFormedType context.names}
    (firstAccepted : checkSubtypeBool context first target = true)
    (secondAccepted : checkSubtypeBool context second target = true) :
    checkSubtypeBool context (.union first second) target = true :=
  (global_check_lattice (callableHeight first.raw + callableHeight second.raw + callableHeight target.raw)).unionElim
    (by omega) (by omega) (by omega) firstAccepted secondAccepted

/-- Intersection distributes over union for valid types. -/
private theorem check_distributes {first second third : WellFormedType context.names} :
    checkSubtypeBool context (.intersection first (.union second third))
      (.union (.intersection first second) (.intersection first third)) = true :=
  (global_check_lattice (callableHeight first.raw + callableHeight second.raw + callableHeight third.raw)).distributes
    (by omega) (by omega) (by omega)

section EquationGenerators

/-- `Below source target` means that the Boolean comparison accepts this subtype pair.
Both types are valid packages in the current class context. -/
local notation "Below" =>
  (fun (source target : WellFormedType context.names) => checkSubtypeBool context source target = true)

/-- Acceptance in both directions between valid type packages. -/
private def Mutual (source target : WellFormedType context.names) : Prop := Below source target ∧ Below target source

/-- A source with no normalized intersections compares below bottom. -/
private theorem below_bottom_of_no_intersections
    {source : WellFormedType context.names}
    (empty : ∀ intersection, intersection ∈ (splitIntoIntersections context source).intersections → False) :
    Below source .bottom :=
  (checkSubtypeBool_iff_intersections context _ _).mpr (fun intersection member => (empty intersection member).elim)

/-- A class intersected with its exclusion and bottom compare in both directions. -/
private theorem class_contradiction
    {name : Identifier} (known : name ∈ context.names) :
    Mutual (.intersection (.class_ name known) (.negClass name known)) .bottom := by
  refine ⟨below_bottom_of_no_intersections ?_, check_bottom⟩
  intro intersection member
  have positive := (checkSubtypeBool_classLiteral_iff context _ name known true).mp
    (check_inter_left check_refl) intersection member
  have negative := (checkSubtypeBool_classLiteral_iff context _ name known false).mp
    (check_inter_right check_refl) intersection member
  exact Bool.noConfusion (positive.symm.trans negative)

/-- A class unioned with its exclusion and Object compare in both directions. -/
private theorem class_complement
    {name : Identifier} (known : name ∈ context.names) :
    Mutual (.union (.class_ name known) (.negClass name known)) context.objectType := by
  refine ⟨check_object_top, (checkSubtypeBool_iff_intersections context _ _).mpr ?_⟩
  intro intersection _
  cases sign : intersection.classIntersection.includesClass name <;>
    obtain ⟨target, targetMember, same, empty⟩ :=
      splitIntoIntersections_classLiteral_matches intersection.classIntersection name known _ sign <;>
    refine ⟨target, ?_, same, fun _ member => nomatch (empty ▸ member)⟩ <;>
    rw [splitIntoIntersections_union]
  · exact List.mem_append_right _ targetMember
  · exact List.mem_append_left _ targetMember

/-- Intersecting a class with any ancestor and the class alone compare in both directions. -/
private theorem class_inheritance
    {name ancestor : Identifier} (known : name ∈ context.names)
    (inherited : ancestor ∈ context.ancestors name) :
    Mutual (.intersection (.class_ name known)
      (.class_ ancestor (context.valid.ancestorsKnown _ known _ inherited))) (.class_ name known) := by
  refine ⟨check_inter_left check_refl, check_inter_intro check_refl ?_⟩
  apply (checkSubtypeBool_classLiteral_iff context _ ancestor
    (context.valid.ancestorsKnown _ known _ inherited) true).mpr
  intro intersection member
  have included := (checkSubtypeBool_classLiteral_iff context _ name known true).mp
    check_refl intersection member
  exact (intersection.classIntersection.includesClass_iff_mem ancestor).mpr
    (intersection.classIntersection.constraints.inheritance name known
      ((intersection.classIntersection.includesClass_iff_mem name).mp included) ancestor inherited)

/-- A sealed class intersected with a known class outside its MRO and bottom compare in both directions. -/
private theorem sealed_exclusion
    {builtin name : Identifier} (sealed : builtin ∈ sealedClasses)
    (known : name ∈ context.names) (outside : name ∉ context.ancestors builtin) :
    Mutual (.intersection (.class_ builtin (context.valid.sealedKnown _ sealed))
      (.class_ name known)) .bottom := by
  refine ⟨below_bottom_of_no_intersections ?_, check_bottom⟩
  intro intersection member
  have builtinAnswer := (checkSubtypeBool_classLiteral_iff context _ builtin
    (context.valid.sealedKnown _ sealed) true).mp (check_inter_left check_refl) intersection member
  have included := (checkSubtypeBool_classLiteral_iff context _ name known true).mp
    (check_inter_right check_refl) intersection member
  exact outside ((intersection.classIntersection.constraints.sealing builtin sealed
    ((intersection.classIntersection.includesClass_iff_mem builtin).mp builtinAnswer) name known).mp
      ((intersection.classIntersection.includesClass_iff_mem name).mp included))

/-- The comparison accepts each listed type below the join of the listed valid types. -/
private theorem join_member (types : List (WellFormedType context.names))
    (type : WellFormedType context.names) (member : type ∈ types) :
    Below type (WellFormedType.joinTypes types) := by
  induction types with
  | nil => cases member
  | cons first rest inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | member
      · exact check_union_left check_refl
      · exact check_union_right (inductionHypothesis member)

/-- The comparison accepts the meet of known classes and bottom in both directions
when their MROs have no common order. -/
private theorem incompatible_classes
    (classes : List Identifier) (known : ∀ name ∈ classes, name ∈ context.names)
    (failed : hasValidClassOrder context classes = false) :
    Mutual (WellFormedType.meetTypes context.valid.objectKnown
      (classes.attach.map fun name => .class_ name.val (known _ name.property))) .bottom := by
  refine ⟨below_bottom_of_no_intersections ?_, check_bottom⟩
  intro intersection member
  have compatible := hasValidClassOrder_of_subset intersection.classIntersection.constraints.orderCompatible
    (fun name _ listed => (intersection.classIntersection.includesClass_iff_mem name).mp
      ((checkSubtypeBool_classLiteral_iff context _ name (known name listed) true).mp
        (meet_member_within_height (global_check_lattice 0)
          (fun _ member => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp member; exact Nat.le_refl 0)
          (List.mem_map.mpr ⟨⟨name, listed⟩, List.mem_attach _ _, rfl⟩)) intersection member))
  exact Bool.noConfusion (compatible.symm.trans failed)

/-- Singleton coverage suffices to compare two function types. -/
private theorem callable_below_callable
    {sourceInput sourceResult targetInput targetResult : WellFormedType context.names}
    (covered : Below targetInput (inputTypeForResult context [(sourceInput, sourceResult)] targetResult)) :
    Below (.callable sourceInput sourceResult) (.callable targetInput targetResult) := by
  apply checkSubtypeBool_of_callable_coverage
  intro intersection member
  rw [splitIntoIntersections_callable] at member
  cases List.mem_singleton.mp member
  exact ⟨fun _ _ => rfl, covered⟩

/-- Coverage by the complete two-element requirement list accepts the intersection of two callables. -/
private theorem two_callable_below
    (firstInput firstResult secondInput secondResult parameter result : WellFormedType context.names)
    (covered : Below parameter (inputTypeForResult context
      [(firstInput, firstResult), (secondInput, secondResult)] result)) :
    Below (.intersection (.callable firstInput firstResult) (.callable secondInput secondResult))
      (.callable parameter result) := by
  apply checkSubtypeBool_of_callable_coverage
  intro intersection member
  rw [splitIntoIntersections_intersection_iff] at member
  simp only [splitIntoIntersections_callable, List.mem_singleton, exists_eq_left] at member
  rw [member.2.1, member.2.2]
  exact ⟨fun _ _ => rfl, covered⟩

/-- A selected nonempty subset whose result meet compares below the requested result
contributes its input meet to input coverage. -/
private theorem selected_input_below_coverage
    (source subset : List (WellFormedType context.names × WellFormedType context.names))
    (result : WellFormedType context.names)
    (listed : subset ∈ subsequences source) (nonempty : subset ≠ [])
    (results : Below (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.snd)) result) :
    Below (WellFormedType.meetTypes context.valid.objectKnown (subset.map Prod.fst))
      (inputTypeForResult context source result) := by
  apply join_member
  exact List.mem_map.mpr ⟨subset, List.mem_filter.mpr
    ⟨mem_nonemptySubsets.mpr ⟨listed, nonempty⟩, results⟩, rfl⟩

/-- A listed source function covers its input for every result above its own result. -/
private theorem member_input_below
    {source : List (WellFormedType context.names × WellFormedType context.names)}
    {input output result : WellFormedType context.names}
    (member : (input, output) ∈ source) (results : Below output result) :
    Below input (inputTypeForResult context source result) :=
  check_trans (check_inter_intro check_refl check_object_top)
    (selected_input_below_coverage source [(input, output)] result
      (mem_subsequences.mpr (List.singleton_sublist.mpr member)) (by simp)
      (check_trans (check_inter_left check_refl) results))

/-- Accepted input comparisons are reversed for functions, while accepted result comparisons
keep their direction. -/
private theorem callable_monotone
    {sourceInput sourceResult targetInput targetResult : WellFormedType context.names}
    (input : Below targetInput sourceInput) (result : Below sourceResult targetResult) :
    Below (.callable sourceInput sourceResult) (.callable targetInput targetResult) :=
  callable_below_callable
    (check_trans input (member_input_below (List.mem_singleton_self _) result))

/-- The comparison accepts a function on a union input and the intersection
of the two functions on its alternatives in both directions. -/
private theorem function_union_input
    {first second result : WellFormedType context.names} :
    Mutual (.callable (.union first second) result)
      (.intersection (.callable first result) (.callable second result)) := by
  have singleton : Below (.union first second)
      (inputTypeForResult context [(.union first second, result)] result) :=
    member_input_below (List.mem_singleton_self _) check_refl
  refine ⟨check_inter_intro
    (callable_below_callable (check_trans (check_union_left check_refl) singleton))
    (callable_below_callable (check_trans (check_union_right check_refl) singleton)), ?_⟩
  apply two_callable_below
  apply check_union_elim <;> exact member_input_below (by simp) check_refl

/-- The comparison accepts a function with an intersection result and the
intersection of the two functions with the same input and separate results in both directions. -/
private theorem function_intersection_result
    {input first second : WellFormedType context.names} :
    Mutual (.callable input (.intersection first second))
      (.intersection (.callable input first) (.callable input second)) := by
  refine ⟨check_inter_intro
    (callable_below_callable
      (member_input_below (List.mem_singleton_self _) (check_inter_left check_refl)))
    (callable_below_callable
      (member_input_below (List.mem_singleton_self _) (check_inter_right check_refl))), ?_⟩
  apply two_callable_below
  exact check_trans (check_inter_intro check_refl (check_inter_intro check_refl check_object_top))
    (selected_input_below_coverage [(input, first), (input, second)]
      [(input, first), (input, second)] (.intersection first second)
      (mem_subsequences.mpr (List.Sublist.refl _)) (by simp)
      (check_inter_intro (check_inter_left check_refl) (check_inter_right (check_inter_left check_refl))))

/-- Empty-input function requirements and BoundMethod compare in both directions. -/
private theorem function_empty_input
    {result : WellFormedType context.names} :
    Mutual (.callable .bottom result) context.boundMethodType := by
  refine ⟨?_, checkSubtypeBool_of_callable_coverage fun intersection member => ?_⟩
  · apply (checkSubtypeBool_classLiteral_iff context _ boundMethodClass context.valid.boundMethodKnown true).mpr
    intro intersection member
    rw [splitIntoIntersections_callable] at member
    cases List.mem_singleton.mp member
    exact ClassIntersection.boundMethod_includesSelf context
  · have answer := ((mem_splitIntoIntersections_classLiteral boundMethodClass
      context.valid.boundMethodKnown true intersection).mp member).2.1
    exact ⟨fun name _ => intersection.classIntersection.boundMethod_includesClass answer name, check_bottom⟩

/-- Every equation derivation compares its two operands in both directions.
Global transitivity permits equation intermediates with arbitrary function nesting. -/
private theorem equation_mutual
    {source target : WellFormedType context.names} (equation : TypeEquivalence context source target) :
    Mutual source target := by
  induction equation with
  | refl => exact ⟨check_refl, check_refl⟩
  | symm _ inductionHypothesis => exact ⟨inductionHypothesis.2, inductionHypothesis.1⟩
  | trans _ _ firstInduction secondInduction =>
      exact ⟨check_trans firstInduction.1 secondInduction.1,
        check_trans secondInduction.2 firstInduction.2⟩
  | union _ _ left right =>
      exact ⟨check_union_elim (check_union_left left.1) (check_union_right right.1),
        check_union_elim (check_union_left left.2) (check_union_right right.2)⟩
  | intersection _ _ left right =>
      exact ⟨check_inter_intro (check_inter_left left.1) (check_inter_right right.1),
        check_inter_intro (check_inter_left left.2) (check_inter_right right.2)⟩
  | callable _ _ input result =>
      exact ⟨callable_monotone input.2 result.1, callable_monotone input.1 result.2⟩
  | unionCommutative =>
      exact ⟨check_union_elim (check_union_right check_refl) (check_union_left check_refl),
        check_union_elim (check_union_right check_refl) (check_union_left check_refl)⟩
  | intersectionCommutative =>
      exact ⟨check_inter_intro (check_inter_right check_refl) (check_inter_left check_refl),
        check_inter_intro (check_inter_right check_refl) (check_inter_left check_refl)⟩
  | unionAssociative =>
      exact ⟨check_union_elim
          (check_union_elim (check_union_left check_refl) (check_union_right (check_union_left check_refl)))
          (check_union_right (check_union_right check_refl)),
        check_union_elim (check_union_left (check_union_left check_refl))
          (check_union_elim (check_union_left (check_union_right check_refl)) (check_union_right check_refl))⟩
  | intersectionAssociative =>
      exact ⟨check_inter_intro (check_inter_left (check_inter_left check_refl))
          (check_inter_intro (check_inter_left (check_inter_right check_refl)) (check_inter_right check_refl)),
        check_inter_intro
          (check_inter_intro (check_inter_left check_refl) (check_inter_right (check_inter_left check_refl)))
          (check_inter_right (check_inter_right check_refl))⟩
  | unionAbsorption => exact ⟨check_union_elim check_refl (check_inter_left check_refl), check_union_left check_refl⟩
  | intersectionAbsorption =>
      exact ⟨check_inter_left check_refl, check_inter_intro check_refl (check_union_left check_refl)⟩
  | unionBottom => exact ⟨check_union_elim check_refl check_bottom, check_union_left check_refl⟩
  | intersectionObject => exact ⟨check_inter_left check_refl, check_inter_intro check_refl check_object_top⟩
  | intersectionDistributes =>
      exact ⟨check_distributes, check_union_elim
        (check_inter_intro (check_inter_left check_refl) (check_union_left (check_inter_right check_refl)))
        (check_inter_intro (check_inter_left check_refl) (check_union_right (check_inter_right check_refl)))⟩
  | functionUnionInput => exact function_union_input
  | functionIntersectionResult => exact function_intersection_result
  | functionEmptyInput => exact function_empty_input
  | classComplement known => exact class_complement known
  | classContradiction known => exact class_contradiction known
  | inheritance known inherited => exact class_inheritance known inherited
  | sealedExclusion sealed known outside => exact sealed_exclusion sealed known outside
  | @incompatibleClasses classes known failed => exact incompatible_classes classes known failed

end EquationGenerators

end ComparisonProof

/-- Algebraic subtype derivations are accepted by the Boolean comparison. -/
theorem checkSubtypeBool_of_subtype (context : ValidatedClassContext)
    (source target : WellFormedType context.names)
    (included : TypeEquivalence.Subtype context source.raw target.raw) :
    checkSubtypeBool context source target = true :=
  check_trans (check_union_left check_refl) (equation_mutual included.equation).1

end FwPython.Static.Subtyping

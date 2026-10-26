import FwPython.Gradual.Statics

/-! # Gradual `isInstance` branch refinement

This module defines the source and checked branch type policy for
`if isInstance(x, C)`. The policy removes object-level `any` uncertainty
before adding the runtime class fact produced by the test. -/

/-- Compute the definite object-level facet guaranteed by the whole type before
    adding a runtime `isInstance` fact.

    A union survives only when both sides have definite facets; for example,
    `A | any` has no guaranteed non-`any` base and returns `none`. An
    intersection keeps every definite facet that remains. A callable survives as
    one object-level fact, without inspecting its parameter or return
    annotations. -/
def isInstanceRefinementBase? : GTy → Option GTy
  | .any => none
  | .class_ C => some (.class_ C)
  | .callable P R => some (.callable P R)
  | .union L R =>
      match isInstanceRefinementBase? L, isInstanceRefinementBase? R with
      | some L', some R' => some (.union L' R')
      | _, _ => none
  | .intersection L R =>
      match isInstanceRefinementBase? L, isInstanceRefinementBase? R with
      | none, none => none
      | some L', none => some L'
      | none, some R' => some R'
      | some L', some R' => some (.intersection L' R')
  | .bottom => some .bottom
  | .negClass C => some (.negClass C)

/-- Branch refinement parametrized by the runtime fact `extra` the test
    contributes. The surviving object-level facet is intersected with `extra`;
    when no facet survives, `extra` stands alone. -/
def isInstanceRefinementWith (T extra : GTy) : GTy :=
  match isInstanceRefinementBase? T with
  | none => extra
  | some U => .intersection U extra

/-- Positive `isInstance` branch refinement. The branch adds the runtime class
    fact to the surviving object facet, or uses only the runtime fact when no
    definite facet remains. -/
def isInstanceThenRefinement (T : GTy) (C : Identifier) : GTy :=
  isInstanceRefinementWith T (.class_ C)

/-- Negative `isInstance` branch refinement. The branch adds the runtime
    class-exclusion fact to the surviving object facet, or uses only the
    runtime fact when no definite facet remains. -/
def isInstanceElseRefinement (T : GTy) (C : Identifier) : GTy :=
  isInstanceRefinementWith T (.negClass C)

section

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

private theorem gradualSubtype_to_any (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G : GTy)
    (valid : WellFormedTy (eraseClassTable gct) (upperBound G)) :
    GradualSubtype gct structural G .any := by
  unfold GradualSubtype
  simp [upperBound, staticTop]
  exact IsSubtype.objectTop valid

private theorem gradualSubtype_intersection_intro
    (hG : GradualSubtype gct structural G H)
    (hK : GradualSubtype gct structural G K) :
    GradualSubtype gct structural G (.intersection H K) := by
  simpa [GradualSubtype, upperBound] using
    IsSubtype.interIntro hG hK

private theorem gradualSubtype_of_isInstanceRefinementBase?_none
    (hany : GradualSubtype gct structural F .any)
    (hbase : isInstanceRefinementBase? T = none)
    (valid : WellFormedTy (eraseClassTable gct) (upperBound T)) :
    GradualSubtype gct structural F T := by
  induction T with
  | any => exact hany
  | class_ _ | callable _ _ | bottom | negClass _ =>
      simp [isInstanceRefinementBase?] at hbase
  | union L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      all_goals first
      | exact gradualSubtype_trans (ihL hL valid.union_left)
          (gradualSubtype_union_left gct structural L R valid.union_left valid.union_right)
      | exact gradualSubtype_trans (ihR hR valid.union_right)
          (gradualSubtype_union_right gct structural L R valid.union_left valid.union_right)
  | intersection L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      exact gradualSubtype_intersection_intro (ihL hL valid.intersection_left) (ihR hR valid.intersection_right)

/-- The surviving facet is a supertype of the original type: removing
    object-level `any` facts does not add any runtime requirement. -/
private theorem isInstanceRefinementBase?_subtype
    (hbase : isInstanceRefinementBase? T = some U)
    (valid : WellFormedTy (eraseClassTable gct) (upperBound T)) :
    GradualSubtype gct structural T U := by
  induction T generalizing U with
  | any => simp [isInstanceRefinementBase?] at hbase
  | class_ _ | callable _ _ | bottom | negClass _ =>
      simp [isInstanceRefinementBase?] at hbase
      cases hbase; exact IsSubtype.refl valid
  | union L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      cases hbase; exact gradualSubtype_union_mono (ihL hL valid.union_left) (ihR hR valid.union_right)
  | intersection L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      · cases hbase
        exact gradualSubtype_trans
          (gradualSubtype_intersection_right gct structural L R valid.intersection_left valid.intersection_right)
          (ihR hR valid.intersection_right)
      · cases hbase
        exact gradualSubtype_trans
          (gradualSubtype_intersection_left gct structural L R valid.intersection_left valid.intersection_right)
          (ihL hL valid.intersection_left)
      · cases hbase
        exact gradualSubtype_intersection_intro
          (gradualSubtype_trans
            (gradualSubtype_intersection_left gct structural L R valid.intersection_left valid.intersection_right)
            (ihL hL valid.intersection_left))
          (gradualSubtype_trans
            (gradualSubtype_intersection_right gct structural L R valid.intersection_left valid.intersection_right)
            (ihR hR valid.intersection_right))

private theorem isInstanceRefinementBase?_self_subtype
    (hbase : isInstanceRefinementBase? T = some U)
    (valid : WellFormedTy (eraseClassTable gct) (upperBound T)) :
    GradualSubtype gct structural U T := by
  induction T generalizing U with
  | any => simp [isInstanceRefinementBase?] at hbase
  | class_ _ | callable _ _ | bottom | negClass _ =>
      simp [isInstanceRefinementBase?] at hbase
      cases hbase; exact IsSubtype.refl valid
  | union L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      cases hbase; exact gradualSubtype_union_mono (ihL hL valid.union_left) (ihR hR valid.union_right)
  | intersection L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      · cases hbase
        exact gradualSubtype_intersection_intro
          (gradualSubtype_of_isInstanceRefinementBase?_none
            (gradualSubtype_to_any gct structural _ (ihR hR valid.intersection_right).sourceWellFormed)
            hL valid.intersection_left)
          (ihR hR valid.intersection_right)
      · cases hbase
        exact gradualSubtype_intersection_intro (ihL hL valid.intersection_left)
          (gradualSubtype_of_isInstanceRefinementBase?_none
            (gradualSubtype_to_any gct structural _ (ihL hL valid.intersection_left).sourceWellFormed)
            hR valid.intersection_right)
      · cases hbase
        exact gradualSubtype_intersection_mono (ihL hL valid.intersection_left) (ihR hR valid.intersection_right)

/-- The refined type retains the original upper-bound requirement. -/
private theorem isInstanceRefinementWith_subtype_self
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T extra : GTy)
    (validT : WellFormedTy (eraseClassTable gct) (upperBound T))
    (validExtra : WellFormedTy (eraseClassTable gct) (upperBound extra)) :
    GradualSubtype gct structural (isInstanceRefinementWith T extra) T := by
  unfold isInstanceRefinementWith
  cases hbase : isInstanceRefinementBase? T with
  | none =>
      exact gradualSubtype_of_isInstanceRefinementBase?_none
        (gradualSubtype_to_any gct structural extra validExtra) hbase validT
  | some U =>
      have included := isInstanceRefinementBase?_self_subtype (structural := structural) hbase validT
      exact gradualSubtype_trans
        (gradualSubtype_intersection_left gct structural U extra included.sourceWellFormed validExtra) included

/-- A positive refinement retains the valid original annotation. -/
theorem isInstanceThenRefinement_subtype_self
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T : GTy) (C : Identifier)
    (validT : WellFormedGTy gct T)
    (validC : WellFormedGTy gct (.class_ C)) :
    GradualSubtype gct structural (isInstanceThenRefinement T C) T :=
  isInstanceRefinementWith_subtype_self gct structural T (.class_ C)
    (validT.boundsNamesKnown structural).2 (validC.boundsNamesKnown structural).2

/-- A negative refinement retains the valid original annotation. -/
theorem isInstanceElseRefinement_subtype_self
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T : GTy) (C : Identifier)
    (validT : WellFormedGTy gct T)
    (validC : WellFormedGTy gct (.class_ C)) :
    GradualSubtype gct structural (isInstanceElseRefinement T C) T :=
  isInstanceRefinementWith_subtype_self gct structural T (.negClass C)
    (validT.boundsNamesKnown structural).2 (validC.boundsNamesKnown structural).2.neg_of_class

/-- A refinement retains the additional valid requirement. -/
private theorem isInstanceRefinementWith_subtype_extra
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T extra : GTy)
    (validT : WellFormedTy (eraseClassTable gct) (upperBound T))
    (validExtra : WellFormedTy (eraseClassTable gct) (upperBound extra)) :
    GradualSubtype gct structural (isInstanceRefinementWith T extra) extra := by
  unfold isInstanceRefinementWith
  cases hbase : isInstanceRefinementBase? T with
  | none => exact IsSubtype.refl validExtra
  | some U =>
      exact gradualSubtype_intersection_right gct structural U extra
        (isInstanceRefinementBase?_subtype (structural := structural) hbase validT).targetWellFormed validExtra

/-- Refinement preserves upper-bound inclusion when the added requirement is valid. -/
private theorem isInstanceRefinementWith_mono
    (hsub : GradualSubtype gct structural sourceTy checkedTy)
    (validExtra : WellFormedTy (eraseClassTable gct) (upperBound extra)) :
    GradualSubtype gct structural
      (isInstanceRefinementWith sourceTy extra)
      (isInstanceRefinementWith checkedTy extra) := by
  unfold isInstanceRefinementWith
  cases hchecked : isInstanceRefinementBase? checkedTy with
  | none =>
      exact isInstanceRefinementWith_subtype_extra gct structural sourceTy extra hsub.sourceWellFormed validExtra
  | some checkedBase =>
      exact gradualSubtype_intersection_intro
        (gradualSubtype_trans
          (isInstanceRefinementWith_subtype_self gct structural sourceTy extra hsub.sourceWellFormed validExtra)
          (gradualSubtype_trans hsub
            (isInstanceRefinementBase?_subtype hchecked hsub.targetWellFormed)))
        (isInstanceRefinementWith_subtype_extra gct structural sourceTy extra hsub.sourceWellFormed validExtra)

/-- Positive refinement preserves inclusion for a known class. -/
theorem isInstanceThenRefinement_mono
    (hsub : GradualSubtype gct structural sourceTy checkedTy)
    (validC : WellFormedGTy gct (.class_ C)) :
    GradualSubtype gct structural
      (isInstanceThenRefinement sourceTy C)
      (isInstanceThenRefinement checkedTy C) :=
  isInstanceRefinementWith_mono hsub (validC.boundsNamesKnown structural).2

/-- Negative refinement preserves inclusion for a known class. -/
theorem isInstanceElseRefinement_mono
    (hsub : GradualSubtype gct structural sourceTy checkedTy)
    (validC : WellFormedGTy gct (.class_ C)) :
    GradualSubtype gct structural
      (isInstanceElseRefinement sourceTy C)
      (isInstanceElseRefinement checkedTy C) :=
  isInstanceRefinementWith_mono hsub (validC.boundsNamesKnown structural).2.neg_of_class

end

theorem wellFormedGTy_isInstanceRefinementBase?
    (hbase : isInstanceRefinementBase? T = some U)
    (hwf : WellFormedGTy gct T) :
    WellFormedGTy gct U := by
  induction T generalizing U with
  | any => simp [isInstanceRefinementBase?] at hbase
  | class_ _ | callable _ _ | bottom | negClass _ =>
      simp [isInstanceRefinementBase?] at hbase
      cases hbase; exact hwf
  | union L R ihL ihR =>
      cases hwf with | union hwfL hwfR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      cases hbase; exact .union (ihL hL hwfL) (ihR hR hwfR)
  | intersection L R ihL ihR =>
      cases hwf with | intersection hwfL hwfR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hbase
      · cases hbase; exact ihR hR hwfR
      · cases hbase; exact ihL hL hwfL
      · cases hbase; exact .intersection (ihL hL hwfL) (ihR hR hwfR)

theorem wellFormedGTy_isInstanceRefinementWith
    (hwf : WellFormedGTy gct T)
    (hextra : WellFormedGTy gct extra) :
    WellFormedGTy gct (isInstanceRefinementWith T extra) := by
  unfold isInstanceRefinementWith
  cases hbase : isInstanceRefinementBase? T with
  | none => exact hextra
  | some U =>
      exact .intersection (wellFormedGTy_isInstanceRefinementBase? hbase hwf) hextra

theorem wellFormedGTy_isInstanceThenRefinement
    (hwf : WellFormedGTy gct T)
    (hclass : WellFormedGTy gct (.class_ C)) :
    WellFormedGTy gct (isInstanceThenRefinement T C) :=
  wellFormedGTy_isInstanceRefinementWith hwf hclass

/-- A valid annotation and a declared test class give a valid negative branch refinement. -/
theorem wellFormedGTy_isInstanceElseRefinement
    (hwf : WellFormedGTy gct T)
    (hclass : WellFormedGTy gct (.class_ C)) :
    WellFormedGTy gct (isInstanceElseRefinement T C) :=
  wellFormedGTy_isInstanceRefinementWith hwf (by
    cases hclass with
    | class_ lookup computed => exact .negClass lookup computed)

@[simp] theorem isInstanceRefinementBase?_embedTy (T : Ty) :
    isInstanceRefinementBase? (embedTy T) = some (embedTy T) := by
  induction T with
  | class_ C => rfl
  | negClass C => rfl
  | callable P R ihP ihR => rfl
  | union L R ihL ihR =>
      simp [embedTy, isInstanceRefinementBase?, ihL, ihR]
  | intersection L R ihL ihR =>
      simp [embedTy, isInstanceRefinementBase?, ihL, ihR]
  | bottom => rfl

theorem isInstanceRefinementWith_embedTy (T : Ty) (extra : GTy) :
    isInstanceRefinementWith (embedTy T) extra =
      .intersection (embedTy T) extra := by
  simp [isInstanceRefinementWith]

theorem isInstanceThenRefinement_embedTy (T : Ty) (C : Identifier) :
    isInstanceThenRefinement (embedTy T) C =
      .intersection (embedTy T) (.class_ C) :=
  isInstanceRefinementWith_embedTy T (.class_ C)

theorem isInstanceElseRefinement_embedTy (T : Ty) (C : Identifier) :
    isInstanceElseRefinement (embedTy T) C =
      .intersection (embedTy T) (.negClass C) :=
  isInstanceRefinementWith_embedTy T (.negClass C)

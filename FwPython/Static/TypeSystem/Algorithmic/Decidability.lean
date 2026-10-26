import FwPython.Static.TypeSystem.Algorithmic.Correctness

/-! ## Algorithmic checking and targeted decidability -/

open FwPython.Static.Subtyping

variable {ct : ClassTable}

/-- Validate the requested annotation once, then compare it with valid inferred candidates.
The class-table evidence supplies valid method signatures and the structural
table used by subtype checks. -/
def checkHasType? (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) (e : Expr) (T : Ty) : Bool :=
  match typeNamesKnown_decidable (ct.map ClassDecl.name) T with
  | isFalse _ => false
  | isTrue known =>
      (inferBasis hwfct Γ hΓwf e).types.any fun source =>
        letI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy source ⟨T, known⟩
        decide (IsSubtype hwfct.toWellFormedClassHierarchy source.raw T)

/-- The executable checker accepts exactly the declaratively typed expressions. -/
theorem checkHasType?_iff_hasType (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    checkHasType? hwfct hΓwf e T = true ↔ HasType hwfct.toWellFormedClassHierarchy Γ e T := by
  unfold checkHasType?
  cases typeNamesKnown_decidable (ct.map ClassDecl.name) T with
  | isFalse unknown =>
      refine ⟨(fun checked => by cases checked), fun typed => ?_⟩
      exact (unknown (hasType_wellFormed hwfct hΓwf typed)).elim
  | isTrue known =>
      constructor
      · intro checked
        obtain ⟨source, listed, accepted⟩ := List.any_eq_true.mp checked
        haveI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy source ⟨T, known⟩
        have included : IsSubtype hwfct.toWellFormedClassHierarchy source.raw T := by
          by_cases included : IsSubtype hwfct.toWellFormedClassHierarchy source.raw T
          · exact included
          · simp [included] at accepted
        exact .sub ((inferBasis hwfct Γ hΓwf e).types_sound listed)
          included
      · intro typed
        obtain ⟨source, listed, included⟩ := inferBasis_complete hwfct hΓwf typed
        apply List.any_eq_true.mpr
        refine ⟨source, listed, ?_⟩
        haveI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy source ⟨T, known⟩
        simp [included]

/-- Decide expression typing with a valid class table and variable environment. -/
def hasType_decidable_wfEnv
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    Decidable (HasType hwfct.toWellFormedClassHierarchy Γ e T) := by
  by_cases hcheck : checkHasType? hwfct hΓwf e T = true
  · exact isTrue ((checkHasType?_iff_hasType hwfct hΓwf).1 hcheck)
  · exact isFalse fun htype => hcheck ((checkHasType?_iff_hasType hwfct hΓwf).2 htype)

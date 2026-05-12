import FwPython.Static.TypeSystem.Algorithmic.Correctness

/-! ## Algorithmic checking and targeted decidability -/

def checkHasType?
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (e : Expr) (T : Ty) : Bool :=
  match wellFormedTy_decidable hwfct T with
  | isFalse _ => false
  | isTrue hwfT =>
      (inferBasis hwfct hΓwf e).attach.any fun entry =>
        let _ : Decidable (IsSubtype ct entry.1 T) :=
          isSubtype_decidable hwfct
            (inferBasis_all_wellFormed hwfct hΓwf entry.2) hwfT
        decide (IsSubtype ct entry.1 T)

theorem checkHasType?_iff_hasType
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    checkHasType? hwfct hΓwf e T = true ↔ HasType ct Γ e T := by
  unfold checkHasType?
  cases hdecT : wellFormedTy_decidable hwfct T with
  | isFalse hnot =>
      refine ⟨fun hcheck => by simp at hcheck, fun htype => ?_⟩
      exact (hnot (hasType_wellFormed hwfct hΓwf htype)).elim
  | isTrue hwfT =>
      constructor
      · intro hcheck
        rw [List.any_eq_true] at hcheck
        rcases hcheck with ⟨entry, _, hpred⟩
        let _ : Decidable (IsSubtype ct entry.1 T) :=
          isSubtype_decidable hwfct
            (inferBasis_all_wellFormed hwfct hΓwf entry.2) hwfT
        have hsub : IsSubtype ct entry.1 T := by
          by_cases hsub : IsSubtype ct entry.1 T
          · exact hsub
          · simp [hsub] at hpred
        exact .sub (inferBasis_sound hwfct hΓwf entry.2) hsub hwfT
      · intro htype
        obtain ⟨S, hS, hsub⟩ := inferBasis_complete hwfct hΓwf htype
        rw [List.any_eq_true]
        refine ⟨⟨S, hS⟩, by simp, ?_⟩
        let _ : Decidable (IsSubtype ct S T) :=
          isSubtype_decidable hwfct
            (inferBasis_all_wellFormed hwfct hΓwf hS) hwfT
        simp [hsub]

def hasType_decidable_wfEnv
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ) :
    Decidable (HasType ct Γ e T) := by
  by_cases hcheck : checkHasType? hwfct hΓwf e T = true
  · exact isTrue ((checkHasType?_iff_hasType hwfct hΓwf).1 hcheck)
  · exact isFalse fun htype => hcheck ((checkHasType?_iff_hasType hwfct hΓwf).2 htype)

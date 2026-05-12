import FwPython.Static.TypeSystem.Algorithmic.Infer

/-! ## Algorithmic completeness -/

private theorem inferBasis_complete_leaf
    {ct : ClassTable} {Γ : TyEnv} {e : Expr} {T : Ty}
    (hwfct : WellFormedClassTable ct) (hΓwf : WellFormedTyEnv ct Γ)
    (heq : inferBasis hwfct hΓwf e = saturateBasis [T]) :
    ∃ S, S ∈ inferBasis hwfct hΓwf e ∧ IsSubtype ct S T :=
  ⟨T, heq ▸ saturateBasis_mem_of_mem (List.mem_singleton.mpr rfl), .refl⟩

theorem inferBasis_complete
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h : HasType ct Γ e T) :
    ∃ S, S ∈ inferBasis hwfct hΓwf e ∧ IsSubtype ct S T := by
  revert hΓwf
  induction h with
  | sub _ hsub _ ih =>
      intro hΓwf
      obtain ⟨S, hS, hsub'⟩ := ih hwfct hΓwf
      exact ⟨S, hS, .trans hsub' hsub⟩
  | var hlook =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf (inferBasis_var_eq hwfct hΓwf hlook)
  | constNone =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf (inferBasis_constNone_eq hwfct hΓwf)
  | constTrue =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf (inferBasis_constTrue_eq hwfct hΓwf)
  | constFalse =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf (inferBasis_constFalse_eq hwfct hΓwf)
  | new hfind hbool hnone hbm =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf
        (inferBasis_new_eq hwfct hΓwf hfind hbool hnone hbm)
  | isInstance hlook hfind =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf
        (inferBasis_isInstance_eq hwfct hΓwf hlook hfind)
  | attrAccess _ hfmt ih =>
      intro hΓwf
      obtain ⟨Sb, hSb, hsub⟩ := ih hwfct hΓwf
      exact ⟨_, inferBasis_attrAccess_step hwfct hΓwf hSb hsub hfmt, .refl⟩
  | attrAccessUnion _ hfmt1 hfmt2 ih =>
      intro hΓwf
      obtain ⟨Sb, hSb, hsub⟩ := ih hwfct hΓwf
      exact ⟨_, inferBasis_attrAccessUnion_step hwfct hΓwf hSb hsub hfmt1 hfmt2, .refl⟩
  | call _ _ hsubArg ihCallee ihArg =>
      intro hΓwf
      obtain ⟨Sc, hSc, hsubC⟩ := ihCallee hwfct hΓwf
      obtain ⟨Sa, hSa, hsubA⟩ := ihArg hwfct hΓwf
      exact inferBasis_call_step hwfct hΓwf hSc hSa
        hsubC (.trans hsubA hsubArg)
  | cond _ hbool _ _ ihCond ihThen ihElse =>
      intro hΓwf
      obtain ⟨Sc, hSc, hsubC⟩ := ihCond hwfct hΓwf
      obtain ⟨St, hSt, hsubT⟩ := ihThen hwfct hΓwf
      obtain ⟨Se, hSe, hsubE⟩ := ihElse hwfct hΓwf
      exact ⟨_,
        inferBasis_cond_ordinary_step hwfct hΓwf hSc (.trans hsubC hbool) hSt hSe,
        .unionElim (.trans hsubT (.unionLeft .refl))
          (.trans hsubE (.unionRight .refl))⟩
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
      intro hΓwf
      let hmro := (hwfct.allMrosExist _ _ hfind).hmro
      obtain ⟨St, hSt, hsubT⟩ :=
        ihThen hwfct (wellFormedTyEnv_update_class hΓwf hlook hfind hmro)
      obtain ⟨Se, hSe, hsubE⟩ :=
        ihElse hwfct (wellFormedTyEnv_update_negClass hΓwf hlook hfind hmro)
      exact ⟨_,
        inferBasis_cond_isInstance_specialized_step hwfct hΓwf hlook hfind St Se hSt hSe,
        .unionElim (.trans hsubT (.unionLeft .refl))
          (.trans hsubE (.unionRight .refl))⟩
  | interIntro _ _ ih1 ih2 =>
      intro hΓwf
      obtain ⟨S1, hS1, hsub1⟩ := ih1 hwfct hΓwf
      obtain ⟨S2, hS2, hsub2⟩ := ih2 hwfct hΓwf
      obtain ⟨U, hU, hUsub⟩ := inferBasis_intersection_step hwfct hΓwf hS1 hS2
      exact ⟨U, hU, .trans hUsub
        (.interIntro (.trans (.interLeft .refl) hsub1)
          (.trans (.interRight .refl) hsub2))⟩

theorem inferBasis_bool_candidate
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcond : HasType ct Γ condExpr testTy)
    (hbool : IsSubtype ct testTy (.class_ boolClass)) :
    ∃ S, S ∈ inferBasis hwfct hΓwf condExpr ∧ IsSubtype ct S (.class_ boolClass) := by
  obtain ⟨S, hS, hsub⟩ := inferBasis_complete hwfct hΓwf hcond
  exact ⟨S, hS, .trans hsub hbool⟩

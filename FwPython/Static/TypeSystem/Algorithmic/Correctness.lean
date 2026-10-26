import FwPython.Static.TypeSystem.Algorithmic.Infer

open FwPython.Static.Subtyping

/-! ## Algorithmic completeness -/

variable {ct : ClassTable}

/-- A singleton candidate list contains a valid package below its own annotation. -/
private theorem inferBasis_complete_leaf
    (hwfct : WellTypedClassHierarchy ct) (hΓwf : WellFormedTyEnv ct Γ)
    (type : WellFormedType (ct.map ClassDecl.name))
    (heq : (inferBasis hwfct Γ hΓwf e).types = [type]) :
    ∃ candidate ∈ (inferBasis hwfct Γ hΓwf e).types,
      IsSubtype hwfct.toWellFormedClassHierarchy candidate.raw type.raw :=
  ⟨type, heq ▸ List.mem_singleton.mpr rfl, .refl type.namesKnown⟩

/-- Every declarative type contains a validated candidate produced by inference. -/
theorem inferBasis_complete
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h : HasType hwfct.toWellFormedClassHierarchy Γ e T) :
    ∃ S ∈ (inferBasis hwfct Γ hΓwf e).types,
      IsSubtype hwfct.toWellFormedClassHierarchy S.raw T := by
  revert hΓwf
  induction h with
  | sub _ hsub ih =>
      intro hΓwf
      obtain ⟨S, hS, hsub'⟩ := ih hΓwf
      exact ⟨S, hS, .trans hsub' hsub⟩
  | var hlook =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _ (inferBasis_var_eq hwfct hΓwf hlook)
  | constNone =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _ (inferBasis_constNone_eq hwfct hΓwf)
  | constTrue =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _ (inferBasis_constTrue_eq hwfct hΓwf)
  | constFalse =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _ (inferBasis_constFalse_eq hwfct hΓwf)
  | new hfind hbool hnone hbm =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _
        (inferBasis_new_eq hwfct hΓwf hfind hbool hnone hbm)
  | isInstance hlook hfind =>
      intro hΓwf
      exact inferBasis_complete_leaf hwfct hΓwf _
        (inferBasis_isInstance_eq hwfct hΓwf hlook hfind)
  | attrAccess _ hfmt ih =>
      intro hΓwf
      obtain ⟨Sb, hSb, hsub⟩ := ih hΓwf
      obtain ⟨result, member, equal⟩ := inferBasis_attrAccess_step hwfct hΓwf hSb hsub hfmt
      exact ⟨result, member, equal ▸ .refl result.namesKnown⟩
  | attrAccessUnion _ hfmt1 hfmt2 ih =>
      intro hΓwf
      obtain ⟨Sb, hSb, hsub⟩ := ih hΓwf
      obtain ⟨result, member, equal⟩ := inferBasis_attrAccessUnion_step hwfct hΓwf hSb hsub hfmt1 hfmt2
      exact ⟨result, member, equal ▸ .refl result.namesKnown⟩
  | call _ _ hsubArg ihCallee ihArg =>
      intro hΓwf
      obtain ⟨Sc, hSc, hsubC⟩ := ihCallee hΓwf
      obtain ⟨Sa, hSa, hsubA⟩ := ihArg hΓwf
      exact inferBasis_call_step hwfct hΓwf hSc hSa
        hsubC (.trans hsubA hsubArg)
  | cond _ hbool _ _ ihCond ihThen ihElse =>
      intro hΓwf
      obtain ⟨Sc, hSc, hsubC⟩ := ihCond hΓwf
      obtain ⟨St, hSt, hsubT⟩ := ihThen hΓwf
      obtain ⟨Se, hSe, hsubE⟩ := ihElse hΓwf
      exact ⟨_,
        inferBasis_cond_ordinary_step hwfct hΓwf hSc (.trans hsubC hbool) hSt hSe,
        .unionMono hsubT hsubE⟩
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
      intro hΓwf
      obtain ⟨St, hSt, hsubT⟩ :=
        ihThen (wellFormedTyEnv_update_class hΓwf hlook hfind)
      obtain ⟨Se, hSe, hsubE⟩ :=
        ihElse (wellFormedTyEnv_update_negClass hΓwf hlook hfind)
      exact ⟨_,
        inferBasis_cond_isInstance_specialized_step hwfct hΓwf hlook hfind St Se hSt hSe,
        .unionMono hsubT hsubE⟩
  | interIntro _ _ ih1 ih2 =>
      intro hΓwf
      obtain ⟨S1, hS1, hsub1⟩ := ih1 hΓwf
      obtain ⟨S2, hS2, hsub2⟩ := ih2 hΓwf
      obtain ⟨U, hU, hUsub⟩ := InferredBasis.intersection_cover _ hS1 hS2
      exact ⟨U, hU, .trans hUsub
        (.interMono hsub1 hsub2)⟩

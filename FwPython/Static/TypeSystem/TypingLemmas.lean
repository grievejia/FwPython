import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.WellFormedness
import FwPython.Static.Subtyping.Lattice

/-! ## Theorem support for the surface typing core. -/

theorem WellFormedTy.callable_inv :
    WellFormedTy ct (.callable P R) → WellFormedTy ct P ∧ WellFormedTy ct R
  | .callable hwfP hwfR => ⟨hwfP, hwfR⟩

theorem WellFormedTy.union_inv :
    WellFormedTy ct (.union T U) → WellFormedTy ct T ∧ WellFormedTy ct U
  | .union hwfT hwfU => ⟨hwfT, hwfU⟩

theorem WellFormedTy.intersection_inv :
    WellFormedTy ct (.intersection T U) → WellFormedTy ct T ∧ WellFormedTy ct U
  | .intersection hwfT hwfU => ⟨hwfT, hwfU⟩

theorem hasType_wellFormed
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h : HasType ct Γ e T) :
    WellFormedTy ct T := by
  induction h with
  | sub _ _ hwfT _ =>
      exact hwfT
  | var hlook =>
      exact hΓwf _ _ hlook
  | constNone =>
      exact wellFormed_none_type hwfct
  | constTrue | constFalse | isInstance _ _ =>
      exact wellFormed_bool_type hwfct
  | new hfind _ _ _ =>
      exact .class_ hfind (hwfct.allMrosExist _ _ hfind).hmro
  | attrAccess _ hfmt =>
      exact (findMethodType_wellFormed hwfct hfmt).elim .callable
  | attrAccessUnion _ hfmt1 hfmt2 =>
      obtain ⟨hP1, hR1⟩ := findMethodType_wellFormed hwfct hfmt1
      obtain ⟨hP2, hR2⟩ := findMethodType_wellFormed hwfct hfmt2
      exact .union (.callable hP1 hR1) (.callable hP2 hR2)
  | call _ _ _ ihCallee _ =>
      exact (WellFormedTy.callable_inv (ihCallee hwfct hΓwf)).2
  | cond _ _ _ _ _ ihThen ihElse =>
      exact .union (ihThen hwfct hΓwf) (ihElse hwfct hΓwf)
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
      have hmroC := (hwfct.allMrosExist _ _ hfind).hmro
      exact .union
        (ihThen hwfct (wellFormedTyEnv_update_class hΓwf hlook hfind hmroC))
        (ihElse hwfct (wellFormedTyEnv_update_negClass hΓwf hlook hfind hmroC))
  | interIntro _ _ ih1 ih2 =>
      exact .intersection (ih1 hwfct hΓwf) (ih2 hwfct hΓwf)

/-! ## Derived convenience lemmas. -/

theorem HasType.attrAccessInter
    (h1 : HasType ct Γ base (.class_ c1))
    (h2 : HasType ct Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType ct Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) :=
  .interIntro (.attrAccess h1 hfmt1) (.attrAccess h2 hfmt2)

theorem HasType.call_direct
    (hcallee : HasType ct Γ callee (.callable paramTy returnTy))
    (harg : HasType ct Γ arg paramTy) :
    HasType ct Γ (.call callee arg) returnTy :=
  .call hcallee harg .refl

theorem HasType.call_intersection
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee
      (.intersection (.callable p1 r1) (.callable p2 r2)))
    (harg1 : HasType ct Γ arg p1)
    (harg2 : HasType ct Γ arg p2) :
    HasType ct Γ (.call callee arg) (.intersection r1 r2) := by
  obtain ⟨hwf1, hwf2⟩ :=
    WellFormedTy.intersection_inv (hasType_wellFormed hwfct hΓwf hcallee)
  exact .interIntro
    (HasType.call_direct (.sub hcallee (.interLeft .refl) hwf1) harg1)
    (HasType.call_direct (.sub hcallee (.interRight .refl) hwf2) harg2)

theorem HasType.call_union_summary
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType ct Γ arg (.intersection p1 p2)) :
    HasType ct Γ (.call callee arg) (.union r1 r2) := by
  obtain ⟨hwf1, hwf2⟩ :=
    WellFormedTy.union_inv (hasType_wellFormed hwfct hΓwf hcallee)
  obtain ⟨hwfP1, hwfR1⟩ := hwf1.callable_inv
  obtain ⟨hwfP2, hwfR2⟩ := hwf2.callable_inv
  exact HasType.call_direct
    (.sub hcallee subtype_union_callable_summary
      (.callable (.intersection hwfP1 hwfP2) (.union hwfR1 hwfR2)))
    harg

theorem HasType.condIsInstance_common
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType ct
      (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType ct
      (Γ.update x (.intersection T (.negClass C))) elseBr R)
    (hwfR : WellFormedTy ct R) :
    HasType ct Γ (.cond (.isInstance x C) thenBr elseBr) R :=
  .sub (.condIsInstance hlook hfind hthen helse) subtype_union_idem hwfR

private theorem hasType_strengthen_var_condIsInstance_aux
    {ct : ClassTable} {Γ : TyEnv} {x : Identifier} {S : Ty}
    {C : Identifier} {cls : Class} {thenBr elseBr : Expr} {thenTy elseTy : Ty}
    (hlookX : Γ.lookup x = some S)
    (hfindC : findClass ct C = some cls)
    (ihThen : ∀ {z : Identifier} {oldTy newTy : Ty},
      WellFormedClassTable ct →
      (Γ.update x (.intersection S (.class_ C))).lookup z = some oldTy →
      IsSubtype ct newTy oldTy →
      WellFormedTy ct newTy →
      WellFormedTyEnv ct (Γ.update x (.intersection S (.class_ C))) →
      HasType ct
        ((Γ.update x (.intersection S (.class_ C))).update z newTy)
        thenBr thenTy)
    (ihElse : ∀ {z : Identifier} {oldTy newTy : Ty},
      WellFormedClassTable ct →
      (Γ.update x (.intersection S (.negClass C))).lookup z = some oldTy →
      IsSubtype ct newTy oldTy →
      WellFormedTy ct newTy →
      WellFormedTyEnv ct (Γ.update x (.intersection S (.negClass C))) →
      HasType ct
        ((Γ.update x (.intersection S (.negClass C))).update z newTy)
        elseBr elseTy)
    {z : Identifier} {oldTy newTy : Ty}
    (hwf : WellFormedClassTable ct)
    (hlook : Γ.lookup z = some oldTy)
    (hsub : IsSubtype ct newTy oldTy)
    (hwfNew : WellFormedTy ct newTy)
    (hΓwf : WellFormedTyEnv ct Γ) :
    HasType ct (Γ.update z newTy)
      (.cond (.isInstance x C) thenBr elseBr)
      (.union thenTy elseTy) := by
  obtain ⟨cmro, hcmro⟩ := hwf.allMrosExist _ _ hfindC
  have hwfC : WellFormedTy ct (.class_ C) := .class_ hfindC hcmro
  have hwfNegC : WellFormedTy ct (.negClass C) := .negClass hfindC hcmro
  by_cases hxz : z = x
  · subst hxz
    have heq := Option.some.inj (hlook.symm.trans hlookX)
    subst heq
    have hThen :=
      @ihThen z (.intersection oldTy (.class_ C)) (.intersection newTy (.class_ C))
        hwf
        (tyEnv_update_lookup_eq (.intersection oldTy (.class_ C)) ⟨oldTy, hlook⟩)
        (.interIntro (.interLeft hsub) (.interRight .refl))
        (.intersection hwfNew hwfC)
        (wellFormedTyEnv_update_class hΓwf hlook hfindC hcmro)
    rw [tyEnv_update_shadow] at hThen
    have hElse :=
      @ihElse z (.intersection oldTy (.negClass C)) (.intersection newTy (.negClass C))
        hwf
        (tyEnv_update_lookup_eq (.intersection oldTy (.negClass C)) ⟨oldTy, hlook⟩)
        (.interIntro (.interLeft hsub) (.interRight .refl))
        (.intersection hwfNew hwfNegC)
        (wellFormedTyEnv_update_negClass hΓwf hlook hfindC hcmro)
    rw [tyEnv_update_shadow] at hElse
    exact .condIsInstance
      (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩)
      hfindC
      (by simpa [tyEnv_update_shadow] using hThen)
      (by simpa [tyEnv_update_shadow] using hElse)
  · have hne : x ≠ z := Ne.symm hxz
    have hThen :=
      @ihThen z oldTy newTy
        hwf
        ((tyEnv_update_lookup_ne _ hxz).trans hlook)
        hsub
        hwfNew
        (wellFormedTyEnv_update_class hΓwf hlookX hfindC hcmro)
    rw [tyEnv_update_commute hne] at hThen
    have hElse :=
      @ihElse z oldTy newTy
        hwf
        ((tyEnv_update_lookup_ne _ hxz).trans hlook)
        hsub
        hwfNew
        (wellFormedTyEnv_update_negClass hΓwf hlookX hfindC hcmro)
    rw [tyEnv_update_commute hne] at hElse
    have hlook' : (Γ.update z newTy).lookup x = some S :=
      (tyEnv_update_lookup_ne newTy hne).trans hlookX
    exact .condIsInstance hlook' hfindC hThen hElse

theorem hasType_strengthen_var
    (h : HasType ct Γ e T)
    (hwf : WellFormedClassTable ct)
    (hlook : Γ.lookup z = some oldTy)
    (hsub : IsSubtype ct newTy oldTy)
    (hwfNew : WellFormedTy ct newTy)
    (hΓwf : WellFormedTyEnv ct Γ) :
    HasType ct (Γ.update z newTy) e T := by
  induction h generalizing z oldTy newTy with
  | var hlook' =>
      rename_i y
      by_cases hyz : y = z
      · subst hyz
        have heq := Option.some.inj (hlook.symm.trans hlook')
        subst heq
        exact .sub (.var (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩)) hsub (hΓwf _ _ hlook)
      · exact .var ((tyEnv_update_lookup_ne newTy hyz).trans hlook')
  | sub _ hsub' hwfT ih =>
      exact .sub (ih hwf hlook hsub hwfNew hΓwf) hsub' hwfT
  | constNone =>
      exact .constNone
  | constTrue =>
      exact .constTrue
  | constFalse =>
      exact .constFalse
  | new hfind hne1 hne2 hne3 =>
      exact .new hfind hne1 hne2 hne3
  | attrAccess _ hfmt ih =>
      exact .attrAccess (ih hwf hlook hsub hwfNew hΓwf) hfmt
  | attrAccessUnion _ hfmt1 hfmt2 ih =>
      exact .attrAccessUnion (ih hwf hlook hsub hwfNew hΓwf) hfmt1 hfmt2
  | call _ _ hsubArg ihCallee ihArg =>
      exact .call
        (ihCallee hwf hlook hsub hwfNew hΓwf)
        (ihArg hwf hlook hsub hwfNew hΓwf)
        hsubArg
  | cond _ hbool _ _ ihCond ihThen ihElse =>
      exact .cond
        (ihCond hwf hlook hsub hwfNew hΓwf)
        hbool
        (ihThen hwf hlook hsub hwfNew hΓwf)
        (ihElse hwf hlook hsub hwfNew hΓwf)
  | isInstance hlook' hfind =>
      rename_i y
      by_cases hyz : y = z
      · subst hyz
        exact .isInstance (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩) hfind
      · exact .isInstance ((tyEnv_update_lookup_ne newTy hyz).trans hlook') hfind
  | condIsInstance hlookX hfindC _ _ ihThen ihElse =>
      exact hasType_strengthen_var_condIsInstance_aux
        hlookX hfindC ihThen ihElse hwf hlook hsub hwfNew hΓwf
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro
        (ih1 hwf hlook hsub hwfNew hΓwf)
        (ih2 hwf hlook hsub hwfNew hΓwf)

theorem hasType_strengthen_var_condIsInstance
    (h : HasType ct Γ (.cond (.isInstance x C) thenBr elseBr) T)
    (hwf : WellFormedClassTable ct)
    (hlook : Γ.lookup z = some oldTy)
    (hsub : IsSubtype ct newTy oldTy)
    (hwfNew : WellFormedTy ct newTy)
    (hΓwf : WellFormedTyEnv ct Γ) :
    HasType ct (Γ.update z newTy)
      (.cond (.isInstance x C) thenBr elseBr) T :=
  hasType_strengthen_var h hwf hlook hsub hwfNew hΓwf

theorem has_type_var_inv
    (h : HasType ct Γ (.var x) T) :
    ∃ T', Γ.lookup x = some T' ∧ IsSubtype ct T' T := by
  generalize he : Expr.var x = e at h
  induction h with
  | sub _ hsub _ ih =>
      obtain ⟨T', hlook, hsub'⟩ := ih he
      exact ⟨T', hlook, .trans hsub' hsub⟩
  | var hlook =>
      cases he
      exact ⟨_, hlook, .refl⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨T1, hlook1, hsub1⟩ := ih1 he
      obtain ⟨T2, hlook2, hsub2⟩ := ih2 he
      have heq := Option.some.inj (hlook1.symm.trans hlook2)
      subst heq
      exact ⟨T1, hlook1, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

theorem has_type_constNone_inv
    (h : HasType ct Γ .constNone T) :
    IsSubtype ct (.class_ noneClass) T := by
  generalize he : Expr.constNone = e at h
  induction h with
  | sub _ hsub _ ih =>
      exact .trans (ih he) hsub
  | constNone =>
      exact .refl
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

theorem has_type_constTrue_inv
    (h : HasType ct Γ .constTrue T) :
    IsSubtype ct (.class_ boolClass) T := by
  generalize he : Expr.constTrue = e at h
  induction h with
  | sub _ hsub _ ih =>
      exact .trans (ih he) hsub
  | constTrue =>
      exact .refl
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

theorem has_type_constFalse_inv
    (h : HasType ct Γ .constFalse T) :
    IsSubtype ct (.class_ boolClass) T := by
  generalize he : Expr.constFalse = e at h
  induction h with
  | sub _ hsub _ ih =>
      exact .trans (ih he) hsub
  | constFalse =>
      exact .refl
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

theorem has_type_new_inv
    (h : HasType ct Γ (.new cname) T) :
    ∃ c, findClass ct cname = some c ∧
      cname ≠ boolClass ∧
      cname ≠ noneClass ∧
      cname ≠ boundMethodClass ∧
      IsSubtype ct (.class_ cname) T := by
  generalize he : Expr.new cname = e at h
  induction h with
  | sub _ hsub _ ih =>
      obtain ⟨c, hfind, hbool, hnone, hbm, hsub'⟩ := ih he
      exact ⟨c, hfind, hbool, hnone, hbm, .trans hsub' hsub⟩
  | new hfind hbool hnone hbm =>
      cases he
      exact ⟨_, hfind, hbool, hnone, hbm, .refl⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨c, hfind, hbool, hnone, hbm, hsub1⟩ := ih1 he
      obtain ⟨_, hfind', _, _, _, hsub2⟩ := ih2 he
      have heq := Option.some.inj (hfind.symm.trans hfind')
      subst heq
      exact ⟨c, hfind, hbool, hnone, hbm, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

theorem has_type_isInstance_inv
    (h : HasType ct Γ (.isInstance x C) T) :
    (∃ T', Γ.lookup x = some T') ∧
    (∃ cls, findClass ct C = some cls) ∧
    IsSubtype ct (.class_ boolClass) T := by
  generalize he : Expr.isInstance x C = e at h
  induction h with
  | sub _ hsub _ ih =>
      obtain ⟨hlook, hfind, hsub'⟩ := ih he
      exact ⟨hlook, hfind, .trans hsub' hsub⟩
  | isInstance hlook hfind =>
      cases he
      exact ⟨⟨_, hlook⟩, ⟨_, hfind⟩, .refl⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨hlook, hfind, hsub1⟩ := ih1 he
      obtain ⟨_, _, hsub2⟩ := ih2 he
      exact ⟨hlook, hfind, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

theorem has_type_cond_isInstance_inv
    (h : HasType ct Γ (.cond (.isInstance x C) thenBr elseBr) T) :
    ∃ S cls, Γ.lookup x = some S ∧ findClass ct C = some cls := by
  generalize he : Expr.cond (.isInstance x C) thenBr elseBr = e at h
  induction h generalizing x C thenBr elseBr with
  | cond hcond _ _ _ =>
      cases he
      obtain ⟨⟨S, hlook⟩, ⟨cls, hfind⟩, _⟩ := has_type_isInstance_inv hcond
      exact ⟨S, cls, hlook, hfind⟩
  | condIsInstance hlook hfind _ _ =>
      cases he
      exact ⟨_, _, hlook, hfind⟩
  | sub _ _ _ ih =>
      exact ih he
  | interIntro _ _ ih1 _ =>
      exact ih1 he
  | _ =>
      exact Expr.noConfusion he

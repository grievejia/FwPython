import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.WellFormedness
import FwPython.Static.Subtyping.Lattice

/-! ## Theorem support for the surface typing core. -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- Typing in a well-typed class hierarchy and environment produces an annotation with known class names. -/
theorem hasType_wellFormed
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h : HasType hwfct.toWellFormedClassHierarchy Γ e T) :
    WellFormedTy ct T := by
  induction h with
  | sub _ included _ =>
      exact included.targetWellFormed
  | var hlook =>
      exact hΓwf _ _ hlook
  | constNone =>
      exact WellFormedTy.none hwfct.toWellFormedClassHierarchy
  | constTrue | constFalse | isInstance _ _ =>
      exact WellFormedTy.bool hwfct.toWellFormedClassHierarchy
  | new hfind _ _ _ =>
      exact WellFormedTy.class_of_lookup hfind
  | attrAccess _ hfmt =>
      exact findMethodType_wellFormed hwfct hfmt
  | attrAccessUnion _ hfmt1 hfmt2 =>
      exact .union (findMethodType_wellFormed hwfct hfmt1) (findMethodType_wellFormed hwfct hfmt2)
  | call _ _ _ ihCallee _ =>
      exact (ihCallee hΓwf).callable_return
  | cond _ _ _ _ _ ihThen ihElse =>
      exact .union (ihThen hΓwf) (ihElse hΓwf)
  | condIsInstance hlook hfind _ _ ihThen ihElse =>
      exact .union
        (ihThen (wellFormedTyEnv_update_class hΓwf hlook hfind))
        (ihElse (wellFormedTyEnv_update_negClass hΓwf hlook hfind))
  | interIntro _ _ ih1 ih2 =>
      exact .intersection (ih1 hΓwf) (ih2 hΓwf)

/-! ## Derived convenience lemmas. -/

theorem HasType.attrAccessInter
    (h1 : HasType structural Γ base (.class_ c1))
    (h2 : HasType structural Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType structural Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) :=
  .interIntro (.attrAccess h1 hfmt1) (.attrAccess h2 hfmt2)

/-- A call returns the declared result when the argument has the valid declared input type. -/
theorem HasType.call_direct
    (hcallee : HasType structural Γ callee (.callable paramTy returnTy))
    (harg : HasType structural Γ arg paramTy)
    (inputValid : WellFormedTy ct paramTy) :
    HasType structural Γ (.call callee arg) returnTy :=
  .call hcallee harg (.refl inputValid)

/-- If the argument satisfies both input requirements, the call satisfies both result requirements. -/
theorem HasType.call_intersection
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee
      (.intersection (.callable p1 r1) (.callable p2 r2)))
    (harg1 : HasType hwfct.toWellFormedClassHierarchy Γ arg p1)
    (harg2 : HasType hwfct.toWellFormedClassHierarchy Γ arg p2) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.call callee arg) (.intersection r1 r2) := by
  have valid := hasType_wellFormed hwfct hΓwf hcallee
  have hwf1 := valid.intersection_left
  have hwf2 := valid.intersection_right
  exact .interIntro
    (HasType.call_direct (.sub hcallee (.interLeft (.refl hwf1) hwf2)) harg1 hwf1.callable_param)
    (HasType.call_direct (.sub hcallee (.interRight (.refl hwf2) hwf1)) harg2 hwf2.callable_param)

/-- Calling either function alternative requires both inputs and permits either result. -/
theorem HasType.call_union_summary
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg (.intersection p1 p2)) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.call callee arg) (.union r1 r2) := by
  have valid := hasType_wellFormed hwfct hΓwf hcallee
  have hwf1 := valid.union_left
  have hwf2 := valid.union_right
  exact HasType.call_direct
    (.sub hcallee (subtype_union_callable_summary hwf1.callable_param hwf2.callable_param
      hwf1.callable_return hwf2.callable_return))
    harg (.intersection hwf1.callable_param hwf2.callable_param)

/-- A class-test conditional has a valid type shared by both refined branches. -/
theorem HasType.condIsInstance_common
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType structural
      (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType structural
      (Γ.update x (.intersection T (.negClass C))) elseBr R)
    (hwfR : WellFormedTy ct R) :
    HasType structural Γ (.cond (.isInstance x C) thenBr elseBr) R :=
  .sub (.condIsInstance hlook hfind hthen helse) (subtype_union_idem hwfR)

/-- Variable strengthening preserves both class-test branches, including a test of that variable. -/
private theorem hasType_strengthen_var_condIsInstance_aux
    {Γ : TyEnv} {x : Identifier} {S : Ty}
    {C : Identifier} {cls : Class} {thenBr elseBr : Expr} {thenTy elseTy : Ty}
    (hlookX : Γ.lookup x = some S)
    (hfindC : findClass ct C = some cls)
    (ihThen : ∀ {z : Identifier} {oldTy newTy : Ty},
      (Γ.update x (.intersection S (.class_ C))).lookup z = some oldTy →
      IsSubtype structural newTy oldTy →
      HasType structural
        ((Γ.update x (.intersection S (.class_ C))).update z newTy)
        thenBr thenTy)
    (ihElse : ∀ {z : Identifier} {oldTy newTy : Ty},
      (Γ.update x (.intersection S (.negClass C))).lookup z = some oldTy →
      IsSubtype structural newTy oldTy →
      HasType structural
        ((Γ.update x (.intersection S (.negClass C))).update z newTy)
        elseBr elseTy)
    {z : Identifier} {oldTy newTy : Ty}
    (hlook : Γ.lookup z = some oldTy)
    (hsub : IsSubtype structural newTy oldTy) :
    HasType structural (Γ.update z newTy)
      (.cond (.isInstance x C) thenBr elseBr)
      (.union thenTy elseTy) := by
  have hwfC : WellFormedTy ct (.class_ C) := WellFormedTy.class_of_lookup hfindC
  have hwfNegC : WellFormedTy ct (.negClass C) := WellFormedTy.negClass_of_lookup hfindC
  by_cases hxz : z = x
  · subst hxz
    have heq := Option.some.inj (hlook.symm.trans hlookX)
    subst heq
    have hThen :=
      @ihThen z (.intersection oldTy (.class_ C)) (.intersection newTy (.class_ C))
        (tyEnv_update_lookup_eq (.intersection oldTy (.class_ C)) ⟨oldTy, hlook⟩)
        (.interMono hsub (.refl hwfC))
    rw [tyEnv_update_shadow] at hThen
    have hElse :=
      @ihElse z (.intersection oldTy (.negClass C)) (.intersection newTy (.negClass C))
        (tyEnv_update_lookup_eq (.intersection oldTy (.negClass C)) ⟨oldTy, hlook⟩)
        (.interMono hsub (.refl hwfNegC))
    rw [tyEnv_update_shadow] at hElse
    exact .condIsInstance
      (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩)
      hfindC
      (by simpa [tyEnv_update_shadow] using hThen)
      (by simpa [tyEnv_update_shadow] using hElse)
  · have hne : x ≠ z := Ne.symm hxz
    have hThen :=
      @ihThen z oldTy newTy
        ((tyEnv_update_lookup_ne _ hxz).trans hlook)
        hsub
    rw [tyEnv_update_commute hne] at hThen
    have hElse :=
      @ihElse z oldTy newTy
        ((tyEnv_update_lookup_ne _ hxz).trans hlook)
        hsub
    rw [tyEnv_update_commute hne] at hElse
    have hlook' : (Γ.update z newTy).lookup x = some S :=
      (tyEnv_update_lookup_ne newTy hne).trans hlookX
    exact .condIsInstance hlook' hfindC hThen hElse

/-- Replacing one variable annotation by a subtype preserves expression typing. -/
theorem hasType_strengthen_var
    (h : HasType structural Γ e T)
    (hlook : Γ.lookup z = some oldTy)
    (hsub : IsSubtype structural newTy oldTy) :
    HasType structural (Γ.update z newTy) e T := by
  induction h generalizing z oldTy newTy with
  | var hlook' =>
      rename_i y
      by_cases hyz : y = z
      · subst hyz
        have heq := Option.some.inj (hlook.symm.trans hlook')
        subst heq
        exact .sub (.var (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩)) hsub
      · exact .var ((tyEnv_update_lookup_ne newTy hyz).trans hlook')
  | sub _ hsub' ih =>
      exact .sub (ih hlook hsub) hsub'
  | constNone =>
      exact .constNone
  | constTrue =>
      exact .constTrue
  | constFalse =>
      exact .constFalse
  | new hfind hne1 hne2 hne3 =>
      exact .new hfind hne1 hne2 hne3
  | attrAccess _ hfmt ih =>
      exact .attrAccess (ih hlook hsub) hfmt
  | attrAccessUnion _ hfmt1 hfmt2 ih =>
      exact .attrAccessUnion (ih hlook hsub) hfmt1 hfmt2
  | call _ _ hsubArg ihCallee ihArg =>
      exact .call
        (ihCallee hlook hsub)
        (ihArg hlook hsub)
        hsubArg
  | cond _ hbool _ _ ihCond ihThen ihElse =>
      exact .cond
        (ihCond hlook hsub)
        hbool
        (ihThen hlook hsub)
        (ihElse hlook hsub)
  | isInstance hlook' hfind =>
      rename_i y
      by_cases hyz : y = z
      · subst hyz
        exact .isInstance (tyEnv_update_lookup_eq newTy ⟨_, hlook⟩) hfind
      · exact .isInstance ((tyEnv_update_lookup_ne newTy hyz).trans hlook') hfind
  | condIsInstance hlookX hfindC _ _ ihThen ihElse =>
      exact hasType_strengthen_var_condIsInstance_aux
        hlookX hfindC ihThen ihElse hlook hsub
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro
        (ih1 hlook hsub)
        (ih2 hlook hsub)

/-- A typed variable has a binding whose type is a subtype of its assigned type.
The environment supplies validity of the binding when typing uses no subsumption. -/
theorem has_type_var_inv
    (h : HasType structural Γ (.var x) T) (hΓwf : WellFormedTyEnv ct Γ) :
    ∃ T', Γ.lookup x = some T' ∧ IsSubtype structural T' T := by
  generalize he : Expr.var x = e at h
  induction h with
  | sub _ hsub ih =>
      obtain ⟨T', hlook, hsub'⟩ := ih hΓwf he
      exact ⟨T', hlook, .trans hsub' hsub⟩
  | var hlook =>
      cases he
      exact ⟨_, hlook, .refl (hΓwf _ _ hlook)⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨T1, hlook1, hsub1⟩ := ih1 hΓwf he
      obtain ⟨T2, hlook2, hsub2⟩ := ih2 hΓwf he
      have heq := Option.some.inj (hlook1.symm.trans hlook2)
      subst heq
      exact ⟨T1, hlook1, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

/-- Every type assigned to None includes its declared class type. -/
theorem has_type_constNone_inv
    (h : HasType structural Γ .constNone T) :
    IsSubtype structural (.class_ noneClass) T := by
  generalize he : Expr.constNone = e at h
  induction h with
  | sub _ hsub ih =>
      exact .trans (ih he) hsub
  | constNone =>
      exact .refl (.none structural)
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

/-- Every type assigned to True includes Bool. -/
theorem has_type_constTrue_inv
    (h : HasType structural Γ .constTrue T) :
    IsSubtype structural (.class_ boolClass) T := by
  generalize he : Expr.constTrue = e at h
  induction h with
  | sub _ hsub ih =>
      exact .trans (ih he) hsub
  | constTrue =>
      exact .refl (.bool structural)
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

/-- Every type assigned to False includes Bool. -/
theorem has_type_constFalse_inv
    (h : HasType structural Γ .constFalse T) :
    IsSubtype structural (.class_ boolClass) T := by
  generalize he : Expr.constFalse = e at h
  induction h with
  | sub _ hsub ih =>
      exact .trans (ih he) hsub
  | constFalse =>
      exact .refl (.bool structural)
  | interIntro _ _ ih1 ih2 =>
      exact .interIntro (ih1 he) (ih2 he)
  | _ =>
      exact Expr.noConfusion he

/-- A typed allocation selects a declared, allocatable class whose type is below the result. -/
theorem has_type_new_inv
    (h : HasType structural Γ (.new cname) T) :
    ∃ c, findClass ct cname = some c ∧
      cname ≠ boolClass ∧
      cname ≠ noneClass ∧
      cname ≠ boundMethodClass ∧
      IsSubtype structural (.class_ cname) T := by
  generalize he : Expr.new cname = e at h
  induction h with
  | sub _ hsub ih =>
      obtain ⟨c, hfind, hbool, hnone, hbm, hsub'⟩ := ih he
      exact ⟨c, hfind, hbool, hnone, hbm, .trans hsub' hsub⟩
  | new hfind hbool hnone hbm =>
      cases he
      exact ⟨_, hfind, hbool, hnone, hbm, .refl (WellFormedTy.class_of_lookup hfind)⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨c, hfind, hbool, hnone, hbm, hsub1⟩ := ih1 he
      obtain ⟨_, hfind', _, _, _, hsub2⟩ := ih2 he
      have heq := Option.some.inj (hfind.symm.trans hfind')
      subst heq
      exact ⟨c, hfind, hbool, hnone, hbm, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

/-- A typed class test has a bound variable, a declared test class, and a result above Bool. -/
theorem has_type_isInstance_inv
    (h : HasType structural Γ (.isInstance x C) T) :
    (∃ T', Γ.lookup x = some T') ∧
    (∃ cls, findClass ct C = some cls) ∧
    IsSubtype structural (.class_ boolClass) T := by
  generalize he : Expr.isInstance x C = e at h
  induction h with
  | sub _ hsub ih =>
      obtain ⟨hlook, hfind, hsub'⟩ := ih he
      exact ⟨hlook, hfind, .trans hsub' hsub⟩
  | isInstance hlook hfind =>
      cases he
      exact ⟨⟨_, hlook⟩, ⟨_, hfind⟩, .refl (.bool structural)⟩
  | interIntro _ _ ih1 ih2 =>
      obtain ⟨hlook, hfind, hsub1⟩ := ih1 he
      obtain ⟨_, _, hsub2⟩ := ih2 he
      exact ⟨hlook, hfind, .interIntro hsub1 hsub2⟩
  | _ =>
      exact Expr.noConfusion he

/-- A typed conditional with a class test has a bound test variable and a declared test class. -/
theorem has_type_cond_isInstance_inv
    (h : HasType structural Γ (.cond (.isInstance x C) thenBr elseBr) T) :
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
  | sub _ _ ih =>
      exact ih he
  | interIntro _ _ ih1 _ =>
      exact ih1 he
  | _ =>
      exact Expr.noConfusion he

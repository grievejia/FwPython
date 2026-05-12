import FwPython.Static.TypeSystem.WellFormedness

/-! ## Algorithmic lookup prerequisites -/

def wellFormedTy_decidable
    (hwfct : WellFormedClassTable ct) :
    (T : Ty) → Decidable (WellFormedTy ct T)
  | .bottom =>
      isTrue .bottom
  | .class_ cname =>
      match hfind : findClass ct cname with
      | none =>
          isFalse (by
            intro hwf
            cases hwf with
            | class_ hfind' _ =>
                rw [hfind] at hfind'
                cases hfind')
      | some cls =>
          isTrue (.class_ hfind (hwfct.allMrosExist _ _ hfind).hmro)
  | .negClass cname =>
      match hfind : findClass ct cname with
      | none =>
          isFalse (by
            intro hwf
            cases hwf with
            | negClass hfind' _ =>
                rw [hfind] at hfind'
                cases hfind')
      | some cls =>
          isTrue (.negClass hfind (hwfct.allMrosExist _ _ hfind).hmro)
  | .union T U =>
      match wellFormedTy_decidable hwfct T, wellFormedTy_decidable hwfct U with
      | isTrue hwfT, isTrue hwfU =>
          isTrue (.union hwfT hwfU)
      | isFalse hnotT, _ =>
          isFalse (by
            intro hwf
            cases hwf with
            | union hwfT _ =>
                exact hnotT hwfT)
      | _, isFalse hnotU =>
          isFalse (by
            intro hwf
            cases hwf with
            | union _ hwfU =>
                exact hnotU hwfU)
  | .intersection T U =>
      match wellFormedTy_decidable hwfct T, wellFormedTy_decidable hwfct U with
      | isTrue hwfT, isTrue hwfU =>
          isTrue (.intersection hwfT hwfU)
      | isFalse hnotT, _ =>
          isFalse (by
            intro hwf
            cases hwf with
            | intersection hwfT _ =>
                exact hnotT hwfT)
      | _, isFalse hnotU =>
          isFalse (by
            intro hwf
            cases hwf with
            | intersection _ hwfU =>
                exact hnotU hwfU)
  | .callable T U =>
      match wellFormedTy_decidable hwfct T, wellFormedTy_decidable hwfct U with
      | isTrue hwfT, isTrue hwfU =>
          isTrue (.callable hwfT hwfU)
      | isFalse hnotT, _ =>
          isFalse (by
            intro hwf
            cases hwf with
            | callable hwfT _ =>
                exact hnotT hwfT)
      | _, isFalse hnotU =>
          isFalse (by
            intro hwf
            cases hwf with
            | callable _ hwfU =>
                exact hnotU hwfU)

private def VisibleTyEnvWellFormed (ct : ClassTable) (seen : List Identifier) :
    TyEnv → Prop
  | [] => True
  | (x, T) :: rest =>
      if x ∈ seen then
        VisibleTyEnvWellFormed ct (x :: seen) rest
      else
        WellFormedTy ct T ∧ VisibleTyEnvWellFormed ct (x :: seen) rest

private theorem lookup_cons_eq
    {Γ : TyEnv} {x : Identifier} {T : Ty} :
    NamedEnv.lookup ((x, T) :: Γ) x = some T := by
  simp [NamedEnv.lookup]

private theorem lookup_cons_ne
    {Γ : TyEnv} {x y : Identifier} {T : Ty}
    (hne : y ≠ x) :
    NamedEnv.lookup ((x, T) :: Γ) y = NamedEnv.lookup Γ y := by
  have hxy : x ≠ y := Ne.symm hne
  simp [NamedEnv.lookup, hxy]

private def visibleTyEnvWellFormed_decidable
    (hwfct : WellFormedClassTable ct) (seen : List Identifier) :
    (Γ : TyEnv) → Decidable (VisibleTyEnvWellFormed ct seen Γ)
  | [] =>
      isTrue trivial
  | (x, T) :: rest =>
      by
        by_cases hx : x ∈ seen
        · simpa [VisibleTyEnvWellFormed, hx] using
            visibleTyEnvWellFormed_decidable hwfct (x :: seen) rest
        · match wellFormedTy_decidable hwfct T,
            visibleTyEnvWellFormed_decidable hwfct (x :: seen) rest with
          | isTrue hwfT, isTrue hrest =>
              exact isTrue (by simp [VisibleTyEnvWellFormed, hx, hwfT, hrest])
          | isFalse hnotT, _ =>
              exact isFalse (by
                intro hvis
                simp [VisibleTyEnvWellFormed, hx] at hvis
                exact hnotT hvis.1)
          | _, isFalse hnotRest =>
              exact isFalse (by
                intro hvis
                simp [VisibleTyEnvWellFormed, hx] at hvis
                exact hnotRest hvis.2)

private theorem visibleTyEnvWellFormed_iff
    (seen : List Identifier) (Γ : TyEnv) :
    VisibleTyEnvWellFormed ct seen Γ ↔
      ∀ x T, Γ.lookup x = some T → x ∉ seen → WellFormedTy ct T := by
  induction Γ generalizing seen with
  | nil =>
      constructor
      · intro _
        intro x T hlook
        simp [NamedEnv.lookup] at hlook
      · intro _
        trivial
  | cons p rest ih =>
      rcases p with ⟨y, U⟩
      by_cases hy : y ∈ seen
      · constructor
        · intro hvis x T hlook hnotSeen
          have hxy : x ≠ y := by
            intro hEq
            subst hEq
            exact hnotSeen hy
          have hyx : y ≠ x := Ne.symm hxy
          have hlookRest : NamedEnv.lookup rest x = some T := by
            simpa [NamedEnv.lookup, hyx] using hlook
          exact (ih (y :: seen)).1
            (by simpa [VisibleTyEnvWellFormed, hy] using hvis)
            x T hlookRest (by simp [hxy, hnotSeen])
        · intro hlooks
          have hrest :
              VisibleTyEnvWellFormed ct (y :: seen) rest :=
            (ih (y :: seen)).2 (by
              intro x T hlookRest hnotSeen
              have hxy : x ≠ y := by
                intro hEq
                subst hEq
                exact hnotSeen (by simp)
              have hyx : y ≠ x := Ne.symm hxy
              have hlookFull : NamedEnv.lookup ((y, U) :: rest) x = some T := by
                simpa [NamedEnv.lookup, hyx] using hlookRest
              exact hlooks x T hlookFull (by
                intro hxSeen
                exact hnotSeen (by simp [hxSeen])))
          simpa [VisibleTyEnvWellFormed, hy] using hrest
      · constructor
        · intro hvis x T hlook hnotSeen
          have hvis' : WellFormedTy ct U ∧ VisibleTyEnvWellFormed ct (y :: seen) rest := by
            simpa [VisibleTyEnvWellFormed, hy] using hvis
          by_cases hxy : x = y
          · subst x
            have hTy : some U = some T := by
              simpa [NamedEnv.lookup] using hlook
            cases hTy
            exact hvis'.1
          · have hlookRest : NamedEnv.lookup rest x = some T := by
              have hyx : y ≠ x := Ne.symm hxy
              simpa [NamedEnv.lookup, hyx] using hlook
            exact (ih (y :: seen)).1 hvis'.2 x T hlookRest (by
              simp [hxy, hnotSeen])
        · intro hlooks
          have hUwf : WellFormedTy ct U :=
            hlooks y U (lookup_cons_eq (Γ := rest) (x := y) (T := U)) hy
          have hrest :
              VisibleTyEnvWellFormed ct (y :: seen) rest :=
            (ih (y :: seen)).2 (by
              intro x T hlookRest hnotSeen
              have hxy : x ≠ y := by
                intro hEq
                subst hEq
                exact hnotSeen (by simp)
              have hyx : y ≠ x := Ne.symm hxy
              have hlookFull : NamedEnv.lookup ((y, U) :: rest) x = some T := by
                simpa [NamedEnv.lookup, hyx] using hlookRest
              exact hlooks x T hlookFull (by
                intro hxSeen
                exact hnotSeen (by simp [hxSeen])))
          simpa [VisibleTyEnvWellFormed, hy] using And.intro hUwf hrest

def wellFormedTyEnv_decidable
    (hwfct : WellFormedClassTable ct) (Γ : TyEnv) :
    Decidable (WellFormedTyEnv ct Γ) := by
  let hdec := visibleTyEnvWellFormed_decidable hwfct [] Γ
  cases hdec with
  | isTrue hvis =>
      exact isTrue <| by
        intro x T hlook
        exact (visibleTyEnvWellFormed_iff (ct := ct) [] Γ).1 hvis x T hlook (by simp)
  | isFalse hnot =>
      exact isFalse <| by
        intro hΓwf
        apply hnot
        exact (visibleTyEnvWellFormed_iff (ct := ct) [] Γ).2 (by
          intro x T hlook _
          exact hΓwf x T hlook)

def classNameList (ct : ClassTable) : List Identifier :=
  ct.map ClassDecl.name

theorem findClass_some_mem_classNameList
    (hfind : findClass ct cname = some cls) :
    cname ∈ classNameList ct := by
  unfold classNameList
  exact List.mem_map.mpr ⟨cls, findClass_mem hfind, findClass_name hfind⟩

private def lookupMethodTyOnMro
    (ct : ClassTable) (mro : List Identifier) (attr : Identifier) :
    Option (Ty × Ty) :=
  match findMethodInMro ct mro attr with
  | none => none
  | some m => some (m.paramTy, m.returnTy)

def staticLookupMethodTy? (hwfct : WellFormedClassTable ct)
    (cname attr : Identifier) : Option (Ty × Ty) :=
  match hfind : findClass ct cname with
  | none => none
  | some _cls =>
      let mro := (hwfct.allMrosExist _ _ hfind).mro
      lookupMethodTyOnMro ct mro attr

theorem staticLookupMethodTy?_of_find
    (hwfct : WellFormedClassTable ct)
    (hfindTy : FindMethodType ct cname attr P R) :
    staticLookupMethodTy? hwfct cname attr = some (P, R) := by
  obtain ⟨cls, mro, m, hfind, hmro, hmethod, hparam, hreturn⟩ := hfindTy
  subst hparam
  subst hreturn
  unfold staticLookupMethodTy?
  split
  · rename_i hnone
    rw [hfind] at hnone
    cases hnone
  · rename_i cls' hfind'
    have hcls' : cls' = cls := by
      rw [hfind] at hfind'
      cases hfind'
      rfl
    subst hcls'
    let wmro := hwfct.allMrosExist _ _ hfind
    have hmroEq : wmro.mro = mro := determinism wmro.hmro hmro
    have hlookupW : findMethodInMro ct wmro.mro attr = some m := by
      simpa [hmroEq] using hmethod
    simp [lookupMethodTyOnMro, wmro, hlookupW]

private theorem staticLookupMethodTy?_find
    (hwfct : WellFormedClassTable ct)
    (hlookup : staticLookupMethodTy? hwfct cname attr = some (P, R)) :
    FindMethodType ct cname attr P R := by
  unfold staticLookupMethodTy? at hlookup
  split at hlookup
  · simp at hlookup
  · rename_i cls hfind
    let wmro := hwfct.allMrosExist _ _ hfind
    unfold lookupMethodTyOnMro at hlookup
    cases hmethod : findMethodInMro ct wmro.mro attr with
    | none =>
        simp [wmro, hmethod] at hlookup
    | some m =>
        simp [wmro, hmethod] at hlookup
        obtain ⟨hparam, hreturn⟩ := hlookup
        exact ⟨cls, wmro.mro, m, hfind, wmro.hmro, hmethod, hparam, hreturn⟩

theorem staticLookupMethodTy?_some_iff_findMethodType
    (hwfct : WellFormedClassTable ct) :
    staticLookupMethodTy? hwfct cname attr = some (P, R) ↔
      FindMethodType ct cname attr P R := by
  constructor
  · exact staticLookupMethodTy?_find hwfct
  · exact staticLookupMethodTy?_of_find hwfct

theorem staticLookupMethodTy?_none_iff_not_findMethodType
    (hwfct : WellFormedClassTable ct) :
    staticLookupMethodTy? hwfct cname attr = none ↔
      ¬ ∃ P R, FindMethodType ct cname attr P R := by
  constructor
  · intro hnone hex
    rcases hex with ⟨P, R, hfindTy⟩
    rw [staticLookupMethodTy?_of_find hwfct hfindTy] at hnone
    cases hnone
  · intro hnot
    cases hlookup : staticLookupMethodTy? hwfct cname attr with
    | none =>
        rfl
    | some pr =>
        rcases pr with ⟨P, R⟩
        exfalso
        exact hnot ⟨P, R, (staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup⟩

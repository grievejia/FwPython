import FwPython.Static.TypeSystem.WellFormedness

/-! ## Algorithmic lookup prerequisites -/

private def lookupMethodTyOnMro
    (ct : ClassTable) (mro : List Identifier) (attr : Identifier) :
    Option (Ty × Ty) :=
  match findMethodInMro ct mro attr with
  | none => none
  | some m => some (m.paramTy, m.returnTy)

def staticLookupMethodTy? (hwfct : WellTypedClassHierarchy ct)
    (cname attr : Identifier) : Option (Ty × Ty) :=
  match hfind : findClass ct cname with
  | none => none
  | some _cls =>
      let mro := (hwfct.allMrosExist _ _ hfind).mro
      lookupMethodTyOnMro ct mro attr

theorem staticLookupMethodTy?_of_find
    (hwfct : WellTypedClassHierarchy ct)
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

/-- A successful computed method lookup supplies its declared function signature. -/
theorem staticLookupMethodTy?_find
    (hwfct : WellTypedClassHierarchy ct)
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

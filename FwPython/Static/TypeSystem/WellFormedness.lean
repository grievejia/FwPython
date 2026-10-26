import FwPython.Static.Subtyping.Inversion
import FwPython.Static.TypeSystem.Value.Lemmas
import FwPython.Static.MRO.LookupLemmas

/-! ## Type environment update helpers -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

theorem tyEnv_update_lookup_eq
    {Γ : TyEnv} {x : Identifier} (S : Ty)
    (hx : ∃ T, Γ.lookup x = some T) :
    (Γ.update x S).lookup x = some S :=
  namedEnv_update_lookup_eq S hx

theorem tyEnv_update_lookup_ne
    {Γ : TyEnv} {x y : Identifier} (S : Ty)
    (hne : y ≠ x) :
    (Γ.update x S).lookup y = Γ.lookup y :=
  namedEnv_update_lookup_ne S hne

/-- Shadowing: a double update at the same key keeps only the last value. -/
theorem tyEnv_update_shadow
    {Γ : TyEnv} {x : Identifier} {S T : Ty} :
    (Γ.update x S).update x T = Γ.update x T :=
  namedEnv_update_shadow

/-- Commuting: updates at distinct keys can be reordered. -/
theorem tyEnv_update_commute
    {Γ : TyEnv} {x y : Identifier} {S T : Ty}
    (hne : x ≠ y) :
    (Γ.update x S).update y T = (Γ.update y T).update x S :=
  namedEnv_update_commute hne

/-- Updating a well-formed type environment at a bound variable with a
    well-formed type preserves well-formedness. -/
theorem wellFormedTyEnv_update
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some oldTy)
    (hwfNew : WellFormedTy ct newTy) :
    WellFormedTyEnv ct (Γ.update x newTy) := by
  intro y T hlookΓ'
  by_cases hyx : y = x
  · subst hyx
    have hlookS := tyEnv_update_lookup_eq newTy ⟨oldTy, hlook⟩
    rw [hlookS] at hlookΓ'
    exact Option.some.inj hlookΓ'.symm ▸ hwfNew
  · rw [tyEnv_update_lookup_ne newTy hyx] at hlookΓ'
    exact hΓwf y T hlookΓ'

/-- Narrowing a bound variable's type by intersecting with a class preserves
    environment well-formedness. -/
theorem wellFormedTyEnv_update_class
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls) :
    WellFormedTyEnv ct (Γ.update x (.intersection T (.class_ C))) :=
  wellFormedTyEnv_update hΓwf hlook
    (.intersection (hΓwf _ _ hlook) (WellFormedTy.class_of_lookup hfind))

/-- Narrowing a bound variable's type by intersecting with a negated class
    preserves environment well-formedness. -/
theorem wellFormedTyEnv_update_negClass
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls) :
    WellFormedTyEnv ct (Γ.update x (.intersection T (.negClass C))) :=
  wellFormedTyEnv_update hΓwf hlook
    (.intersection (hΓwf _ _ hlook) (WellFormedTy.negClass_of_lookup hfind))

/-! ## Well-formedness of typed terms -/

/-- FindMethodType produces well-formed callable types. -/
theorem findMethodType_wellFormed
    (hwf : WellTypedClassHierarchy ct)
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    WellFormedTy ct (.callable paramTy returnTy) := by
  obtain ⟨_, _, _, found, computed, hmethod, rfl, rfl⟩ := hfmt
  exact methodInReceiverMro_wellFormed hwf
    (method_in_receiver_mro_of_lookup found computed hmethod)

/-- Derive WellFormedTyEnv from EnvHasType via valueHasType_wellFormed. -/
theorem envHasType_wellFormedTyEnv
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy h env Γ) :
    WellFormedTyEnv ct Γ := by
  intro x T hlook
  obtain ⟨v, _, hval⟩ := henv x T hlook
  exact valueHasType_wellFormed hwf hheap hval

/-! ## Type environment narrowing -/

/-- Narrow the type environment at variable `x` given a new typing proof. -/
theorem env_has_type_narrow
     {hp : Heap} {env : Env} {Γ : TyEnv}
    {x : Identifier} {T S : Ty}
    (henv : EnvHasType structural hp env Γ)
    (hlookΓ : Γ.lookup x = some T)
    (hval : ∀ v, env.lookup x = some v → ValueHasType structural hp v S) :
    EnvHasType structural hp env (Γ.update x S) := by
  intro y Ty' hlookΓ'
  by_cases hyx : y = x
  · subst hyx
    have hlookS := tyEnv_update_lookup_eq S ⟨T, hlookΓ⟩
    rw [hlookS] at hlookΓ'; have := Option.some.inj hlookΓ'.symm; subst this
    obtain ⟨v, henv_v, _⟩ := henv _ T hlookΓ
    exact ⟨v, henv_v, hval v henv_v⟩
  · rw [tyEnv_update_lookup_ne S hyx] at hlookΓ'
    exact henv y Ty' hlookΓ'

/-! ## Method resolution helpers -/

/-- A typed method must exist on the runtime receiver's MRO. -/
theorem typed_method_exists_on_runtime_receiver
     {cname attrName : Identifier} {paramTy returnTy : Ty}
    (hwf : WellTypedClassHierarchy ct)
    (hfmt : FindMethodType ct cname attrName paramTy returnTy)
    {recvClass : Identifier} {recvCls : Class} {recvMro : List Identifier}
    (hsub : IsSubtype hwf.toWellFormedClassHierarchy (.class_ recvClass) (.class_ cname))
    (hfindRecv : findClass ct recvClass = some recvCls)
    (hmroRecv : ComputeMro ct recvCls recvMro) :
    ∃ m, findMethodInMro ct recvMro attrName = some m := by
  obtain ⟨c_decl, mro_decl, m_decl, hfind_decl, hmro_decl, hmethod_decl, _, _⟩ := hfmt
  have hcn_in_mro := class_subtype_mem_mro hwf.toWellFormedClassHierarchy hsub hfindRecv hmroRecv
  have hfind_cname : findClass ct cname = some c_decl := hfind_decl
  exact findMethodInMro_of_ancestor hmroRecv (findClass_self hfindRecv) hcn_in_mro
    hfind_cname hmro_decl hmethod_decl

/-- Liskov variance for a typed method resolved on the runtime receiver. -/
theorem typed_method_variance_on_runtime_receiver

    (hwf : WellTypedClassHierarchy ct)
    {cname attrName : Identifier} {paramTy returnTy : Ty}
    (hfmt : FindMethodType ct cname attrName paramTy returnTy)
    {recvClass : Identifier} {recvCls : Class} {recvMro : List Identifier}
    (hsub : IsSubtype hwf.toWellFormedClassHierarchy (.class_ recvClass) (.class_ cname))
    (hfindRecv : findClass ct recvClass = some recvCls)
    (hmroRecv : ComputeMro ct recvCls recvMro)
    {m : Method}
    (hlookupRecv : findMethodInMro ct recvMro attrName = some m) :
    IsSubtype hwf.toWellFormedClassHierarchy paramTy m.paramTy ∧ IsSubtype hwf.toWellFormedClassHierarchy m.returnTy returnTy := by
  obtain ⟨c_decl, mro_decl, m_decl, hfind_decl, hmro_decl, hmethod_decl, hpeq, hreq⟩ := hfmt
  have hcn_in_mro := class_subtype_mem_mro hwf.toWellFormedClassHierarchy hsub hfindRecv hmroRecv
  have ⟨hpvar, hrvar⟩ := hwf.liskovCondition recvClass cname recvCls c_decl recvMro mro_decl attrName m m_decl
    hfindRecv hmroRecv hcn_in_mro hfind_decl hmro_decl hlookupRecv hmethod_decl
  exact ⟨hpeq ▸ hpvar, hreq ▸ hrvar⟩

/-- A subtype of a leaf built-in is the built-in itself. -/
theorem bool_subtype_is_bool
    (hwf : WellTypedClassHierarchy ct)
    (hsub : IsSubtype hwf.toWellFormedClassHierarchy (.class_ actual) (.class_ boolClass))
    (hfind : findClass ct actual = some cls)
    (hmro : ComputeMro ct cls mro) :
    actual = boolClass :=
  hwf.sealedLeaf boolClass (by simp [sealedClasses]) actual cls mro hfind hmro
    (class_subtype_mem_mro hwf.toWellFormedClassHierarchy hsub hfind hmro)

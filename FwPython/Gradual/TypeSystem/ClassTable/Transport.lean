import FwPython.Common.Forall2
import FwPython.Gradual.Statics
import FwPython.Gradual.TypeSystem.Context
import FwPython.Gradual.TypeSystem.Method.Lookup

/-! # Source-side precision relations for gradual programs

Defines exact-shape precision relations on gradual source programs:
environments, methods, classes, class tables, and programs. Precision
only changes gradual type annotations (via `MoreStatic`); it does not
change source expressions, class names, base-class lists, method order,
method names, parameter names, or method bodies. -/

/-! ## Source Precision Relations -/

inductive TyEnvAnnotationPrecision (gct : GClassTable) : GTyEnv → GTyEnv → Prop where
  | nil :
      TyEnvAnnotationPrecision gct [] []
  | cons :
      MoreStatic gct G₁ G₂ →
      TyEnvAnnotationPrecision gct Γ₁ Γ₂ →
      TyEnvAnnotationPrecision gct ((x, G₁) :: Γ₁) ((x, G₂) :: Γ₂)

structure MethodAnnotationPrecision (gct : GClassTable) (m₁ m₂ : GMethod) : Prop where
  name_eq : m₁.name = m₂.name
  receiver_eq : m₁.receiverParam = m₂.receiverParam
  param_eq : m₁.param = m₂.param
  paramTy_prec : MoreStatic gct m₁.paramTy m₂.paramTy
  returnTy_prec : MoreStatic gct m₁.returnTy m₂.returnTy
  body_eq : m₁.body = m₂.body

structure ClassAnnotationPrecision (gct : GClassTable) (gc₁ gc₂ : GClass) : Prop where
  name_eq : gc₁.name = gc₂.name
  baseClasses_eq : gc₁.baseClasses = gc₂.baseClasses
  methods_prec : Forall₂ (MethodAnnotationPrecision gct) gc₁.methods gc₂.methods

abbrev ClassTableAnnotationPrecision (gct₁ gct₂ : GClassTable) : Prop :=
  Forall₂ (ClassAnnotationPrecision gct₁) gct₁ gct₂

structure ProgramAnnotationPrecision (gp₁ gp₂ : GProgram) : Prop where
  classes_prec : ClassTableAnnotationPrecision gp₁.classes gp₂.classes
  main_eq : gp₁.main = gp₂.main

theorem programAnnotationPrecision_implies_classTableAnnotationPrecision
    (h : ProgramAnnotationPrecision gp₁ gp₂) :
    ClassTableAnnotationPrecision gp₁.classes gp₂.classes :=
  h.classes_prec

/-! ## Reflexivity -/

theorem tyEnvAnnotationPrecision_refl (gct : GClassTable) : ∀ (Γ : GTyEnv),
    TyEnvAnnotationPrecision gct Γ Γ
  | [] => .nil
  | (_, G) :: Γ => .cons (moreStatic_refl gct G) (tyEnvAnnotationPrecision_refl gct Γ)

theorem methodAnnotationPrecision_refl (gct : GClassTable) (m : GMethod) :
    MethodAnnotationPrecision gct m m :=
  ⟨rfl, rfl, rfl, moreStatic_refl gct m.paramTy, moreStatic_refl gct m.returnTy, rfl⟩

theorem classAnnotationPrecision_refl (gct : GClassTable) (gc : GClass) :
    ClassAnnotationPrecision gct gc gc :=
  ⟨rfl, rfl, forall₂_refl (methodAnnotationPrecision_refl gct) gc.methods⟩

theorem classTableAnnotationPrecision_refl (gct : GClassTable) :
    ClassTableAnnotationPrecision gct gct :=
  forall₂_refl (classAnnotationPrecision_refl gct) gct

theorem programAnnotationPrecision_refl (gp : GProgram) :
    ProgramAnnotationPrecision gp gp :=
  ⟨classTableAnnotationPrecision_refl gp.classes, rfl⟩

/-! ## Erasure Equality -/

theorem eraseMethod_eq_of_methodAnnotationPrecision
    (h : MethodAnnotationPrecision gct m₁ m₂) :
    eraseMethod m₁ = eraseMethod m₂ := by
  unfold eraseMethod; rw [h.name_eq, h.receiver_eq, h.param_eq]

theorem eraseClass_eq_of_classAnnotationPrecision
    (h : ClassAnnotationPrecision gct gc₁ gc₂) :
    eraseClass gc₁ = eraseClass gc₂ := by
  unfold eraseClass
  rw [h.name_eq, h.baseClasses_eq,
    show gc₁.methods.map eraseMethod = gc₂.methods.map eraseMethod from
      forall₂_map_eq (fun _ _ hm => eraseMethod_eq_of_methodAnnotationPrecision hm) h.methods_prec]

theorem eraseClassTable_eq_of_classTableAnnotationPrecision
    (h : ClassTableAnnotationPrecision gct₁ gct₂) :
    eraseClassTable gct₁ = eraseClassTable gct₂ :=
  forall₂_map_eq (fun _ _ hc => eraseClass_eq_of_classAnnotationPrecision hc) h

theorem ClassTableAnnotationPrecision_preserves_erase
    (h : ClassTableAnnotationPrecision gct₁ gct₂) :
    eraseClassTable gct₁ = eraseClassTable gct₂ :=
  eraseClassTable_eq_of_classTableAnnotationPrecision h

/-! ## Semantic Transport -/

theorem moreStatic_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂) :
    MoreStatic gct₁ G₁ G₂ ↔ MoreStatic gct₂ G₁ G₂ := by
  unfold MoreStatic; rw [eraseClassTable_eq_of_classTableAnnotationPrecision hct]

theorem gradualSubtype_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂) :
    GradualSubtype gct₁ G₁ G₂ ↔ GradualSubtype gct₂ G₁ G₂ := by
  unfold GradualSubtype; rw [eraseClassTable_eq_of_classTableAnnotationPrecision hct]

theorem assignableTo_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂) :
    AssignableTo gct₁ G₁ G₂ ↔ AssignableTo gct₂ G₁ G₂ := by
  unfold AssignableTo; rw [eraseClassTable_eq_of_classTableAnnotationPrecision hct]

/-! ## Transitivity -/

theorem tyEnvAnnotationPrecision_trans
    (h12 : TyEnvAnnotationPrecision gct Γ₁ Γ₂)
    (h23 : TyEnvAnnotationPrecision gct Γ₂ Γ₃) :
    TyEnvAnnotationPrecision gct Γ₁ Γ₃ := by
  induction h12 generalizing Γ₃ with
  | nil => cases h23; exact .nil
  | cons hprec _ ih =>
    cases h23 with
    | cons hprec' h23' => exact .cons (moreStatic_trans hprec hprec') (ih h23')

theorem methodAnnotationPrecision_trans
    (h12 : MethodAnnotationPrecision gct m₁ m₂) (h23 : MethodAnnotationPrecision gct m₂ m₃) :
    MethodAnnotationPrecision gct m₁ m₃ :=
  ⟨h12.name_eq.trans h23.name_eq, h12.receiver_eq.trans h23.receiver_eq,
   h12.param_eq.trans h23.param_eq, moreStatic_trans h12.paramTy_prec h23.paramTy_prec,
   moreStatic_trans h12.returnTy_prec h23.returnTy_prec, h12.body_eq.trans h23.body_eq⟩

theorem classAnnotationPrecision_trans
    (h12 : ClassAnnotationPrecision gct c₁ c₂) (h23 : ClassAnnotationPrecision gct c₂ c₃) :
    ClassAnnotationPrecision gct c₁ c₃ where
  name_eq := h12.name_eq.trans h23.name_eq
  baseClasses_eq := h12.baseClasses_eq.trans h23.baseClasses_eq
  methods_prec := forall₂_trans (R := MethodAnnotationPrecision gct)
    (fun _ _ _ h₁ h₂ => methodAnnotationPrecision_trans h₁ h₂) h12.methods_prec h23.methods_prec

theorem classTableAnnotationPrecision_trans
    (h12 : ClassTableAnnotationPrecision gct₁ gct₂) (h23 : ClassTableAnnotationPrecision gct₂ gct₃) :
    ClassTableAnnotationPrecision gct₁ gct₃ := by
  have h23' : Forall₂ (ClassAnnotationPrecision gct₁) gct₂ gct₃ :=
    forall₂_imp (fun _ _ hc =>
      ⟨hc.name_eq, hc.baseClasses_eq,
       forall₂_imp (fun _ _ hm =>
         ⟨hm.name_eq, hm.receiver_eq, hm.param_eq,
          (moreStatic_transport h12).mpr hm.paramTy_prec,
          (moreStatic_transport h12).mpr hm.returnTy_prec, hm.body_eq⟩)
         hc.methods_prec⟩) h23
  exact forall₂_trans (R := ClassAnnotationPrecision gct₁)
    (fun _ _ _ h₁ h₂ => classAnnotationPrecision_trans h₁ h₂) h12 h23'

theorem programAnnotationPrecision_trans
    (h12 : ProgramAnnotationPrecision gp₁ gp₂) (h23 : ProgramAnnotationPrecision gp₂ gp₃) :
    ProgramAnnotationPrecision gp₁ gp₃ :=
  ⟨classTableAnnotationPrecision_trans h12.classes_prec h23.classes_prec,
   h12.main_eq.trans h23.main_eq⟩

/-! ## Environment Lookup and Update -/

theorem tyEnvAnnotationPrecision_lookup
    (hΓ : TyEnvAnnotationPrecision gct Γ₁ Γ₂) (hlook : Γ₁.lookup x = some G₁) :
    ∃ G₂, Γ₂.lookup x = some G₂ ∧ MoreStatic gct G₁ G₂ := by
  induction hΓ with
  | nil => simp [NamedEnv.lookup] at hlook
  | @cons G₁' G₂' Γ₁' Γ₂' x' hprec _ ih =>
    by_cases hxx : x' = x
    · simp [NamedEnv.lookup, hxx] at hlook ⊢
      cases hlook
      exact hprec
    · simp [NamedEnv.lookup, hxx] at hlook ⊢
      exact ih hlook

theorem tyEnvAnnotationPrecision_update
    (hΓ : TyEnvAnnotationPrecision gct Γ₁ Γ₂) (hprec : MoreStatic gct G₁ G₂) :
    TyEnvAnnotationPrecision gct (Γ₁.update x G₁) (Γ₂.update x G₂) := by
  induction hΓ with
  | nil => exact .nil
  | @cons G₁' G₂' Γ₁' Γ₂' x' hprec' htail ih =>
    by_cases hxx : x' = x
    · subst hxx
      simpa [GTyEnv.update, NamedEnv.update] using
        (TyEnvAnnotationPrecision.cons hprec htail)
    · simpa [GTyEnv.update, NamedEnv.update, hxx] using
        (TyEnvAnnotationPrecision.cons hprec' ih)

/-! ## Class and Method Lookup -/

private theorem findGClass_none_of_forall₂
    {gct : GClassTable}
    (hct : Forall₂ (ClassAnnotationPrecision gct) gcs₁ gcs₂)
    (h : findGClass gcs₁ cname = none) :
    findGClass gcs₂ cname = none :=
  findByName_none_of_forall₂ (fun hc => hc.name_eq) hct h

private theorem findGMethodInList_none_of_forall₂
    {gct : GClassTable}
    (hms : Forall₂ (MethodAnnotationPrecision gct) ms₁ ms₂)
    (h : findGMethodInList ms₁ mname = none) :
    findGMethodInList ms₂ mname = none :=
  findByName_none_of_forall₂ (fun hm => hm.name_eq) hms h

theorem findGClass_precision
    {gct : GClassTable}
    (hct : Forall₂ (ClassAnnotationPrecision gct) gcs₁ gcs₂)
    (hfind : findGClass gcs₁ cname = some gc₁) :
    ∃ gc₂,
      findGClass gcs₂ cname = some gc₂ ∧
      ClassAnnotationPrecision gct gc₁ gc₂ :=
  findByName_some_of_forall₂ (fun hc => hc.name_eq) hct hfind

theorem findGMethodInList_precision
    (hms : Forall₂ (MethodAnnotationPrecision gct) ms₁ ms₂)
    (hfind : findGMethodInList ms₁ mname = some m₁) :
    ∃ m₂,
      findGMethodInList ms₂ mname = some m₂ ∧
      MethodAnnotationPrecision gct m₁ m₂ :=
  findByName_some_of_forall₂ (fun hm => hm.name_eq) hms hfind

/-! ## MRO Transport -/

private theorem resolvedBases_eq_of_classAnnotationPrecision
    {gct : GClassTable} {gc₁ gc₂ : GClass}
    (hc : ClassAnnotationPrecision gct gc₁ gc₂) :
    gc₂.resolvedBases = gc₁.resolvedBases := by
  unfold ClassDecl.resolvedBases
  simp [hc.baseClasses_eq, hc.name_eq]

theorem gComputeMro_transport
    {gct₁ gct₂ : GClassTable}
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hc : ClassAnnotationPrecision gct₁ gc₁ gc₂)
    (h : GComputeMro gct₁ gc₁ mro) :
    GComputeMro gct₂ gc₂ mro :=
  -- Use `ComputeMro.rec` specialized to gradual classes.
  ComputeMro.rec
    (motive_1 := fun ct bases parentMros _ =>
      ClassTableAnnotationPrecision ct gct₂ → GAllParentMros gct₂ bases parentMros)
    (motive_2 := fun ct gc mro _ =>
      ∀ gc₂, ClassTableAnnotationPrecision ct gct₂ → ClassAnnotationPrecision ct gc gc₂ →
        GComputeMro gct₂ gc₂ mro)
    -- GAllParentMros.nil
    (fun _ => .nil)
    -- GAllParentMros.cons
    (fun hfind _hmro _hrest ih_mro ih_rest hct' =>
      let ⟨gc₂', hfind₂, hc'⟩ := findGClass_precision hct' hfind
      .cons hfind₂ (ih_mro gc₂' hct' hc') (ih_rest hct'))
    -- GComputeMro.root
    (fun hnil gc₂ _ hc' => by
      have hnil' : gc₂.resolvedBases = [] := by
        simpa [resolvedBases_eq_of_classAnnotationPrecision hc'] using hnil
      have hroot : GComputeMro gct₂ gc₂ [gc₂.name] := .root hnil'
      simpa [hc'.name_eq] using hroot)
    -- GComputeMro.step
    (fun {bases} {ct} {parentMros} {mergedSuffix} {c}
         hbases hne _hparents hmerge ih_parents gc₂ hct' hc' => by
      have hbases' : gc₂.resolvedBases = bases := by
        simpa [resolvedBases_eq_of_classAnnotationPrecision hc'] using hbases
      have hstep : GComputeMro gct₂ gc₂ (gc₂.name :: mergedSuffix) :=
        .step hbases' hne (ih_parents hct') hmerge
      simpa [hc'.name_eq] using hstep)
    h gc₂ hct hc

/-! ## Method-Type Lookup Transport -/

theorem findGMethodInMro_precision
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hfind : findGMethodInMro gct₁ mro mname = some m₁) :
    ∃ m₂,
      findGMethodInMro gct₂ mro mname = some m₂ ∧
      MethodAnnotationPrecision gct₁ m₁ m₂ :=
  findMemberInHierarchy_transport
    (findGClass_none_of_forall₂ hct)
    (findGClass_precision hct)
    (fun hgc => findGMethodInList_none_of_forall₂ hgc.methods_prec)
    (fun hgc => findGMethodInList_precision hgc.methods_prec)
    hfind

theorem findGMethodType_precision
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hfind : FindGMethodType gct₁ cname mname p₁ r₁) :
    ∃ p₂ r₂,
      FindGMethodType gct₂ cname mname p₂ r₂ ∧
      MoreStatic gct₁ p₁ p₂ ∧ MoreStatic gct₁ r₁ r₂ := by
  obtain ⟨c, mro, m, hfc, hmro, hfm, hpty, hrty⟩ := hfind
  obtain ⟨gc₂, hfc₂, hgc⟩ := findGClass_precision hct hfc
  obtain ⟨m₂, hfm₂, hm⟩ := findGMethodInMro_precision hct hfm
  exact ⟨m₂.paramTy, m₂.returnTy,
    ⟨gc₂, mro, m₂, hfc₂, gComputeMro_transport hct hgc hmro, hfm₂, rfl, rfl⟩,
    by simpa [hpty] using hm.paramTy_prec,
    by simpa [hrty] using hm.returnTy_prec⟩

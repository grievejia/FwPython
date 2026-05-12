import FwPython.Common.Forall2
import FwPython.Gradual.TypeSystem.ClassTable.Transport
import FwPython.Gradual.TypeSystem.CallParamTarget
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision

/-! # Structural Precision Through Checked-Target Images

Same-skeleton source-side precision stated directly through the explicit
checked-target image of method annotations. The static and dynamic GG entry
packages consume `ProgramTargetPrecision` together with the root-only
`ProgramRootTargetInputPrecision`. -/

namespace Checked

structure MethodTargetPrecision (m₁ m₂ : GMethod) : Prop where
  name_eq : m₁.name = m₂.name
  receiver_eq : m₁.receiverParam = m₂.receiverParam
  param_eq : m₁.param = m₂.param
  paramTy_prec : AnnotationTargetPrecision m₁.paramTy m₂.paramTy
  paramTy_callParam_prec :
    CompileTargetPrecision
      (callParamAnnotationTarget m₁.paramTy)
      (callParamAnnotationTarget m₂.paramTy)
  returnTy_prec : AnnotationTargetPrecision m₁.returnTy m₂.returnTy
  returnTy_callParam_prec :
    CompileTargetPrecision
      (callParamAnnotationTarget m₁.returnTy)
      (callParamAnnotationTarget m₂.returnTy)
  body_eq : m₁.body = m₂.body

structure ClassTargetPrecision (gc₁ gc₂ : GClass) : Prop where
  name_eq : gc₁.name = gc₂.name
  baseClasses_eq : gc₁.baseClasses = gc₂.baseClasses
  methods_prec : Forall₂ MethodTargetPrecision gc₁.methods gc₂.methods

abbrev ClassTableTargetPrecision (gct₁ gct₂ : GClassTable) : Prop :=
  Forall₂ ClassTargetPrecision gct₁ gct₂

structure ProgramTargetPrecision (gp₁ gp₂ : GProgram) : Prop where
  classes_prec : ClassTableTargetPrecision gp₁.classes gp₂.classes
  main_eq : gp₁.main = gp₂.main

theorem methodTargetPrecision_refl
    (m : GMethod) :
    MethodTargetPrecision m m :=
  ⟨rfl, rfl, rfl,
    annotationTargetPrecision_refl _,
    compileTargetPrecision_refl _,
    annotationTargetPrecision_refl _,
    compileTargetPrecision_refl _,
    rfl⟩

theorem classTargetPrecision_refl
    (gc : GClass) :
    ClassTargetPrecision gc gc :=
  ⟨rfl, rfl, forall₂_refl methodTargetPrecision_refl gc.methods⟩

theorem classTableTargetPrecision_refl
    (gct : GClassTable) :
    ClassTableTargetPrecision gct gct :=
  forall₂_refl classTargetPrecision_refl gct

theorem programTargetPrecision_refl
    (gp : GProgram) :
    ProgramTargetPrecision gp gp :=
  ⟨classTableTargetPrecision_refl gp.classes, rfl⟩

theorem methodTargetPrecision_trans
    (h₁ : MethodTargetPrecision m₁ m₂)
    (h₂ : MethodTargetPrecision m₂ m₃) :
    MethodTargetPrecision m₁ m₃ :=
  ⟨h₁.name_eq.trans h₂.name_eq,
    h₁.receiver_eq.trans h₂.receiver_eq,
    h₁.param_eq.trans h₂.param_eq,
    annotationTargetPrecision_trans h₁.paramTy_prec h₂.paramTy_prec,
    compileTargetPrecision_trans h₁.paramTy_callParam_prec h₂.paramTy_callParam_prec,
    annotationTargetPrecision_trans h₁.returnTy_prec h₂.returnTy_prec,
    compileTargetPrecision_trans h₁.returnTy_callParam_prec h₂.returnTy_callParam_prec,
    h₁.body_eq.trans h₂.body_eq⟩

theorem classTargetPrecision_trans
    (h₁ : ClassTargetPrecision c₁ c₂)
    (h₂ : ClassTargetPrecision c₂ c₃) :
    ClassTargetPrecision c₁ c₃ :=
  ⟨h₁.name_eq.trans h₂.name_eq,
    h₁.baseClasses_eq.trans h₂.baseClasses_eq,
    forall₂_trans (R := MethodTargetPrecision)
      (fun _ _ _ => methodTargetPrecision_trans) h₁.methods_prec h₂.methods_prec⟩

theorem classTableTargetPrecision_trans
    (h₁ : ClassTableTargetPrecision gct₁ gct₂)
    (h₂ : ClassTableTargetPrecision gct₂ gct₃) :
    ClassTableTargetPrecision gct₁ gct₃ :=
  forall₂_trans (R := ClassTargetPrecision)
    (fun _ _ _ => classTargetPrecision_trans) h₁ h₂

theorem programTargetPrecision_trans
    (h₁ : ProgramTargetPrecision gp₁ gp₂)
    (h₂ : ProgramTargetPrecision gp₂ gp₃) :
    ProgramTargetPrecision gp₁ gp₃ :=
  ⟨classTableTargetPrecision_trans h₁.classes_prec h₂.classes_prec,
    h₁.main_eq.trans h₂.main_eq⟩

theorem methodTargetPrecision_to_methodAnnotationPrecision
    (gct : GClassTable)
    (h : MethodTargetPrecision m₁ m₂) :
    MethodAnnotationPrecision gct m₁ m₂ :=
  ⟨h.name_eq, h.receiver_eq, h.param_eq,
    annotationTargetPrecision_sound (gct := gct) h.paramTy_prec,
    annotationTargetPrecision_sound (gct := gct) h.returnTy_prec,
    h.body_eq⟩

theorem classTargetPrecision_to_classAnnotationPrecision
    (gct : GClassTable)
    (h : ClassTargetPrecision gc₁ gc₂) :
    ClassAnnotationPrecision gct gc₁ gc₂ :=
  ⟨h.name_eq, h.baseClasses_eq,
    forall₂_imp
      (fun _ _ hm => methodTargetPrecision_to_methodAnnotationPrecision gct hm)
      h.methods_prec⟩

theorem classTableTargetPrecision_to_classTableAnnotationPrecision
    (h : ClassTableTargetPrecision gct₁ gct₂) :
    ClassTableAnnotationPrecision gct₁ gct₂ :=
  forall₂_imp
    (fun _ _ hc => classTargetPrecision_to_classAnnotationPrecision gct₁ hc)
    h

theorem programTargetPrecision_to_programAnnotationPrecision
    (h : ProgramTargetPrecision gp₁ gp₂) :
    ProgramAnnotationPrecision gp₁ gp₂ :=
  ⟨classTableTargetPrecision_to_classTableAnnotationPrecision h.classes_prec, h.main_eq⟩

private theorem findGClass_none_of_classTableTargetPrecision
    (hct : Forall₂ ClassTargetPrecision gcs₁ gcs₂)
    (h : findGClass gcs₁ cname = none) :
    findGClass gcs₂ cname = none :=
  findByName_none_of_forall₂ (fun hc => hc.name_eq) hct h

private theorem findGMethodInList_none_of_methodTargetPrecision
    (hms : Forall₂ MethodTargetPrecision ms₁ ms₂)
    (h : findGMethodInList ms₁ mname = none) :
    findGMethodInList ms₂ mname = none :=
  findByName_none_of_forall₂ (fun hm => hm.name_eq) hms h

private theorem findGClass_targetPrecision
    (hct : Forall₂ ClassTargetPrecision gcs₁ gcs₂)
    (hfind : findGClass gcs₁ cname = some gc₁) :
    ∃ gc₂,
      findGClass gcs₂ cname = some gc₂ ∧
      ClassTargetPrecision gc₁ gc₂ :=
  findByName_some_of_forall₂ (fun hc => hc.name_eq) hct hfind

private theorem findGMethodInList_targetPrecision
    (hms : Forall₂ MethodTargetPrecision ms₁ ms₂)
    (hfind : findGMethodInList ms₁ mname = some m₁) :
    ∃ m₂,
      findGMethodInList ms₂ mname = some m₂ ∧
      MethodTargetPrecision m₁ m₂ :=
  findByName_some_of_forall₂ (fun hm => hm.name_eq) hms hfind

private theorem gComputeMro_targetTransport
    (hct : ClassTableTargetPrecision gct₁ gct₂)
    (hc : ClassTargetPrecision gc₁ gc₂)
    (h : GComputeMro gct₁ gc₁ mro) :
    GComputeMro gct₂ gc₂ mro :=
  gComputeMro_transport
    (classTableTargetPrecision_to_classTableAnnotationPrecision hct)
    (classTargetPrecision_to_classAnnotationPrecision gct₁ hc)
    h

private theorem findGMethodInMro_targetPrecision
    (hct : ClassTableTargetPrecision gct₁ gct₂)
    (hfind : findGMethodInMro gct₁ mro mname = some m₁) :
    ∃ m₂,
      findGMethodInMro gct₂ mro mname = some m₂ ∧
      MethodTargetPrecision m₁ m₂ :=
  findMemberInHierarchy_transport
    (findGClass_none_of_classTableTargetPrecision hct)
    (findGClass_targetPrecision hct)
    (fun hgc => findGMethodInList_none_of_methodTargetPrecision hgc.methods_prec)
    (fun hgc => findGMethodInList_targetPrecision hgc.methods_prec)
    hfind

theorem findGMethodType_targetPrecision
    (hct : ClassTableTargetPrecision gct₁ gct₂)
    (hfind : FindGMethodType gct₁ cname mname p₁ r₁) :
    ∃ p₂ r₂,
      FindGMethodType gct₂ cname mname p₂ r₂ ∧
      AnnotationTargetPrecision p₁ p₂ ∧
      AnnotationTargetPrecision r₁ r₂ ∧
      CompileTargetPrecision
        (callParamAnnotationTarget r₁)
        (callParamAnnotationTarget r₂) := by
  obtain ⟨c, mro, m, hfc, hmro, hfm, rfl, rfl⟩ := hfind
  obtain ⟨gc₂, hfc₂, hgc⟩ := findGClass_targetPrecision hct hfc
  obtain ⟨m₂, hfm₂, hm⟩ := findGMethodInMro_targetPrecision hct hfm
  exact ⟨m₂.paramTy, m₂.returnTy,
    ⟨gc₂, mro, m₂, hfc₂, gComputeMro_targetTransport hct hgc hmro, hfm₂, rfl, rfl⟩,
    hm.paramTy_prec, hm.returnTy_prec, hm.returnTy_callParam_prec⟩

end Checked

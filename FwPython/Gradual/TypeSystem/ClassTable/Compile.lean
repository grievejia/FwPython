import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.Safety
import FwPython.Common.Forall2

/-! # Canonical checked class table compilation

Defines explicit front-end compilation correspondence between a gradual
class table and a checked class table. Checked method signatures record
the machine-facing projection `runtimePublicTy` of gradual annotations,
and checked method bodies are required to be exactly `compileCheck` of a
source typing witness under the runtime's first-match method-body
environment order `[param, receiver]`. -/

namespace Checked

/-! ## Structural correspondence -/

structure IsCompiledMethodAt
    (gct : GClassTable) (cname : Identifier)
    (gm : GMethod) (cm : CheckedMethod) : Prop where
  name_eq : cm.name = gm.name
  receiverParam_eq : cm.receiverParam = gm.receiverParam
  param_eq : cm.param = gm.param
  paramTy_eq : cm.paramTy = gm.paramTy
  returnTy_eq : cm.returnTy = gm.returnTy
  paramContract_eq : cm.parameterContract = compileBoundaryRaw cm.paramTy
  returnContract_eq : cm.returnContract = compileBoundaryRaw cm.returnTy
  parameterLabels_eq :
    cast (by simpa [paramTy_eq] using congrArg BoundaryLabels paramContract_eq) cm.parameterLabels =
      (mkBoundaryLabels (.methodParameter cname gm.name) .negative
        (compileBoundaryRaw gm.paramTy) 0).1
  returnLabels_eq :
    cast (by simpa [returnTy_eq] using congrArg BoundaryLabels returnContract_eq) cm.returnLabels =
      (mkBoundaryLabels (.methodReturn cname gm.name) .positive
        (compileBoundaryRaw gm.returnTy) 0).1
  body_compiled :
    ∃ hwfct : WellFormedGClassTableCore gct,
      ∃ srcTy,
      ∃ hsrc : GSrcInfer gct hwfct
        [{ name := gm.param, sourceTy := gm.paramTy },
         { name := gm.receiverParam, sourceTy := .class_ cname }]
        gm.body
        srcTy,
      cm.body =
        (compileCheck (.methodBody cname gm.name) hsrc
          [(gm.param, gm.paramTy),
           (gm.receiverParam, .class_ cname)]
          gm.returnTy
          0).1

structure IsCompiledClass
    (gct : GClassTable) (gc : GClass) (cc : CheckedClass) : Prop where
  name_eq : cc.name = gc.name
  baseClasses_eq : cc.baseClasses = gc.baseClasses
  methods_compiled : Forall₂ (IsCompiledMethodAt gct gc.name) gc.methods cc.methods

def IsCompiledClassTable (gct : GClassTable) (cct : CheckedClassTable) : Prop :=
  Forall₂ (IsCompiledClass gct) gct cct

structure ElaboratesProgramAt
    (gp : GProgram) (P : GTy) (cp : CheckedProgram) where
  classes_elab : IsCompiledClassTable gp.classes cp.classes
  hwfct : WellFormedGClassTableCore gp.classes
  main_srcTy : GTy
  main_hsrc : GSrcInfer gp.classes hwfct [] gp.main main_srcTy
  main_eq : cp.main = (compileCheck .main main_hsrc [] P 0).1
  target_runtimePublic : RuntimePublicAnnotation gp.classes P
  target_wf : WellFormedGTy gp.classes P

theorem ElaboratesProgramAt.main_elabCheck
    (hcompiled : ElaboratesProgramAt gp P cp) :
    ElabCheck .main hcompiled.main_hsrc [] P 0 cp.main
      (compileCheck .main hcompiled.main_hsrc [] P 0).2 :=
  hcompiled.main_eq ▸ compileCheck_elaborates

/-! ## Lookup correspondence -/

theorem isCompiledClassTable_findClass
    (hct : Forall₂ (IsCompiledClass gct) gclasses cclasses)
    (hfind : findGClass gclasses cname = some gc) :
    ∃ cc, findCheckedClass cclasses cname = some cc ∧ IsCompiledClass gct gc cc := by
  induction hct with
  | nil =>
      have : False := by
        simp [findGClass, findClass, findByName] at hfind
      exact False.elim this
  | @cons gc' cc' gclasses cclasses hc _ ih =>
      by_cases hname : gc'.name = cname
      · have hhead : findGClass (gc' :: gclasses) cname = some gc' := by
          simp [findGClass, findClass, findByName, hname]
        rw [hhead] at hfind
        cases hfind
        have hcchead : findCheckedClass (cc' :: cclasses) cname = some cc' := by
          have hccname : cc'.name = cname := hc.name_eq.trans hname
          simp [findCheckedClass, findByName, hccname]
        exact ⟨cc', hcchead, hc⟩
      · have hccneq : cc'.name ≠ cname := by
          intro hEq
          exact hname (hc.name_eq.symm.trans hEq)
        have htail : findGClass gclasses cname = some gc := by
          simpa [findGClass, findClass, findByName, hname] using hfind
        obtain ⟨cc, hfindc, hcc⟩ := ih htail
        exact ⟨cc, by simpa [findCheckedClass, findByName, hccneq] using hfindc, hcc⟩

private theorem isCompiledClassTable_findClass_none
    (hct : Forall₂ (IsCompiledClass gct) gclasses cclasses)
    (hfind : findGClass gclasses cname = none) :
    findCheckedClass cclasses cname = none := by
  induction hct with
  | nil =>
      rfl
  | @cons gc' cc' gclasses cclasses hc _ ih =>
      by_cases hname : gc'.name = cname
      · have hhead : findGClass (gc' :: gclasses) cname = some gc' := by
          simp [findGClass, findClass, findByName, hname]
        rw [hhead] at hfind
        cases hfind
      · have hccneq : cc'.name ≠ cname := by
          intro hEq
          exact hname (hc.name_eq.symm.trans hEq)
        have htail : findGClass gclasses cname = none := by
          simpa [findGClass, findClass, findByName, hname] using hfind
        simpa [findCheckedClass, findByName, hccneq] using ih htail

private theorem isCompiledClassTable_findClass_reverse
    (hct : Forall₂ (IsCompiledClass gct) gclasses cclasses)
    (hfind : findCheckedClass cclasses cname = some cc) :
    ∃ gc, findGClass gclasses cname = some gc ∧ IsCompiledClass gct gc cc := by
  by_cases hnone : findGClass gclasses cname = none
  · have : findCheckedClass cclasses cname = none :=
      isCompiledClassTable_findClass_none hct hnone
    rw [this] at hfind
    cases hfind
  · cases hfindg : findGClass gclasses cname with
    | none =>
        contradiction
    | some gc =>
        obtain ⟨cc', hfindc, hcc⟩ := isCompiledClassTable_findClass hct hfindg
        rw [hfindc] at hfind
        cases hfind
        exact ⟨gc, rfl, hcc⟩

private theorem isCompiledMethods_findMethod
    (hms : Forall₂ (IsCompiledMethodAt gct cname) gms cms)
    (hfind : findGMethodInList gms mname = some gm) :
    ∃ cm, findCheckedMethodInList cms mname = some cm ∧
      IsCompiledMethodAt gct cname gm cm := by
  induction hms with
  | nil =>
      have : False := by
        simp [findGMethodInList, findMethodInList, findByName] at hfind
      exact False.elim this
  | @cons gm' cm' gms cms hm _ ih =>
      by_cases hname : gm'.name = mname
      · have hhead : findGMethodInList (gm' :: gms) mname = some gm' := by
          simp [findGMethodInList, findMethodInList, findByName, hname]
        rw [hhead] at hfind
        cases hfind
        have hcmhead : findCheckedMethodInList (cm' :: cms) mname = some cm' := by
          have hcmname : cm'.name = mname := hm.name_eq.trans hname
          simp [findCheckedMethodInList, findByName, hcmname]
        exact ⟨cm', hcmhead, hm⟩
      · have hcmneq : cm'.name ≠ mname := by
          intro hEq
          exact hname (hm.name_eq.symm.trans hEq)
        have htail : findGMethodInList gms mname = some gm := by
          simpa [findGMethodInList, findMethodInList, findByName, hname] using hfind
        obtain ⟨cm, hfindc, hmc⟩ := ih htail
        exact ⟨cm, by simpa [findCheckedMethodInList, findByName, hcmneq] using hfindc, hmc⟩

private theorem isCompiledMethods_findMethod_none
    (hms : Forall₂ (IsCompiledMethodAt gct cname) gms cms)
    (hfind : findGMethodInList gms mname = none) :
    findCheckedMethodInList cms mname = none := by
  induction hms with
  | nil =>
      rfl
  | @cons gm' cm' gms cms hm _ ih =>
      by_cases hname : gm'.name = mname
      · have hhead : findGMethodInList (gm' :: gms) mname = some gm' := by
          simp [findGMethodInList, findMethodInList, findByName, hname]
        rw [hhead] at hfind
        cases hfind
      · have hcmneq : cm'.name ≠ mname := by
          intro hEq
          exact hname (hm.name_eq.symm.trans hEq)
        have htail : findGMethodInList gms mname = none := by
          simpa [findGMethodInList, findMethodInList, findByName, hname] using hfind
        simpa [findCheckedMethodInList, findByName, hcmneq] using ih htail

theorem isCompiledClassTable_findMethodInMro
    (hct : IsCompiledClassTable gct cct)
    (hfind : findGMethodInMro gct mro mname = some gm) :
    ∃ cm, findCheckedMethodInMro cct mro mname = some cm ∧
      ∃ dname, IsCompiledMethodAt gct dname gm cm :=
  findMemberInHierarchy_transport
    (RClass := fun gc cc => IsCompiledClass gct gc cc)
    (RMember := fun gm cm => ∃ dname, IsCompiledMethodAt gct dname gm cm)
    (isCompiledClassTable_findClass_none hct)
    (isCompiledClassTable_findClass hct)
    (fun hgc hnone => isCompiledMethods_findMethod_none hgc.methods_compiled hnone)
    (fun hgc hsome => by
      obtain ⟨cm, hfcm, hmc⟩ := isCompiledMethods_findMethod hgc.methods_compiled hsome
      exact ⟨cm, hfcm, _, hmc⟩)
    hfind

/-! ## Membership and provenance helpers -/

theorem forall₂_mem_right {R : α → β → Prop}
    (hf : Forall₂ R as bs) (hmem : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction hf with
  | nil => cases hmem
  | cons hr _ ih =>
    cases hmem with
    | head => exact ⟨_, .head _, hr⟩
    | tail _ h =>
      obtain ⟨a, ha, hr⟩ := ih h
      exact ⟨a, .tail _ ha, hr⟩

theorem forall₂_mem_left {R : α → β → Prop}
    (hf : Forall₂ R as bs) (hmem : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction hf with
  | nil => cases hmem
  | cons hr _ ih =>
      cases hmem with
      | head => exact ⟨_, .head _, hr⟩
      | tail _ h =>
          obtain ⟨b, hb, hr⟩ := ih h
          exact ⟨b, .tail _ hb, hr⟩

theorem traceMethodToSource
    (hcompiled : IsCompiledClassTable gct cct)
    (hfc : findCheckedClass cct cname = some cc)
    (hmem : cm ∈ cc.methods) :
    ∃ gc gm, findGClass gct cname = some gc ∧
      gm ∈ gc.methods ∧ IsCompiledMethodAt gct cname gm cm := by
  obtain ⟨gc, hfg, hgc⟩ := isCompiledClassTable_findClass_reverse hcompiled hfc
  obtain ⟨gm, hgm, hmc⟩ := forall₂_mem_right hgc.methods_compiled hmem
  refine ⟨gc, gm, hfg, hgm, ?_⟩
  simpa [findGClass_name hfg] using hmc

theorem findCheckedClass_functional
    (hfind₁ : findCheckedClass cct cname = some cc₁)
    (hfind₂ : findCheckedClass cct cname = some cc₂) :
    cc₁ = cc₂ := by
  rw [hfind₁] at hfind₂; cases hfind₂; rfl

theorem checkedClass_lookup_to_source
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hfc : findCheckedClass cp.classes cname = some cc) :
    ∃ gc, findGClass gp.classes cname = some gc ∧ IsCompiledClass gp.classes gc cc :=
  isCompiledClassTable_findClass_reverse hcompiled.classes_elab hfc

theorem compiledMethod_named_unique
    (hwfct : WellFormedGClassTableCore gp.classes)
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hfc : findCheckedClass cp.classes dname = some cc)
    (hmem₁ : cm₁ ∈ cc.methods)
    (hmem₂ : cm₂ ∈ cc.methods)
    (hcm₁ : IsCompiledMethodAt gp.classes dname gm₁ cm₁)
    (hcm₂ : IsCompiledMethodAt gp.classes dname gm₂ cm₂)
    (hname : gm₁.name = gm₂.name) :
    cm₁ = cm₂ := by
  obtain ⟨gc, hfg, hgc⟩ := checkedClass_lookup_to_source hcompiled hfc
  have hnodupSrc : List.Nodup (gc.methods.map MethodDecl.name) :=
    hwfct.allMethodNamesDistinct _ _ hfg
  have hnames :
      gc.methods.map MethodDecl.name =
        cc.methods.map CheckedMethod.name :=
    forall₂_map_eq (fun gm cm h => by simp [h.name_eq]) hgc.methods_compiled
  have hnodupChecked : List.Nodup (cc.methods.map CheckedMethod.name) :=
    hnames ▸ hnodupSrc
  have hcmName : cm₁.name = cm₂.name :=
    hcm₁.name_eq.trans (hname.trans hcm₂.name_eq.symm)
  exact findCheckedMethodInList_unique hnodupChecked hmem₁ hmem₂ hcmName

/-! ## Main alignment theorem -/

theorem alignedCheckedClassTable_of_compiled
    (hwfct : WellFormedGClassTableCore gct)
    (hcompiled : IsCompiledClassTable gct cct) :
    AlignedCheckedClassTable gct cct where
  classLookupAgree := fun _ _ hfg => by
    obtain ⟨cc, hfc, hgc⟩ := isCompiledClassTable_findClass hcompiled hfg
    exact ⟨cc, hfc, hgc.name_eq, hgc.baseClasses_eq⟩
  methodLookupAgree := fun _ _ _ _ _ _ _ _ hfgm => by
    obtain ⟨cm, hfcm, _, hmc⟩ := isCompiledClassTable_findMethodInMro hcompiled hfgm
    exact ⟨cm, hfcm, hmc.paramTy_eq, hmc.returnTy_eq,
      hmc.paramTy_eq ▸ hmc.paramContract_eq, hmc.returnTy_eq ▸ hmc.returnContract_eq⟩
  methodBodiesTyped := fun cname cc cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, hmc⟩ := traceMethodToSource hcompiled hfc hmem
    obtain ⟨hparamWf, hretWf⟩ := hwfct.allMethodSignaturesWellFormed _ _ _ hfg hgm
    obtain ⟨hparamRt, hretRt⟩ := hwfct.allMethodSignaturesRuntimePublic _ _ _ hfg hgm
    have hclassWf : WellFormedGTy gct (.class_ cname) :=
      classTy_wellFormed_of_findGClass hwfct hfg
    have hclassRt : RuntimePublicAnnotation gct (.class_ cname) :=
      runtimePublicAnnotation_mk (CheckedTargetTy.classFormula FormulaGTy.class_)
    have hsrcEnv :
        SourceEnvOk gct
          [{ name := gm.param, sourceTy := gm.paramTy },
           { name := gm.receiverParam, sourceTy := .class_ cname }] := by
      intro b hb
      simp at hb
      rcases hb with rfl | rfl
      · exact ⟨runtimePublicAnnotation_to_sourceCallableTy _ hparamRt, hparamWf⟩
      · exact ⟨.class_, hclassWf⟩
    have helab :
        ElabEnvOk gct
          [{ name := gm.param, sourceTy := gm.paramTy },
           { name := gm.receiverParam, sourceTy := .class_ cname }]
          [(gm.param, gm.paramTy),
           (gm.receiverParam, .class_ cname)] :=
      .cons
        { name_eq := rfl, checked_target := hparamRt,
          checked_wf := hparamWf,
          source_sub_checked := gradualSubtype_refl gct gm.paramTy }
        (.cons
          { name_eq := rfl, checked_target := hclassRt,
            checked_wf := hclassWf,
            source_sub_checked := gradualSubtype_refl gct (.class_ cname) }
          .nil)
    obtain ⟨hwfctMethod, srcTy, hsrc, hbody⟩ := hmc.body_compiled
    simpa [hmc.param_eq, hmc.receiverParam_eq, hmc.paramTy_eq, hmc.returnTy_eq, hbody,
      runtimePublicTy_id] using
      compileCheck_checked (.methodBody cname gm.name) hsrcEnv helab hwfctMethod hretRt hretWf hsrc
  methodSignaturesWellFormed := fun cname _ cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, hmc⟩ := traceMethodToSource hcompiled hfc hmem
    have ⟨p, r⟩ := hwfct.allMethodSignaturesWellFormed _ _ _ hfg hgm
    exact ⟨hmc.paramTy_eq ▸ p, hmc.returnTy_eq ▸ r⟩
  methodContractsCompiled := fun _ _ cm hfc hmem => by
    obtain ⟨_, _, _, _, hmc⟩ := traceMethodToSource hcompiled hfc hmem
    exact ⟨hmc.paramContract_eq, hmc.returnContract_eq⟩
  methodSignaturesRuntimePublic := fun cname _ cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, hmc⟩ := traceMethodToSource hcompiled hfc hmem
    have ⟨p, r⟩ := hwfct.allMethodSignaturesRuntimePublic _ _ _ hfg hgm
    exact ⟨
      ⟨runtimePublicCheckedTargetShape_all _,
        by simpa [hmc.paramTy_eq] using runtimePublicAnnotation_checked p⟩,
      ⟨runtimePublicCheckedTargetShape_all _,
        by simpa [hmc.returnTy_eq] using runtimePublicAnnotation_checked r⟩⟩

end Checked

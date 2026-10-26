import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.Safety
import FwPython.Common.Forall2

/-! # Canonical checked class table compilation

Defines explicit front-end compilation correspondence between a gradual
class table and a checked class table. Checked method signatures record
the machine-facing checked-target image of gradual annotations,
and checked method bodies are compiled at neutral target `any` under the
runtime's first-match method-body environment order `[param, receiver]`.
The runtime method-return frame enforces the declared return boundary. -/

namespace Checked

/-! ## Structural correspondence -/

/-- Data-bearing compilation artifact for one source method at a concrete source
class name. -/
structure IsCompiledMethodAt
    (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct)
    (cname : Identifier)
    (gm : GMethod) (cm : CheckedMethod) : Type where
  /-- Preserve the method name from source to checked method. -/
  name_eq : cm.name = gm.name
  /-- Preserve the receiver parameter name. -/
  receiverParam_eq : cm.receiverParam = gm.receiverParam
  /-- Preserve the explicit argument parameter name. -/
  param_eq : cm.param = gm.param
  /-- The checked method parameter target is `checkedTargetOfGTy gm.paramTy`. -/
  paramTy_eq : cm.paramTy = checkedTargetOfGTy gm.paramTy
  /-- The checked method return target is `checkedTargetOfGTy gm.returnTy`. -/
  returnTy_eq : cm.returnTy = checkedTargetOfGTy gm.returnTy
  /-- The stored parameter obligation is the source method-parameter type obligation. -/
  parameterObligation_eq :
    cm.parameterObligation =
      .hasType (.methodParameter cname gm.name) gm.paramTy
  /-- The stored return obligation is the source method-return type obligation. -/
  returnObligation_eq :
    cm.returnObligation =
      .hasType (.methodReturn cname gm.name) gm.returnTy
  /-- The source type synthesized for the method body. -/
  body_srcTy : GTy
  /-- The source typing witness for compiling the checked method body. -/
  body_hsrc : GSrcInfer gct hwfct
    [{ name := gm.param, sourceTy := gm.paramTy },
     { name := gm.receiverParam, sourceTy := .class_ cname }]
    gm.body
    body_srcTy
  /-- The stored checked body is compiled at neutral target `any`; the
  method-return frame enforces `gm.returnTy` after the body produces a value. -/
  body_eq :
    cm.body =
      (compileCheck body_hsrc
        [(gm.param, gm.paramTy), (gm.receiverParam, .class_ cname)]
        .any
        (.methodBody cname gm.name []))

/-- Interpreting the checked parameter and return targets reproduces the source
method's parameter and return types — a direct consequence of `paramTy_eq` and
`returnTy_eq`. -/
theorem IsCompiledMethodAt.interpTargets
    (hmc : IsCompiledMethodAt gct hwfct cname gm cm) :
    interpTarget cm.paramTy = gm.paramTy ∧
    interpTarget cm.returnTy = gm.returnTy :=
  ⟨hmc.paramTy_eq ▸ interpTarget_checkedTargetOfGTy _,
   hmc.returnTy_eq ▸ interpTarget_checkedTargetOfGTy _⟩

/-- Data-bearing compilation artifact for one source class and checked class. -/
structure IsCompiledClass
    (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct)
    (gc : GClass) (cc : CheckedClass) : Type where
  /-- Preserve the class name from source to checked class. -/
  name_eq : cc.name = gc.name
  /-- Preserve the declared base-class list. -/
  baseClasses_eq : cc.baseClasses = gc.baseClasses
  /-- Data-bearing pointwise correspondence between source methods and checked methods. -/
  methods_compiled :
    Forall2Data (IsCompiledMethodAt gct hwfct gc.name) gc.methods cc.methods

/-- Data-bearing pointwise compilation artifact for a source and checked class table. -/
def IsCompiledClassTable
    (gct : GClassTable) (hwfct : WellFormedGClassTableCore gct)
    (cct : CheckedClassTable) : Type :=
  Forall2Data (IsCompiledClass gct hwfct) gct cct

/-- Checked elaboration artifact for a whole gradual program at a requested target. -/
structure ElaboratesProgramAt
    (gp : GProgram) (P : GTy) (cp : CheckedProgram) where
  /-- The well-formedness witness used by class-table and main-expression compilation. -/
  hwfct : WellFormedGClassTableCore gp.classes
  /-- Data-bearing compilation artifact for the program class table under `hwfct`. -/
  classes_elab : IsCompiledClassTable gp.classes hwfct cp.classes
  /-- The source type synthesized for the program main expression. -/
  main_srcTy : GTy
  /-- The source typing witness for compiling the main expression. -/
  main_hsrc : GSrcInfer gp.classes hwfct [] gp.main main_srcTy
  /-- The checked program main is the compiler-produced checked expression for
  `main_hsrc`. -/
  main_eq : cp.main = compileCheck main_hsrc [] P (.main [])
  /-- The requested program target is representable as a checked runtime target. -/
  target_checkedTarget : CheckedTargetTy gp.classes P
  /-- The requested program target is well formed for the gradual class table. -/
  target_wf : WellFormedGTy gp.classes P

/-! ## Lookup correspondence -/

/-- Transport a successful source class lookup to the compiled checked class,
where `value` is the checked class, `found` is the checked lookup equality, and
`related` is the class compilation artifact. -/
def isCompiledClassTable_findClass
    (hct : IsCompiledClassTable gct hwfct cct)
    (hfind : findGClass gct cname = some gc) :
    FindByNameForwardData
      (IsCompiledClass gct hwfct)
      CheckedClass.name
      cct
      cname
      gc :=
  findByName_some_of_forall2Data
    (R := IsCompiledClass gct hwfct)
    (getName₁ := ClassDecl.name)
    (getName₂ := CheckedClass.name)
    (fun h => h.name_eq.symm)
    hct
    hfind

/-- Transport a failed source class lookup to the checked class table. -/
theorem isCompiledClassTable_findClass_none
    (hct : IsCompiledClassTable gct hwfct cct)
    (hfind : findGClass gct cname = none) :
    findCheckedClass cct cname = none :=
  findByName_none_of_forall2Data
    (R := IsCompiledClass gct hwfct)
    (getName₁ := ClassDecl.name)
    (getName₂ := CheckedClass.name)
    (fun h => h.name_eq.symm)
    hct
    hfind

/-- Transport a successful checked class lookup back to the source class, where
`value` is the source class, `found` is the source lookup equality, and
`related` is the class compilation artifact. -/
def checkedClass_lookup_to_source
    (hct : IsCompiledClassTable gct hwfct cct)
    (hfc : findCheckedClass cct cname = some cc) :
    FindByNameReverseData
      (IsCompiledClass gct hwfct)
      ClassDecl.name
      gct
      cname
      cc :=
  findByName_some_right_of_forall2Data
    (R := IsCompiledClass gct hwfct)
    (getName₁ := ClassDecl.name)
    (getName₂ := CheckedClass.name)
    (fun h => h.name_eq.symm)
    hct
    hfc

/-- Transport a successful source method lookup to the compiled checked method,
where `value` is the checked method, `found` is the checked lookup equality, and
`related` is the method compilation artifact. -/
def isCompiledMethods_findMethod
    (hms : Forall2Data (IsCompiledMethodAt gct hwfct cname) gms cms)
    (hfind : findGMethodInList gms mname = some gm) :
    FindByNameForwardData
      (IsCompiledMethodAt gct hwfct cname)
      CheckedMethod.name
      cms
      mname
      gm :=
  findByName_some_of_forall2Data
    (R := IsCompiledMethodAt gct hwfct cname)
    (getName₁ := MethodDecl.name)
    (getName₂ := CheckedMethod.name)
    (fun h => h.name_eq.symm)
    hms
    hfind

/-- Transport a failed source method lookup to the checked method list. -/
theorem isCompiledMethods_findMethod_none
    (hms : Forall2Data (IsCompiledMethodAt gct hwfct cname) gms cms)
    (hfind : findGMethodInList gms mname = none) :
    findCheckedMethodInList cms mname = none :=
  findByName_none_of_forall2Data
    (R := IsCompiledMethodAt gct hwfct cname)
    (getName₁ := MethodDecl.name)
    (getName₂ := CheckedMethod.name)
    (fun h => h.name_eq.symm)
    hms
    hfind

/-- Transport a successful source MRO method lookup to the checked MRO while
preserving the source class name that supplied the method artifact. The returned
Common lookup data stores the checked method in `member2`, the checked MRO
lookup equality in `found`, and the `IsCompiledMethodAt` artifact in
`related`. -/
def isCompiledClassTable_findMethodInMro
    (hct : IsCompiledClassTable gct hwfct cct)
    (hfind : findGMethodInMro gct mro mname = some gm) :
    RelatedHierarchyLookupData
      findCheckedClass
      CheckedClass.methods
      CheckedMethod.name
      cct
      mro
      mname
      (fun definingClassName gm cm =>
        IsCompiledMethodAt gct hwfct definingClassName gm cm)
      gm :=
  findMemberInHierarchy_transportData
    (findClass₁ := findGClass)
    (findClass₂ := findCheckedClass)
    (getMembers₁ := ClassDecl.methods)
    (getMembers₂ := CheckedClass.methods)
    (getName₁ := MethodDecl.name)
    (getName₂ := CheckedMethod.name)
    (ct₁ := gct)
    (ct₂ := cct)
    (memberName := mname)
    mro
    (isCompiledClassTable_findClass_none hct)
    (fun hfindClass =>
      let lookup := isCompiledClassTable_findClass hct hfindClass
      { class2 := lookup.value,
        found := lookup.found,
        related := lookup.related })
    (fun hclass hnone => isCompiledMethods_findMethod_none hclass.methods_compiled hnone)
    (fun {cname gc cc gm} hclass hfindClass hfindMethod =>
      let lookup := isCompiledMethods_findMethod hclass.methods_compiled hfindMethod
      { member2 := lookup.value,
        found := lookup.found,
        related := by
          simpa [findGClass_name hfindClass] using lookup.related })
    hfind

/-! ## Membership and provenance helpers -/

/-- Project checked method membership back to a source class, source method, and
nonempty method compilation artifact. This theorem is Prop-valued because its
position witness is list membership. -/
theorem traceMethodToSource
    (hcompiled : IsCompiledClassTable gct hwfct cct)
    (hfc : findCheckedClass cct cname = some cc)
    (hmem : cm ∈ cc.methods) :
    ∃ sourceClass sourceMethod,
      findGClass gct cname = some sourceClass ∧
      sourceMethod ∈ sourceClass.methods ∧
      Nonempty (IsCompiledMethodAt gct hwfct cname sourceMethod cm) := by
  let classLookup := checkedClass_lookup_to_source hcompiled hfc
  obtain ⟨sourceMethod, hmethodMem, hmethod⟩ :=
    forall2Data_mem_right_exists classLookup.related.methods_compiled hmem
  refine ⟨classLookup.value, sourceMethod, classLookup.found, hmethodMem, ?_⟩
  exact hmethod.elim (fun h => ⟨findGClass_name classLookup.found ▸ h⟩)

/-- A data-bearing class-table compilation artifact establishes the checked
runtime alignment invariant consumed by safety and soundness. -/
theorem alignedCheckedClassTable_of_compiled
    (hcompiled : IsCompiledClassTable gct hwfct cct) :
    AlignedCheckedClassTable gct hwfct.toWellFormedClassHierarchy cct where
  classLookupAgree := fun _ _ hfg => by
    let lookup := isCompiledClassTable_findClass hcompiled hfg
    exact ⟨lookup.value, lookup.found, lookup.related.name_eq,
      lookup.related.baseClasses_eq⟩
  methodLookupAgree := fun _ _ _ _ _ _ _ _ hfgm => by
    let lookup := isCompiledClassTable_findMethodInMro hcompiled hfgm
    have ⟨hpEq, hrEq⟩ := lookup.related.interpTargets
    exact ⟨lookup.member2, lookup.found, hpEq, hrEq⟩
  methodBodiesTyped := fun cname cc cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, ⟨hmc⟩⟩ := traceMethodToSource hcompiled hfc hmem
    obtain ⟨hparamWf, _hretWf⟩ := hwfct.allMethodSignaturesWellFormed _ _ _ hfg hgm
    obtain ⟨hparamRt, _hretRt⟩ := hwfct.allMethodSignaturesCheckedTarget _ _ _ hfg hgm
    have hclassWf : WellFormedGTy gct (.class_ cname) :=
      classTy_wellFormed_of_findGClass hwfct hfg
    have hclassRt : CheckedTargetTy gct (.class_ cname) :=
      CheckedTargetTy.classFormula FormulaGTy.class_
    have helab :
        ElabEnvOk gct hwfct.toWellFormedClassHierarchy
          [{ name := gm.param, sourceTy := gm.paramTy },
           { name := gm.receiverParam, sourceTy := .class_ cname }]
          [(gm.param, gm.paramTy),
           (gm.receiverParam, .class_ cname)] :=
      .cons
        { name_eq := rfl, checked_target := hparamRt,
          checked_wf := hparamWf,
          source_sub_checked := gradualSubtype_refl gct hwfct.toWellFormedClassHierarchy gm.paramTy
            hparamWf }
        (.cons
          { name_eq := rfl, checked_target := hclassRt,
            checked_wf := hclassWf,
            source_sub_checked := gradualSubtype_refl gct hwfct.toWellFormedClassHierarchy (.class_ cname)
              hclassWf }
          .nil)
    simpa [hmc.body_eq, hmc.param_eq, hmc.receiverParam_eq,
      hmc.paramTy_eq, hmc.returnTy_eq, interpTarget_checkedTargetOfGTy] using
      compileCheck_checked hwfct helab (.classFormula .any) .any hmc.body_hsrc
        (.methodBody cname gm.name [])
  methodSignaturesWellFormed := fun cname _ cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, ⟨hmc⟩⟩ := traceMethodToSource hcompiled hfc hmem
    have ⟨p, r⟩ := hwfct.allMethodSignaturesWellFormed _ _ _ hfg hgm
    have ⟨hpEq, hrEq⟩ := hmc.interpTargets
    exact ⟨hpEq ▸ p, hrEq ▸ r⟩
  methodSignaturesCheckedTarget := fun cname _ cm hfc hmem => by
    obtain ⟨gc, gm, hfg, hgm, ⟨hmc⟩⟩ := traceMethodToSource hcompiled hfc hmem
    have ⟨p, r⟩ := hwfct.allMethodSignaturesCheckedTarget _ _ _ hfg hgm
    have ⟨hpEq, hrEq⟩ := hmc.interpTargets
    exact ⟨hpEq ▸ p, hrEq ▸ r⟩

end Checked

import FwPython.Static.TypeSystem.Soundness
import FwPython.Static.TypeSystem.Algorithmic.Decidability
import FwPython.Static.Subtyping.Completeness
import FwPython.Static.Subtyping.Negation

/-! # Type System Examples

Regression theorems for the static surface typing development. -/

/-! ## Intersection and union typing -/

/-- An expression with two typings can be given an intersection type. -/
example (h1 : HasType ct Γ e T) (h2 : HasType ct Γ e U) :
    HasType ct Γ e (.intersection T U) :=
  .interIntro h1 h2

/-- If `base : class_ c1` and `base : class_ c2` and both classes have
    method `f`, then `base.f` has the intersection callable type. -/
example
    (h1 : HasType ct Γ base (.class_ c1))
    (h2 : HasType ct Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType ct Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) :=
  HasType.attrAccessInter h1 h2 hfmt1 hfmt2

/-- Intersection call: if the argument works for both parameter types,
    the result is an intersection of both return types. -/
example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hattr : HasType ct Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)))
    (harg1 : HasType ct Γ arg p1)
    (harg2 : HasType ct Γ arg p2) :
    HasType ct Γ (.call (.attrAccess base attrName) arg) (.intersection r1 r2) :=
  HasType.call_intersection hwfct hΓwf hattr harg1 harg2

/-- If `base : class_ c1 | class_ c2` and both classes have method `f`,
    then `base.f` has the union callable type. -/
example
    (h : HasType ct Γ base (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType ct Γ (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)) :=
  HasType.attrAccessUnion h hfmt1 hfmt2

/-- Union call through the safe summary: the argument must work for both
    parameter types, and the result is a union. -/
example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hattr : HasType ct Γ (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType ct Γ arg (.intersection p1 p2)) :
    HasType ct Γ (.call (.attrAccess base attrName) arg) (.union r1 r2) :=
  HasType.call_union_summary hwfct hΓwf hattr harg

example :
    IsSubtype ct
      (.intersection (.callable P R) (.callable Q S))
      (.callable (.union P Q) (.intersection R S)) :=
  .callableInterUnion

/-- The else-branch of `isInstance` narrows to `T & negClass C`. -/
example
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType ct (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType ct (Γ.update x (.intersection T (.negClass C))) elseBr R)
    (hwfR : WellFormedTy ct R) :
    HasType ct Γ (.cond (.isInstance x C) thenBr elseBr) R :=
  HasType.condIsInstance_common hlook hfind hthen helse hwfR

/-! ## Primitive class-only rules -/

example
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro)
    (hmem : D ∈ mro) :
    IsSubtype ct (.class_ C) (.class_ D) :=
  .class_ hfind hmro hmem

example
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmMro) :
    IsSubtype ct (.callable P R) (.class_ boundMethodClass) :=
  .callableBoundMethod hBMFind hBMMro

example
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : D ∉ bmro) :
    IsSubtype ct (.class_ B) (.negClass D) :=
  .sealedClassNegClass hleaf hfindB hmroB hnotmem

example :
    IsSubtype ct (.intersection (.class_ C) (.negClass C)) .bottom :=
  .classSelfNegClassBottom

/-! ## Class-only negative fragment -/

example :
    IsSubtype ct (.class_ objectClass) (.union (.class_ C) (.negClass C)) :=
  .objectClassUnionNegClass

example :
    IsSubtype ct T (.union (.class_ C) (.negClass C)) :=
  .trans .objectTop .objectClassUnionNegClass

example :
    IsSubtype ct (.intersection (.class_ C) (.negClass C)) .bottom :=
  class_self_negClass_contradiction

example (hsub : IsSubtype ct (.class_ D) (.class_ C)) :
    IsSubtype ct (.intersection (.class_ D) (.negClass C)) .bottom :=
  classNegClassBottom hsub

example (hsub : IsSubtype ct (.class_ D) (.class_ C)) :
    IsSubtype ct (.negClass C) (.negClass D) :=
  negClassAntitone hsub

example
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : C ∉ bmro) :
    IsSubtype ct (.class_ C) (.negClass B) :=
  leafBuiltinNegClass hleaf hfindB hmroB hnotmem

example
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmMro) :
    IsSubtype ct (.callable P R) (.class_ boundMethodClass) :=
  .callableBoundMethod hBMFind hBMMro

example
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmMro) :
    IsSubtype ct
      (.intersection (.callable P R) (.negClass boundMethodClass))
      .bottom :=
  callable_negClass_boundMethod_contradiction hBMFind hBMMro

example
    (hleaf : LeafBuiltin ct boundMethodClass)
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmro)
    (hnotmem : C ∉ bmro) :
    IsSubtype ct (.intersection (.class_ C) (.callable P R)) .bottom :=
  leaf_class_callable_bottom hleaf hBMFind hBMMro hnotmem

example
    (hlook : h.lookup oid = some obj)
    (hwfNeg : WellFormedTy ct (.negClass C))
    (hfindObj : findClass ct obj.className = some cls)
    (hmroObj : ComputeMro ct cls mro)
    (hnotmem : C ∉ mro) :
    ValueHasType ct h (.objRef oid) (.negClass C) :=
  .objRefNegClass hlook hwfNeg hfindObj hmroObj hnotmem

/-! ## Direct semantic subtyping -/

example : SemSubtype ct T T :=
  SemSubtype.refl T

example
    (h₁ : SemSubtype ct T U) (h₂ : SemSubtype ct U V) :
    SemSubtype ct T V :=
  SemSubtype.trans h₁ h₂

example (h : IsSubtype ct T U) : SemSubtype ct T U :=
  semSubtype_sound h

example
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U)
    (h : SemSubtype ct T U) :
    IsSubtype ct T U :=
  semSubtype_complete hwfct hwfT hwfU h

example
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    IsSubtype ct T U ↔ SemSubtype ct T U :=
  isSubtype_iff_semSubtype hwfct hwfT hwfU

example
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    Decidable (IsSubtype ct T U) := by
  haveI := isSubtype_decidable hwfct hwfT hwfU
  infer_instance

example
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    Decidable (SemSubtype ct T U) := by
  haveI := semSubtype_decidable hwfct hwfT hwfU
  infer_instance

example (h : IsSubtype ct T U) (obj : SemObject ct) :
    T.semDenotes ct obj → U.semDenotes ct obj :=
  semDenotes_at_obj_sound (obj := obj) h

/-! ## Algorithmic checker regressions -/

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hbase : HasType ct Γ base (.class_ c))
    (hfmt : FindMethodType ct c attrName p r) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName) (.callable p r) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact .attrAccess hbase hfmt

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hbase : HasType ct Γ base (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.attrAccessUnion hbase hfmt1 hfmt2

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h1 : HasType ct Γ base (.class_ c1))
    (h2 : HasType ct Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.attrAccessInter h1 h2 hfmt1 hfmt2

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee (.callable P R))
    (harg : HasType ct Γ arg P) :
    checkHasType? hwfct hΓwf (.call callee arg) R = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct hcallee harg

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType ct Γ arg (.intersection p1 p2)) :
    checkHasType? hwfct hΓwf (.call callee arg) (.union r1 r2) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_union_summary hwfct hΓwf hcallee harg

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee
      (.intersection (.callable P R) (.callable Q S)))
    (harg : HasType ct Γ arg (.union P Q))
    (hwfp : WellFormedTy ct (.union P Q))
    (hwfr : WellFormedTy ct (.intersection R S)) :
    checkHasType? hwfct hΓwf (.call callee arg) (.intersection R S) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct
    (.sub hcallee .callableInterUnion (.callable hwfp hwfr))
    harg

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType ct Γ callee .bottom)
    (harg : HasType ct Γ arg (.class_ objectClass)) :
    checkHasType? hwfct hΓwf (.call callee arg) .bottom = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct
    (.sub hcallee .bottom (.callable (wellFormed_object_type hwfct) .bottom))
    harg

example
    (hwfct : WellFormedClassTable ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType ct (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType ct (Γ.update x (.intersection T (.negClass C))) elseBr R)
    (hwfR : WellFormedTy ct R) :
    checkHasType? hwfct hΓwf (.cond (.isInstance x C) thenBr elseBr) R = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.condIsInstance_common hlook hfind hthen helse hwfR

/-! ## Execution smoke tests -/

/-- `constNone` evaluates to the none object in one step. -/
example : SmallStep.evaluatesFrom ct Heap.initial [] .constNone Heap.initial
    (.success (.objRef noneOid)) :=
  ⟨_, RuntimeSteps.single SmallStep.Step.constNone, rfl⟩

/-- `constTrue` evaluates to the true object in one step. -/
example : SmallStep.evaluatesFrom ct Heap.initial [] .constTrue Heap.initial
    (.success (.objRef trueOid)) :=
  ⟨_, RuntimeSteps.single SmallStep.Step.constTrue, rfl⟩

/-- End-to-end: a well-typed constant expression executes to a well-typed value. -/
example (hwf : WellFormedClassTable ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType ct h env Γ)
    (htype : HasType ct Γ .constNone (.class_ noneClass))
    (hexec : SmallStep.evaluatesFrom ct h env .constNone h' result) :
    ∃ v, result = .success v ∧ ValueHasType ct h' v (.class_ noneClass) :=
  soundness hwf hheap henv htype hexec

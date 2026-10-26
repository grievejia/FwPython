import FwPython.Static

/-! # Type System Examples

Regression theorems for the static surface typing development. -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-! ## Intersection and union typing -/

/-- An expression with two typings can be given an intersection type. -/
example (h1 : HasType structural Γ e T) (h2 : HasType structural Γ e U) :
    HasType structural Γ e (.intersection T U) :=
  .interIntro h1 h2

/-- If `base : class_ c1` and `base : class_ c2` and both classes have
    method `f`, then `base.f` has the intersection callable type. -/
example
    (h1 : HasType structural Γ base (.class_ c1))
    (h2 : HasType structural Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType structural Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) :=
  HasType.attrAccessInter h1 h2 hfmt1 hfmt2

/-- Intersection call: if the argument works for both parameter types,
    the result is an intersection of both return types. -/
example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hattr : HasType hwfct.toWellFormedClassHierarchy Γ (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)))
    (harg1 : HasType hwfct.toWellFormedClassHierarchy Γ arg p1)
    (harg2 : HasType hwfct.toWellFormedClassHierarchy Γ arg p2) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.call (.attrAccess base attrName) arg) (.intersection r1 r2) :=
  HasType.call_intersection hwfct hΓwf hattr harg1 harg2

/-- If `base : class_ c1 | class_ c2` and both classes have method `f`,
    then `base.f` has the union callable type. -/
example
    (h : HasType structural Γ base (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    HasType structural Γ (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)) :=
  HasType.attrAccessUnion h hfmt1 hfmt2

/-- Union call through the safe summary: the argument must work for both
    parameter types, and the result is a union. -/
example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hattr : HasType hwfct.toWellFormedClassHierarchy Γ (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg (.intersection p1 p2)) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.call (.attrAccess base attrName) arg) (.union r1 r2) :=
  HasType.call_union_summary hwfct hΓwf hattr harg

/-- The two requirements combine into a function accepting either input type
with a result type that includes either requirement's result. -/
example (validP : WellFormedTy ct P) (validQ : WellFormedTy ct Q)
    (validR : WellFormedTy ct R) (validS : WellFormedTy ct S) :
    IsSubtype structural
      (.intersection (.callable P R) (.callable Q S))
      (.callable (.union P Q) (.union R S)) :=
  .callableCorrelatedSummary validP validQ validR validS

/-- The else-branch of `isInstance` narrows to `T & negClass C`. -/
example
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType structural (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType structural (Γ.update x (.intersection T (.negClass C))) elseBr R)
    (hwfR : WellFormedTy ct R) :
    HasType structural Γ (.cond (.isInstance x C) thenBr elseBr) R :=
  HasType.condIsInstance_common hlook hfind hthen helse hwfR

/-! ## Primitive class-only rules -/

example
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro)
    (hmem : D ∈ mro) :
    IsSubtype structural (.class_ C) (.class_ D) :=
  .class_ hfind hmro hmem

example (validP : WellFormedTy ct P) (validR : WellFormedTy ct R) :
    IsSubtype structural (.callable P R) (.class_ boundMethodClass) :=
  .callableBoundMethod validP validR

example
    (hleaf : B ∈ sealedClasses)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : D ∉ bmro) (validD : WellFormedTy ct (.class_ D)) :
    IsSubtype structural (.class_ B) (.negClass D) :=
  .sealedClassNegClass hleaf hfindB hmroB hnotmem validD

example (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.intersection (.class_ C) (.negClass C)) .bottom :=
  .classSelfNegClassBottom validC

/-! ## Class-only negative fragment -/

example (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.class_ objectClass) (.union (.class_ C) (.negClass C)) :=
  .objectClassUnionNegClass validC

example (validT : WellFormedTy ct T) (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural T (.union (.class_ C) (.negClass C)) :=
  .trans (.objectTop validT) (.objectClassUnionNegClass validC)

example (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.intersection (.class_ C) (.negClass C)) .bottom :=
  IsSubtype.classSelfNegClassBottom validC

example (hsub : IsSubtype structural (.class_ D) (.class_ C)) :
    IsSubtype structural (.intersection (.class_ D) (.negClass C)) .bottom :=
  classNegClassBottom hsub

example (hsub : IsSubtype structural (.class_ D) (.class_ C)) :
    IsSubtype structural (.negClass C) (.negClass D) :=
  negClassAntitone hsub

example
    (hleaf : B ∈ sealedClasses)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : C ∉ bmro) (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.class_ C) (.negClass B) :=
  classNegSealedClass hleaf hfindB hmroB hnotmem validC

example (validP : WellFormedTy ct P) (validR : WellFormedTy ct R) :
    IsSubtype structural
      (.intersection (.callable P R) (.negClass boundMethodClass))
      .bottom :=
  callable_negClass_boundMethod_contradiction validP validR

example
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmro)
    (hnotmem : C ∉ bmro) (validC : WellFormedTy ct (.class_ C))
    (validP : WellFormedTy ct P) (validR : WellFormedTy ct R) :
    IsSubtype structural (.intersection (.class_ C) (.callable P R)) .bottom :=
  class_callable_bottom_of_not_boundMethod hBMFind hBMMro hnotmem validC validP validR

example
    (hlook : h.lookup oid = some obj)
    (hwfNeg : WellFormedTy ct (.negClass C))
    (hfindObj : findClass ct obj.className = some cls)
    (hmroObj : ComputeMro ct cls mro)
    (hnotmem : C ∉ mro) :
    ValueHasType structural h (.objRef oid) (.negClass C) :=
  .objRefNegClass hlook hwfNeg hfindObj hmroObj hnotmem

/-! ## Algorithmic checker regressions -/

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hbase : HasType hwfct.toWellFormedClassHierarchy Γ base (.class_ c))
    (hfmt : FindMethodType ct c attrName p r) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName) (.callable p r) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact .attrAccess hbase hfmt

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hbase : HasType hwfct.toWellFormedClassHierarchy Γ base (.union (.class_ c1) (.class_ c2)))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName)
      (.union (.callable p1 r1) (.callable p2 r2)) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.attrAccessUnion hbase hfmt1 hfmt2

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (h1 : HasType hwfct.toWellFormedClassHierarchy Γ base (.class_ c1))
    (h2 : HasType hwfct.toWellFormedClassHierarchy Γ base (.class_ c2))
    (hfmt1 : FindMethodType ct c1 attrName p1 r1)
    (hfmt2 : FindMethodType ct c2 attrName p2 r2) :
    checkHasType? hwfct hΓwf (.attrAccess base attrName)
      (.intersection (.callable p1 r1) (.callable p2 r2)) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.attrAccessInter h1 h2 hfmt1 hfmt2

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee (.callable P R))
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg P) :
    checkHasType? hwfct hΓwf (.call callee arg) R = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct hcallee harg (hasType_wellFormed hwfct hΓwf harg)

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee
      (.union (.callable p1 r1) (.callable p2 r2)))
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg (.intersection p1 p2)) :
    checkHasType? hwfct hΓwf (.call callee arg) (.union r1 r2) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_union_summary hwfct hΓwf hcallee harg

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee
      (.intersection (.callable P R) (.callable Q S)))
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg (.union P Q))
    (hwfp : WellFormedTy ct (.union P Q))
    (hwfr : WellFormedTy ct (.union R S)) :
    checkHasType? hwfct hΓwf (.call callee arg) (.union R S) = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct
    (.sub hcallee (.callableCorrelatedSummary
      hwfp.union_left hwfp.union_right hwfr.union_left hwfr.union_right))
    harg hwfp

/-- A Bottom-typed callee may diverge before its argument is evaluated; the call is typed at Bottom. -/
example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hcallee : HasType hwfct.toWellFormedClassHierarchy Γ callee .bottom)
    (harg : HasType hwfct.toWellFormedClassHierarchy Γ arg (.class_ objectClass)) :
    checkHasType? hwfct hΓwf (.call callee arg) .bottom = true := by
  apply (checkHasType?_iff_hasType hwfct hΓwf).2
  exact HasType.call_direct
    (.sub hcallee (.bottom (.callable (WellFormedTy.object hwfct.toWellFormedClassHierarchy) .bottom)))
    harg (WellFormedTy.object hwfct.toWellFormedClassHierarchy)

example
    (hwfct : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some cls)
    (hthen : HasType hwfct.toWellFormedClassHierarchy (Γ.update x (.intersection T (.class_ C))) thenBr R)
    (helse : HasType hwfct.toWellFormedClassHierarchy (Γ.update x (.intersection T (.negClass C))) elseBr R)
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
example (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy h env Γ)
    (htype : HasType hwf.toWellFormedClassHierarchy Γ .constNone (.class_ noneClass))
    (hexec : SmallStep.evaluatesFrom ct h env .constNone h' result) :
    ∃ v, result = .success v ∧ ValueHasType hwf.toWellFormedClassHierarchy h' v (.class_ noneClass) :=
  soundness hwf hheap henv htype hexec

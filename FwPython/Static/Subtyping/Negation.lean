import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.Lattice

/-! ## Class-only negative helper theorems -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- A known class outside a sealed builtin's MRO satisfies the builtin's exclusion. -/
theorem classNegSealedClass
    (hsealed : B ∈ sealedClasses)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : C ∉ bmro) (validC : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.class_ C) (.negClass B) := by
  have validB : WellFormedTy ct (.class_ B) := WellFormedTy.class_of_lookup hfindB
  have validNegB := validB.neg_of_class
  have excluded : IsSubtype structural (.class_ B) (.negClass C) :=
    .sealedClassNegClass hsealed hfindB hmroB hnotmem validC
  have empty : IsSubtype structural (.intersection (.class_ C) (.class_ B)) .bottom :=
    .trans (.interIntro (.interLeft (.refl validC) validB) (.interRight excluded validC))
      (.classSelfNegClassBottom validC)
  exact .trans
    (.interIntro (.refl validC) (.trans (.objectTop validC) (.objectClassUnionNegClass validB)))
    (.trans (subtype_inter_union_distrib validC validB validNegB)
      (.unionElim (.trans empty (.bottom validNegB))
        (.interRight (.refl validNegB) validC)))

/-- A subclass type and its superclass exclusion have no common value. -/
theorem classNegClassBottom
    (hsub : IsSubtype structural (.class_ D) (.class_ C)) :
    IsSubtype structural (.intersection (.class_ D) (.negClass C)) .bottom :=
  .trans
    (.interIntro (.interLeft hsub hsub.targetWellFormed.neg_of_class)
      (.interRight (.refl hsub.targetWellFormed.neg_of_class) hsub.sourceWellFormed))
    (.classSelfNegClassBottom hsub.targetWellFormed)

/-- Excluding a superclass also excludes each subclass. -/
theorem negClassAntitone
    (hsub : IsSubtype structural (.class_ D) (.class_ C)) :
    IsSubtype structural (.negClass C) (.negClass D) := by
  have validC := hsub.targetWellFormed
  have validD := hsub.sourceWellFormed
  have negC := validC.neg_of_class
  have negD := validD.neg_of_class
  have empty : IsSubtype structural (.intersection (.negClass C) (.class_ D)) .bottom :=
    .trans (subtype_inter_comm negC validD) (classNegClassBottom hsub)
  exact .trans
    (.interIntro (.refl negC) (.trans (.objectTop negC) (.objectClassUnionNegClass validD)))
    (.trans (subtype_inter_union_distrib negC validD negD)
      (.unionElim (.trans empty (.bottom negD)) (.interRight (.refl negD) negC)))

/-- No valid function type can also exclude BoundMethod. -/
theorem callable_negClass_boundMethod_contradiction
    (inputValid : WellFormedTy ct P) (resultValid : WellFormedTy ct R) :
    IsSubtype structural
      (.intersection (.callable P R) (.negClass boundMethodClass)) .bottom :=
  .trans
    (.interIntro
      (.interLeft (.callableBoundMethod inputValid resultValid) (WellFormedTy.boundMethod structural).neg_of_class)
      (.interRight (.refl (WellFormedTy.boundMethod structural).neg_of_class) (.callable inputValid resultValid)))
    (classNegClassBottom (.refl (.boundMethod structural)))

/-- A known class outside BoundMethod's MRO has no callable values. -/
theorem class_callable_bottom_of_not_boundMethod
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmro)
    (hnotmem : C ∉ bmro) (classValid : WellFormedTy ct (.class_ C))
    (inputValid : WellFormedTy ct P) (resultValid : WellFormedTy ct R) :
    IsSubtype structural (.intersection (.class_ C) (.callable P R)) .bottom :=
  .trans (subtype_inter_comm classValid (.callable inputValid resultValid))
    (.trans
      (.interIntro
        (.interLeft (.callableBoundMethod inputValid resultValid) classValid)
        (.interRight (classNegSealedClass (by simp [sealedClasses]) hBMFind hBMMro hnotmem classValid)
          (.callable inputValid resultValid)))
      (classNegClassBottom (.refl (.boundMethod structural))))

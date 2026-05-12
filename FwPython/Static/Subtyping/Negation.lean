import FwPython.Static.Subtyping.Core
import FwPython.Static.Subtyping.Lattice

/-! ## Class-only negative helper theorems -/

/-- A class outside a designated leaf built-in's MRO satisfies the
    corresponding `negClass` atom. -/
theorem leafBuiltinNegClass
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : C ∉ bmro) :
    IsSubtype ct (.class_ C) (.negClass B) :=
  -- `class C <: class C ∩ (class B | negClass B)` then distribute and project.
  have hBNegC : IsSubtype ct (.class_ B) (.negClass C) :=
    .sealedClassNegClass hleaf hfindB hmroB hnotmem
  have hCBBottom : IsSubtype ct (.intersection (.class_ C) (.class_ B)) .bottom :=
    .trans (.interIntro (.interLeft .refl) (.interRight hBNegC)) .classSelfNegClassBottom
  .trans
    (.trans (.interIntro .refl (.trans .objectTop .objectClassUnionNegClass))
      (.trans subtype_inter_union_distrib
        (.unionElim (.trans hCBBottom .bottom) (.interRight .refl))))
    .refl

/-- If `class_ D <: class_ C`, then `class_ D & negClass C <: bottom`. -/
theorem classNegClassBottom
    (hsub : IsSubtype ct (.class_ D) (.class_ C)) :
    IsSubtype ct (.intersection (.class_ D) (.negClass C)) .bottom :=
  .trans
    (.interIntro (.interLeft hsub) (.interRight .refl))
    .classSelfNegClassBottom

/-- Class-only antitonicity: if `class_ D <: class_ C`, then
    `negClass C <: negClass D`. -/
theorem negClassAntitone
    (hsub : IsSubtype ct (.class_ D) (.class_ C)) :
    IsSubtype ct (.negClass C) (.negClass D) :=
  -- `negClass C <: negClass C ∩ Object <: negClass C ∩ (class D | negClass D)`
  -- then distribute, kill the `class D` arm via `classNegClassBottom`, project.
  have hLeftBottom : IsSubtype ct (.intersection (.negClass C) (.class_ D)) .bottom :=
    .trans subtype_inter_comm (classNegClassBottom hsub)
  .trans subtype_inter_object'
    (.trans (.interIntro (.interLeft .refl) (.interRight .objectClassUnionNegClass))
      (.trans subtype_inter_union_distrib
        (.unionElim (.trans hLeftBottom .bottom) (.interRight .refl))))

/-- Mirror `classNegClassBottom` across intersection commutativity. -/
theorem negClass_class_contradiction
    (hsub : IsSubtype ct (.class_ D) (.class_ C)) :
    IsSubtype ct (.intersection (.negClass C) (.class_ D)) .bottom :=
  .trans subtype_inter_comm (classNegClassBottom hsub)

/-- Every class contradicts its own `negClass` atom. -/
theorem class_self_negClass_contradiction :
    IsSubtype ct (.intersection (.class_ C) (.negClass C)) .bottom :=
  classNegClassBottom .refl

/-- No callable can satisfy `negClass BoundMethod`. -/
theorem callable_negClass_boundMethod_contradiction
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmMro) :
    IsSubtype ct
      (.intersection (.callable P R) (.negClass boundMethodClass))
      .bottom :=
  .trans
    (.interIntro
      (.interLeft (.callableBoundMethod hBMFind hBMMro))
      (.interRight .refl))
    (classNegClassBottom .refl)

/-- A leaf built-in class exclusion is enough to show a class is not callable. -/
theorem leaf_class_callable_bottom
    (hleaf : LeafBuiltin ct boundMethodClass)
    (hBMFind : findClass ct boundMethodClass = some bmCls)
    (hBMMro : ComputeMro ct bmCls bmro)
    (hnotmem : C ∉ bmro) :
    IsSubtype ct (.intersection (.class_ C) (.callable P R)) .bottom :=
  .trans subtype_inter_comm
    (.trans
      (.interIntro
        (.interLeft (.callableBoundMethod hBMFind hBMMro))
        (.interRight (leafBuiltinNegClass hleaf hBMFind hBMMro hnotmem)))
      (classNegClassBottom .refl))

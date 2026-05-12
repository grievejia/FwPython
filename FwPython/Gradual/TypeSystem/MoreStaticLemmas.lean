import FwPython.Gradual.TypeSystem.BoundaryPrecision
import FwPython.Gradual.TypeSystem.SemanticEquivalence

/-! # Small semantic helper lemmas -/

theorem moreStatic_bottom_iff
    (gct : GClassTable) (G : GTy) :
    MoreStatic gct G .bottom ↔
      IsSubtype (eraseClassTable gct) (upperBound G) .bottom := by
  constructor
  · intro h
    simpa [MoreStatic, upperBound] using h.2
  · intro hbottom
    refine ⟨?_, ?_⟩
    · simpa [MoreStatic, lowerBound] using
        (IsSubtype.bottom : IsSubtype (eraseClassTable gct) .bottom (lowerBound G))
    · simpa [MoreStatic, upperBound] using hbottom

theorem moreStatic_runtimePublicTy
    (gct : GClassTable) (G : GTy) :
    MoreStatic gct (runtimePublicTy G) G := by
  rw [runtimePublicTy_id]
  exact moreStatic_refl gct G

theorem moreStatic_toAny
    (gct : GClassTable) (G : GTy) :
    MoreStatic gct G .any :=
  ⟨IsSubtype.bottom, IsSubtype.objectTop⟩

theorem moreStatic_intersection_intro
    (h₁ : MoreStatic gct G H₁)
    (h₂ : MoreStatic gct G H₂) :
    MoreStatic gct G (.intersection H₁ H₂) :=
  ⟨IsSubtype.interLeft h₁.1, IsSubtype.interIntro h₁.2 h₂.2⟩

theorem moreStatic_intersection_left_of_upper
    (h : MoreStatic gct G H)
    (hupper : IsSubtype (eraseClassTable gct) (upperBound G) (upperBound K)) :
    MoreStatic gct G (.intersection H K) := by
  refine ⟨?_, ?_⟩
  · exact IsSubtype.interLeft h.1
  · exact IsSubtype.interIntro h.2 hupper

theorem moreStatic_intersection_right_of_upper
    (h : MoreStatic gct G H)
    (hupper : IsSubtype (eraseClassTable gct) (upperBound G) (upperBound K)) :
    MoreStatic gct G (.intersection K H) := by
  refine ⟨?_, ?_⟩
  · exact IsSubtype.interRight h.1
  · exact IsSubtype.interIntro hupper h.2

theorem assignableTo_moreDynamic_arg
    (harg : MoreStatic gct arg₁ arg₂)
    (hassign : AssignableTo gct arg₁ param) :
    AssignableTo gct arg₂ param :=
  IsSubtype.trans harg.1 hassign

theorem assignableTo_moreDynamic_param
    (hparam : MoreStatic gct param₁ param₂)
    (hassign : AssignableTo gct arg param₁) :
    AssignableTo gct arg param₂ :=
  IsSubtype.trans hassign hparam.2

theorem semanticTypeEquivalence_bottom
    (gct : GClassTable) :
    SemanticTypeEquivalence gct .bottom .bottom :=
  semanticTypeEquivalence_refl gct .bottom

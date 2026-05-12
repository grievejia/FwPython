import FwPython.Gradual.Contracts.Semantics
import FwPython.Gradual.Statics

/-! # Boundary-contract precision relations -/

/-- Two boundary contracts are precision-related when their canonical
    meanings are precision-related as gradual types. -/
def BoundaryPrecision (gct : GClassTable)
    (c₁ c₂ : BoundaryContract) : Prop :=
  MoreStatic gct (boundaryMeaning c₁) (boundaryMeaning c₂)

theorem boundaryPrecision_refl (gct : GClassTable) (c : BoundaryContract) :
    BoundaryPrecision gct c c :=
  moreStatic_refl gct (boundaryMeaning c)

theorem boundaryPrecision_trans {gct : GClassTable}
    {c₁ c₂ c₃ : BoundaryContract}
    (h₁ : BoundaryPrecision gct c₁ c₂) (h₂ : BoundaryPrecision gct c₂ c₃) :
    BoundaryPrecision gct c₁ c₃ :=
  moreStatic_trans h₁ h₂

theorem boundaryPrecision_compileBoundaryRaw
    (h : MoreStatic gct G₁ G₂) :
    BoundaryPrecision gct (compileBoundaryRaw G₁) (compileBoundaryRaw G₂) := by
  unfold BoundaryPrecision
  rwa [boundaryMeaning_compileBoundaryRaw, boundaryMeaning_compileBoundaryRaw]

/-- `MoreStatic` is monotone in union types. -/
theorem moreStatic_union
    (h₁ : MoreStatic gct G₁ G₂)
    (h₂ : MoreStatic gct H₁ H₂) :
    MoreStatic gct (.union G₁ H₁) (.union G₂ H₂) :=
  ⟨.unionElim (.unionLeft h₁.1) (.unionRight h₂.1),
   .unionElim (.unionLeft h₁.2) (.unionRight h₂.2)⟩

/-- `MoreStatic` is monotone in intersection types. -/
theorem moreStatic_intersection
    (h₁ : MoreStatic gct G₁ G₂)
    (h₂ : MoreStatic gct H₁ H₂) :
    MoreStatic gct (.intersection G₁ H₁) (.intersection G₂ H₂) :=
  ⟨.interIntro (.interLeft h₁.1) (.interRight h₂.1),
   .interIntro (.interLeft h₁.2) (.interRight h₂.2)⟩

/-- `MoreStatic` is monotone in callable types (contravariant in parameter,
covariant in return). -/
theorem moreStatic_callable
    (hp : MoreStatic gct P₁ P₂)
    (hr : MoreStatic gct R₁ R₂) :
    MoreStatic gct (.callable P₁ R₁) (.callable P₂ R₂) :=
  ⟨.callable hp.2 hr.1, .callable hp.1 hr.2⟩

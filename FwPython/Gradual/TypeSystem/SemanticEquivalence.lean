import FwPython.Gradual.Contracts.Semantics
import FwPython.Gradual.TypeSystem.ClassTable.Transport

/-! # Semantic equivalence for gradual types -/

/-- Two gradual types are semantically equivalent when each is at least as
dynamic as the other under `MoreStatic`. This is the semantic replacement for
literal equality on source-facing theorem statements. -/
def SemanticTypeEquivalence (gct : GClassTable) (G₁ G₂ : GTy) : Prop :=
  MoreStatic gct G₁ G₂ ∧ MoreStatic gct G₂ G₁

@[refl] theorem semanticTypeEquivalence_refl (gct : GClassTable) (G : GTy) :
    SemanticTypeEquivalence gct G G :=
  ⟨moreStatic_refl gct G, moreStatic_refl gct G⟩

@[symm] theorem semanticTypeEquivalence_symm
    (h : SemanticTypeEquivalence gct G₁ G₂) :
    SemanticTypeEquivalence gct G₂ G₁ :=
  ⟨h.2, h.1⟩

theorem semanticTypeEquivalence_trans
    (h₁ : SemanticTypeEquivalence gct G₁ G₂)
    (h₂ : SemanticTypeEquivalence gct G₂ G₃) :
    SemanticTypeEquivalence gct G₁ G₃ :=
  ⟨moreStatic_trans h₁.1 h₂.1, moreStatic_trans h₂.2 h₁.2⟩

theorem semanticTypeEquivalence_of_eq
    (h : G₁ = G₂) :
    SemanticTypeEquivalence gct G₁ G₂ :=
  h ▸ semanticTypeEquivalence_refl gct G₁

theorem semanticTypeEquivalence_iff
    (gct : GClassTable) (G₁ G₂ : GTy) :
    SemanticTypeEquivalence gct G₁ G₂ ↔
      MoreStatic gct G₁ G₂ ∧ MoreStatic gct G₂ G₁ :=
  Iff.rfl

theorem semanticTypeEquivalence_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂) :
    SemanticTypeEquivalence gct₁ G₁ G₂ ↔
      SemanticTypeEquivalence gct₂ G₁ G₂ := by
  unfold SemanticTypeEquivalence
  rw [moreStatic_transport hct, moreStatic_transport hct]

theorem semanticTypeEquivalence_runtimePublicTy
    (G : GTy) :
    SemanticTypeEquivalence gct (runtimePublicTy G) G := by
  simpa [runtimePublicTy_id] using semanticTypeEquivalence_refl gct G

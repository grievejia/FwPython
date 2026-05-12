/-! # Reflexive-transitive closure of a step relation, parameterized over the relation. -/

/-- Reflexive-transitive closure of a binary relation `R` on `State`. -/
inductive RuntimeSteps {State : Type} (R : State → State → Prop) :
    State → State → Prop where
  | refl : RuntimeSteps R s s
  | step : R s₁ s₂ → RuntimeSteps R s₂ s₃ → RuntimeSteps R s₁ s₃

namespace RuntimeSteps

theorem single {State : Type} {R : State → State → Prop} {s₁ s₂ : State}
    (h : R s₁ s₂) : RuntimeSteps R s₁ s₂ :=
  .step h .refl

theorem trans {State : Type} {R : State → State → Prop} {s₁ s₂ s₃ : State}
    (h₁ : RuntimeSteps R s₁ s₂) (h₂ : RuntimeSteps R s₂ s₃) :
    RuntimeSteps R s₁ s₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

end RuntimeSteps

/-! # Pointwise list relation

`Forall₂ R l₁ l₂` holds when `l₁` and `l₂` have the same length and
corresponding elements are related by `R`. This is a standard library
definition that is not available in this Lean version. -/

inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

universe u v w

/-- Type-valued pointwise list relation for producer artifacts whose element
relation carries computational data. -/
inductive Forall2Data {α : Type u} {β : Type v}
    (R : α → β → Type w) :
    List α → List β → Type (max u v w) where
  /-- Relate two empty lists. -/
  | nil : Forall2Data R [] []
  /-- Store data for the head pair and recursively store data for the tails. -/
  | cons : R a b → Forall2Data R as bs → Forall2Data R (a :: as) (b :: bs)

section Forall2Data

variable {α : Type u} {β : Type v} {R : α → β → Type w}
  {S : α → β → Prop} {as : List α} {bs : List β} {b : β}

/-- Erase Type-valued pointwise data into a Prop-valued `Forall₂` relation
through an explicit projection. -/
theorem forall2Data_to_forall2
    (h : Forall2Data R as bs)
    (project : ∀ a b, R a b → S a b) :
    Forall₂ S as bs := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (project _ _ hr) ih

/-- Swap the sides of a `Forall2Data` witness; reuses the same element data
under the flipped relation. -/
def Forall2Data.symm
    {as : List α} {bs : List β} :
    Forall2Data R as bs → Forall2Data (fun b a => R a b) bs as
  | .nil => .nil
  | .cons hr htail => .cons hr htail.symm

/-- Project a right-list membership into a left-list membership plus `Nonempty`
pointwise data for Prop-valued consumers. -/
theorem forall2Data_mem_right_exists
    (hf : Forall2Data R as bs)
    (hmem : b ∈ bs) :
    ∃ a, a ∈ as ∧ Nonempty (R a b) := by
  induction hf with
  | nil => cases hmem
  | cons hr _ ih =>
      cases hmem with
      | head => exact ⟨_, .head _, ⟨hr⟩⟩
      | tail _ h =>
          obtain ⟨a, ha, hrel⟩ := ih h
          exact ⟨a, .tail _ ha, hrel⟩

end Forall2Data

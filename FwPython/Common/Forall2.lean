/-! # Pointwise list relation

`Forall₂ R l₁ l₂` holds when `l₁` and `l₂` have the same length and
corresponding elements are related by `R`. This is a standard library
definition that is not available in this Lean version. -/

inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

theorem forall₂_map_eq {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b)
    {l₁ : List α} {l₂ : List β}
    (h : Forall₂ R l₁ l₂) :
    l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [hfg _ _ hr, ih]

theorem forall₂_refl {R : α → α → Prop} (hr : ∀ a, R a a) :
    ∀ (l : List α), Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (hr a) (forall₂_refl hr l)

theorem forall₂_trans {R : α → α → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {l₁ l₂ l₃ : List α}
    (h12 : Forall₂ R l₁ l₂) (h23 : Forall₂ R l₂ l₃) :
    Forall₂ R l₁ l₃ := by
  induction h12 generalizing l₃ with
  | nil => cases h23; exact .nil
  | cons hr _ ih =>
    cases h23 with
    | cons hr' h23' => exact .cons (htrans _ _ _ hr hr') (ih h23')

theorem forall₂_imp {R S : α → β → Prop}
    (hrs : ∀ a b, R a b → S a b)
    {l₁ : List α} {l₂ : List β}
    (h : Forall₂ R l₁ l₂) :
    Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hrs _ _ hr) ih

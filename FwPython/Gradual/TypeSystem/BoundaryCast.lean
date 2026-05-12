import FwPython.Gradual.Checked.Enforce

/-! # Boundary-contract cast helpers -/

/-- Transport boundary labels along propositional equality of contracts. -/
@[inline] def castBoundaryLabels
    {c₁ c₂ : BoundaryContract}
    (h : c₁ = c₂)
    (labels : BoundaryLabels c₁) :
    BoundaryLabels c₂ :=
  cast (congrArg BoundaryLabels h) labels

@[simp] theorem castBoundaryLabels_rfl
    (labels : BoundaryLabels c) :
    castBoundaryLabels rfl labels = labels :=
  rfl

@[simp] theorem castBoundaryLabels_direct
    {c₁ c₂ : BoundaryContract}
    (h : c₁ = c₂)
    (labels : BoundaryLabels c₁) :
    (castBoundaryLabels h labels).direct = labels.direct := by
  cases h
  rfl

theorem enforceValue_castBoundary
    {c₁ c₂ : BoundaryContract}
    (h : c₁ = c₂)
    (labels : BoundaryLabels c₁)
    (henf : EnforceValue gct heap v c₂ (castBoundaryLabels h labels) r) :
    EnforceValue gct heap v c₁ labels r := by
  cases h; exact henf

theorem enforceValue_castBoundary_forward
    {c₁ c₂ : BoundaryContract}
    (h : c₁ = c₂)
    (labels : BoundaryLabels c₁)
    (henf : EnforceValue gct heap v c₁ labels r) :
    EnforceValue gct heap v c₂ (castBoundaryLabels h labels) r := by
  cases h; exact henf

/-- Recover parameter labels at the compiled parameter contract of a checked
method. -/
@[inline] def castMethodParameterLabels
    (m : CheckedMethod)
    (h : m.parameterContract = compileBoundaryRaw m.paramTy) :
    BoundaryLabels (compileBoundaryRaw m.paramTy) :=
  castBoundaryLabels h m.parameterLabels

/-- Recover return labels at the compiled return contract of a checked
method. -/
@[inline] def castMethodReturnLabels
    (m : CheckedMethod)
    (h : m.returnContract = compileBoundaryRaw m.returnTy) :
    BoundaryLabels (compileBoundaryRaw m.returnTy) :=
  castBoundaryLabels h m.returnLabels

import FwPython.Gradual.TypeSystem.CheckedTargetSyntax

/-! # Structural precision for explicit checked targets -/

/-- Relate a check target to the same target with some parts replaced by `any`.
The no-blame proof uses this relation to transfer value satisfaction to a wider target. -/
inductive CheckedTargetPrecision : CheckedTarget → CheckedTarget → Prop where
  /-- Keep the target unchanged. -/
  | refl :
      CheckedTargetPrecision T T
  /-- Replace the whole target with the unknown target. -/
  | toAny :
      CheckedTargetPrecision T .any
  /-- Replace parts of the function's input or result targets. -/
  | callable :
      CheckedTargetPrecision paramTy₁ paramTy₂ →
      CheckedTargetPrecision returnTy₁ returnTy₂ →
      CheckedTargetPrecision
        (.callable paramTy₁ returnTy₁)
        (.callable paramTy₂ returnTy₂)
  /-- Replace parts of each union alternative. -/
  | union :
      CheckedTargetPrecision left₁ left₂ →
      CheckedTargetPrecision right₁ right₂ →
      CheckedTargetPrecision
        (.union left₁ right₁)
        (.union left₂ right₂)
  /-- Replace parts of each intersection requirement. -/
  | intersection :
      CheckedTargetPrecision left₁ left₂ →
      CheckedTargetPrecision right₁ right₂ →
      CheckedTargetPrecision
        (.intersection left₁ right₁)
        (.intersection left₂ right₂)

/-- Structural precision on raw gradual annotations, phrased directly through
their explicit checked-target images. -/
abbrev AnnotationTargetPrecision (G₁ G₂ : GTy) : Prop :=
  CheckedTargetPrecision (checkedTargetOfGTy G₁) (checkedTargetOfGTy G₂)

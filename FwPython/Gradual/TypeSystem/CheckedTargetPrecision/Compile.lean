import FwPython.Gradual.TypeSystem.CheckedTargetPrecision.Core

/-! # Compile-side precision for explicit checked targets -/

/-- Structural precision on compile-generated checked targets. This extends
`CheckedTargetPrecision` with the source-side bottom escape and the two
intersection-to-branch absorption rules used by normalized call-parameter
targets. -/
inductive CompileTargetPrecision : CheckedTarget → CheckedTarget → Prop where
  | refl :
      CompileTargetPrecision T T
  | toAny :
      CompileTargetPrecision T .any
  | callable :
      CompileTargetPrecision paramTy₁ paramTy₂ →
      CompileTargetPrecision returnTy₁ returnTy₂ →
      CompileTargetPrecision
        (.callable paramTy₁ returnTy₁)
        (.callable paramTy₂ returnTy₂)
  | union :
      CompileTargetPrecision left₁ left₂ →
      CompileTargetPrecision right₁ right₂ →
      CompileTargetPrecision
        (.union left₁ right₁)
        (.union left₂ right₂)
  | intersection :
      CompileTargetPrecision left₁ left₂ →
      CompileTargetPrecision right₁ right₂ →
      CompileTargetPrecision
        (.intersection left₁ right₁)
        (.intersection left₂ right₂)
  | fromBottom :
      CompileTargetPrecision .bottom target
  | intersection_left_toAny :
      CompileTargetPrecision left .any →
      CompileTargetPrecision right target →
      CompileTargetPrecision
        (.intersection left right)
        target
  | intersection_right_toAny :
      CompileTargetPrecision left target →
      CompileTargetPrecision right .any →
      CompileTargetPrecision
        (.intersection left right)
        target
  | meet :
      CompileTargetPrecision target left →
      CompileTargetPrecision target right →
      CompileTargetPrecision
        target
        (.intersection left right)

import FwPython.Gradual.Contracts.Semantics

/-! # Explicit checked-target syntax

The checked/runtime layer stores explicit `CheckedTarget` annotations rather
than raw `GTy`. The constructor surface mirrors `GTy`, with `interpTarget`
projecting back to `GTy` and `compileBoundaryTarget` producing the runtime
contract image. -/

/-- Explicit checked-target syntax. -/
inductive CheckedTarget : Type where
  | any : CheckedTarget
  | class_ : Identifier → CheckedTarget
  | callable : CheckedTarget → CheckedTarget → CheckedTarget
  | union : CheckedTarget → CheckedTarget → CheckedTarget
  | intersection : CheckedTarget → CheckedTarget → CheckedTarget
  | bottom : CheckedTarget
  | negClass : Identifier → CheckedTarget
  deriving DecidableEq, Repr

/-- Interpret an explicit checked target as a source-level gradual type. -/
def interpTarget : CheckedTarget → GTy
  | .any => .any
  | .class_ cname => .class_ cname
  | .callable paramTy returnTy =>
      .callable (interpTarget paramTy) (interpTarget returnTy)
  | .union left right =>
      .union (interpTarget left) (interpTarget right)
  | .intersection left right =>
      .intersection (interpTarget left) (interpTarget right)
  | .bottom => .bottom
  | .negClass cname => .negClass cname

instance : Coe CheckedTarget GTy where
  coe := interpTarget

/-- Compile an explicit checked target to the machine-facing boundary syntax. -/
def compileBoundaryTarget : CheckedTarget → BoundaryContract
  | .any => .unknown
  | .class_ cname => .class_ cname
  | .callable paramTy returnTy =>
      .callable (compileBoundaryTarget paramTy) (compileBoundaryTarget returnTy)
  | .union left right =>
      .union (compileBoundaryTarget left) (compileBoundaryTarget right)
  | .intersection left right =>
      .intersection (compileBoundaryTarget left) (compileBoundaryTarget right)
  | .bottom => .bottom
  | .negClass cname => .negClass cname

/-- Embed a source gradual type into explicit checked-target syntax. -/
def checkedTargetOfGTy : GTy → CheckedTarget
  | .any => .any
  | .class_ cname => .class_ cname
  | .callable paramTy returnTy =>
      .callable (checkedTargetOfGTy paramTy) (checkedTargetOfGTy returnTy)
  | .union left right =>
      .union (checkedTargetOfGTy left) (checkedTargetOfGTy right)
  | .intersection left right =>
      .intersection (checkedTargetOfGTy left) (checkedTargetOfGTy right)
  | .bottom => .bottom
  | .negClass cname => .negClass cname

@[simp] theorem interpTarget_checkedTargetOfGTy
    (G : GTy) :
    interpTarget (checkedTargetOfGTy G) = G := by
  induction G <;> simp [interpTarget, checkedTargetOfGTy, *]

/-- Embedding gradual types into explicit checked-target syntax is injective. -/
theorem checkedTargetOfGTy_injective :
    Function.Injective checkedTargetOfGTy :=
  Function.LeftInverse.injective interpTarget_checkedTargetOfGTy

/-- Equality of embedded gradual types is exactly equality of the source types. -/
theorem checkedTargetOfGTy_eq_iff
    (G H : GTy) :
    checkedTargetOfGTy G = checkedTargetOfGTy H ↔
      G = H :=
  checkedTargetOfGTy_injective.eq_iff

/-- `checkedTargetOfGTy` commutes with proof-only conditional branching. -/
theorem checkedTargetOfGTy_if
    (p : Prop) [Decidable p] (G H : GTy) :
    checkedTargetOfGTy (if p then G else H) =
      if p then checkedTargetOfGTy G else checkedTargetOfGTy H :=
  apply_ite checkedTargetOfGTy p G H

theorem compileBoundaryTarget_eq_compileBoundaryRaw_interp
    (T : CheckedTarget) :
    compileBoundaryTarget T = compileBoundaryRaw (interpTarget T) := by
  induction T <;> simp [compileBoundaryTarget, compileBoundaryRaw, interpTarget, *]

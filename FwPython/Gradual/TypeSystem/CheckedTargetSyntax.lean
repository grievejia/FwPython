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

/-- Embed a boundary contract into explicit checked-target syntax. -/
def checkedTargetOfBoundaryContract : BoundaryContract → CheckedTarget
  | .unknown => .any
  | .class_ cname => .class_ cname
  | .callable paramTy returnTy =>
      .callable
        (checkedTargetOfBoundaryContract paramTy)
        (checkedTargetOfBoundaryContract returnTy)
  | .union left right =>
      .union
        (checkedTargetOfBoundaryContract left)
        (checkedTargetOfBoundaryContract right)
  | .intersection left right =>
      .intersection
        (checkedTargetOfBoundaryContract left)
        (checkedTargetOfBoundaryContract right)
  | .bottom => .bottom
  | .negClass cname => .negClass cname

@[simp] theorem interpTarget_checkedTargetOfGTy
    (G : GTy) :
    interpTarget (checkedTargetOfGTy G) = G := by
  induction G <;> simp [interpTarget, checkedTargetOfGTy, *]

@[simp] theorem checkedTargetOfGTy_interpTarget
    (T : CheckedTarget) :
    checkedTargetOfGTy (interpTarget T) = T := by
  induction T <;> simp [interpTarget, checkedTargetOfGTy, *]

@[simp] theorem compileBoundaryTarget_checkedTargetOfGTy
    (G : GTy) :
    compileBoundaryTarget (checkedTargetOfGTy G) = compileBoundaryRaw G := by
  induction G <;> simp [compileBoundaryTarget, checkedTargetOfGTy, compileBoundaryRaw, *]

@[simp] theorem compileBoundaryTarget_checkedTargetOfBoundaryContract
    (c : BoundaryContract) :
    compileBoundaryTarget (checkedTargetOfBoundaryContract c) = c := by
  induction c <;> simp [compileBoundaryTarget, checkedTargetOfBoundaryContract, *]

@[simp] theorem checkedTargetOfBoundaryContract_compileBoundaryTarget
    (T : CheckedTarget) :
    checkedTargetOfBoundaryContract (compileBoundaryTarget T) = T := by
  induction T <;> simp [compileBoundaryTarget, checkedTargetOfBoundaryContract, *]

@[simp] theorem checkedTargetOfBoundaryContract_compileBoundaryRaw
    (G : GTy) :
    checkedTargetOfBoundaryContract (compileBoundaryRaw G) = checkedTargetOfGTy G := by
  induction G <;> simp [checkedTargetOfBoundaryContract, compileBoundaryRaw, checkedTargetOfGTy, *]

@[simp] theorem interpTarget_checkedTargetOfBoundaryContract
    (c : BoundaryContract) :
    interpTarget (checkedTargetOfBoundaryContract c) = boundaryMeaning c := by
  induction c <;> simp [interpTarget, checkedTargetOfBoundaryContract, boundaryMeaning, *]

theorem boundaryMeaning_compileBoundaryTarget
    (T : CheckedTarget) :
    boundaryMeaning (compileBoundaryTarget T) = interpTarget T := by
  induction T <;> simp [boundaryMeaning, compileBoundaryTarget, interpTarget, *]

theorem compileBoundaryTarget_eq_compileBoundaryRaw_interp
    (T : CheckedTarget) :
    compileBoundaryTarget T = compileBoundaryRaw (interpTarget T) := by
  induction T <;> simp [compileBoundaryTarget, compileBoundaryRaw, interpTarget, *]

/-- The current checked-target normalizer is a semantic-preserving scaffold.
It is intentionally weaker than the contract normalizer because machine-level
`unknown` simplifications are not automatically valid `MoreStatic` rewrites on
source `GTy`. -/
def coreNormalizeCheckedTarget (T : CheckedTarget) : CheckedTarget :=
  T

@[simp] theorem normalize_idempotent
    (T : CheckedTarget) :
    coreNormalizeCheckedTarget (coreNormalizeCheckedTarget T) =
      coreNormalizeCheckedTarget T :=
  rfl

@[simp] theorem normalize_semantic_faithful
    (T : CheckedTarget) :
    interpTarget (coreNormalizeCheckedTarget T) = interpTarget T :=
  rfl

@[simp] theorem normalize_compileBoundaryTarget
    (T : CheckedTarget) :
    compileBoundaryTarget (coreNormalizeCheckedTarget T) = compileBoundaryTarget T :=
  rfl

/-- Gct-free runtime/public shape invariant. The current baseline uses the
checked-target normalizer fixpoint so later strengthening can happen behind the
same interface. -/
def RuntimePublicCheckedTargetShape (T : CheckedTarget) : Prop :=
  coreNormalizeCheckedTarget T = T

instance runtimePublicCheckedTargetShape_decidable
    (T : CheckedTarget) :
    Decidable (RuntimePublicCheckedTargetShape T) := by
  unfold RuntimePublicCheckedTargetShape
  infer_instance

theorem runtimePublicCheckedTargetShape_normalized
    (T : CheckedTarget) :
    RuntimePublicCheckedTargetShape (coreNormalizeCheckedTarget T) := by
  unfold RuntimePublicCheckedTargetShape
  simp

theorem runtimePublicCheckedTargetShape_all
    (T : CheckedTarget) :
    RuntimePublicCheckedTargetShape T := by
  unfold RuntimePublicCheckedTargetShape
  rfl

/-- Raw runtime-public gradual targets embed into checked-target syntax through
the dedicated checked-target layer. -/
def checkedTargetOfRuntimePublicTy (G : GTy) : CheckedTarget :=
  coreNormalizeCheckedTarget (checkedTargetOfGTy (runtimePublicTy G))

@[simp] theorem interpTarget_checkedTargetOfRuntimePublicTy
    (G : GTy) :
    interpTarget (checkedTargetOfRuntimePublicTy G) = runtimePublicTy G := by
  simp [checkedTargetOfRuntimePublicTy]

@[simp] theorem compileBoundaryTarget_checkedTargetOfRuntimePublicTy
    (G : GTy) :
    compileBoundaryTarget (checkedTargetOfRuntimePublicTy G) =
      compileBoundaryRaw (runtimePublicTy G) := by
  rw [compileBoundaryTarget_eq_compileBoundaryRaw_interp, interpTarget_checkedTargetOfRuntimePublicTy]

theorem checkedTargetOfRuntimePublicTy_runtimePublic_shape
    (G : GTy) :
    RuntimePublicCheckedTargetShape (checkedTargetOfRuntimePublicTy G) := by
  unfold checkedTargetOfRuntimePublicTy
  exact runtimePublicCheckedTargetShape_normalized _

/-- Smart constructors route through the checked-target normalizer so later
normalization strengthening remains local to this file. -/
def mkCallable (paramTy returnTy : CheckedTarget) : CheckedTarget :=
  coreNormalizeCheckedTarget (.callable paramTy returnTy)

def mkUnion (left right : CheckedTarget) : CheckedTarget :=
  coreNormalizeCheckedTarget (.union left right)

def mkIntersection (left right : CheckedTarget) : CheckedTarget :=
  coreNormalizeCheckedTarget (.intersection left right)

@[simp] theorem interpTarget_mkCallable
    (paramTy returnTy : CheckedTarget) :
    interpTarget (mkCallable paramTy returnTy) =
      .callable (interpTarget paramTy) (interpTarget returnTy) :=
  rfl

@[simp] theorem interpTarget_mkUnion
    (left right : CheckedTarget) :
    interpTarget (mkUnion left right) =
      .union (interpTarget left) (interpTarget right) :=
  rfl

@[simp] theorem interpTarget_mkIntersection
    (left right : CheckedTarget) :
    interpTarget (mkIntersection left right) =
      .intersection (interpTarget left) (interpTarget right) :=
  rfl

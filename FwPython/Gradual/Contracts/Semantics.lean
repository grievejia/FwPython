import FwPython.Gradual.Contracts.Compile

/-! ## Canonical meaning of boundary contracts -/

/-- The canonical gradual type corresponding to a boundary contract.
    This is a structural right inverse of `compileBoundaryRaw`: each
    contract constructor maps to its `GTy` counterpart, with `.unknown`
    mapping back to `.any` and `.negClass` mapping back to `.negClass`. -/
def boundaryMeaning : BoundaryContract → GTy
  | .unknown => .any
  | .class_ c => .class_ c
  | .callable d r => .callable (boundaryMeaning d) (boundaryMeaning r)
  | .union l r => .union (boundaryMeaning l) (boundaryMeaning r)
  | .intersection l r => .intersection (boundaryMeaning l) (boundaryMeaning r)
  | .bottom => .bottom
  | .negClass c => .negClass c

/-- `boundaryMeaning` is a right inverse of `compileBoundaryRaw`. -/
theorem compileBoundaryRaw_boundaryMeaning (c : BoundaryContract) :
    compileBoundaryRaw (boundaryMeaning c) = c := by
  induction c <;> simp [boundaryMeaning, compileBoundaryRaw, *]

/-- `boundaryMeaning` is a left inverse of `compileBoundaryRaw`. -/
theorem boundaryMeaning_compileBoundaryRaw (G : GTy) :
    boundaryMeaning (compileBoundaryRaw G) = G := by
  induction G <;> simp [boundaryMeaning, compileBoundaryRaw, *]

/-- For a normalized contract, `compileBoundary ∘ boundaryMeaning` is the identity. -/
theorem compileBoundary_boundaryMeaning (h : normalizeBoundary c = c) :
    compileBoundary (boundaryMeaning c) = c := by
  rw [compileBoundary, compileBoundaryRaw_boundaryMeaning, h]

/-! ## Normalization idempotence -/

/-- A boundary contract is normalized when `normalizeBoundary` is a fixpoint. -/
def BoundaryContract.IsNormalized (c : BoundaryContract) : Prop :=
  normalizeBoundary c = c

/-- The result of `normalizeBoundary` is always normalized. -/
theorem normalizeBoundary_idempotent (c : BoundaryContract) :
    (normalizeBoundary c).IsNormalized := by
  unfold BoundaryContract.IsNormalized
  induction c <;> simp_all [normalizeBoundary] <;> split <;> simp_all [normalizeBoundary]

/-- `compileBoundary` always produces a normalized contract. -/
theorem compileBoundary_isNormalized (g : GTy) :
    (compileBoundary g).IsNormalized :=
  normalizeBoundary_idempotent _

/-! ## Machine-facing type projection -/

/-- The machine-facing public type. With `negClass` as the only gradual
    negation, every negation is already class-atomic, so the projection is
    structural through every constructor. -/
def runtimePublicTy : GTy → GTy
  | .any => .any
  | .class_ C => .class_ C
  | .callable P R => .callable (runtimePublicTy P) (runtimePublicTy R)
  | .union G H => .union (runtimePublicTy G) (runtimePublicTy H)
  | .intersection G H => .intersection (runtimePublicTy G) (runtimePublicTy H)
  | .bottom => .bottom
  | .negClass C => .negClass C

@[simp] theorem runtimePublicTy_any : runtimePublicTy .any = .any := rfl
@[simp] theorem runtimePublicTy_class : runtimePublicTy (.class_ c) = .class_ c := rfl
@[simp] theorem runtimePublicTy_callable :
    runtimePublicTy (.callable P R) = .callable (runtimePublicTy P) (runtimePublicTy R) := rfl
@[simp] theorem runtimePublicTy_union :
    runtimePublicTy (.union G H) = .union (runtimePublicTy G) (runtimePublicTy H) := rfl
@[simp] theorem runtimePublicTy_intersection :
    runtimePublicTy (.intersection G H) =
      .intersection (runtimePublicTy G) (runtimePublicTy H) := rfl
@[simp] theorem runtimePublicTy_bottom : runtimePublicTy .bottom = .bottom := rfl
@[simp] theorem runtimePublicTy_negClass :
    runtimePublicTy (.negClass C) = .negClass C := rfl

theorem runtimePublicTy_id (G : GTy) : runtimePublicTy G = G := by
  induction G with
  | any | class_ _ | bottom | negClass _ => rfl
  | callable _ _ ihP ihR => simp [runtimePublicTy, ihP, ihR]
  | union _ _ ih₁ ih₂ => simp [runtimePublicTy, ih₁, ih₂]
  | intersection _ _ ih₁ ih₂ => simp [runtimePublicTy, ih₁, ih₂]

theorem runtimePublicTy_idempotent (G : GTy) :
    runtimePublicTy (runtimePublicTy G) = runtimePublicTy G := by
  induction G with
  | any | class_ _ | bottom | negClass _ => rfl
  | callable _ _ ihP ihR => simp [runtimePublicTy, ihP, ihR]
  | union _ _ ih₁ ih₂ => simp [runtimePublicTy, ih₁, ih₂]
  | intersection _ _ ih₁ ih₂ => simp [runtimePublicTy, ih₁, ih₂]

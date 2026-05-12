import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.Method.Lookup
import FwPython.Gradual.Checked.Core

/-! ## Checked typing judgment

The checked typing judgment assigns gradual types to checked expressions.
It mirrors the source typing judgment but additionally types the
checked-only forms (`enforce`, `dynAttrAccess`). The runtime-facing
`BoundaryContract` annotations are connected back to source types through
`CompilesBoundary`, keeping the contract/source correspondence explicit. -/

/-- A boundary contract corresponds to a source gradual type when the
    contract equals the structural (un-normalized) compiled form of that
    type. Using `compileBoundaryRaw` (instead of `compileBoundary`)
    guarantees `boundaryMeaning c = G`, which makes enforcement soundness
    provable by structural induction. -/
def CompilesBoundary (G : GTy) (c : BoundaryContract) : Prop :=
  c = compileBoundaryRaw G

/-! ## Checked type environment -/

/-- Checked type environment: maps variable names to gradual types.
    Checked typing is still expressed in terms of source gradual types. -/
abbrev CheckedTyEnv := GTyEnv

/-- Replace the first entry for key `k` with value `v`. -/
abbrev CheckedTyEnv.update : CheckedTyEnv → Identifier → GTy → CheckedTyEnv :=
  GTyEnv.update

/-! ## Checked typing judgment -/

/-- `CheckedHasType gct Γ e G` asserts that under gradual class table `gct`
    and type environment `Γ`, checked expression `e` has gradual type `G`.

    This judgment covers all source-level forms plus the checked-only
    forms `enforce` and `dynAttrAccess`. Dynamic source calls are not a
    primitive checked rule; they are represented as
    `call (enforce callee ...) arg` using the ordinary `call` rule after
    the callee has been enforced to a callable type. -/
inductive CheckedHasType : GClassTable → CheckedTyEnv → CheckedExpr → GTy → Prop where

  /-- Variable lookup. -/
  | var :
      Γ.lookup x = some G →
      CheckedHasType gct Γ (.var x) G

  /-- Constants. -/
  | constNone : CheckedHasType gct Γ .constNone (.class_ noneClass)
  | constTrue : CheckedHasType gct Γ .constTrue (.class_ boolClass)
  | constFalse : CheckedHasType gct Γ .constFalse (.class_ boolClass)

  /-- Object creation (only non-builtin classes are allocatable). -/
  | new :
      findGClass gct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      CheckedHasType gct Γ (.new cname) (.class_ cname)

  /-- Attribute access on a class receiver yields a bound-method object.
      The raw checked machine allocates a `BoundMethod` heap object, so the
      result type is `class_ boundMethodClass`. The callable interface is
      recovered through an explicit `enforce` in the elaboration. -/
  | attrAccess :
      CheckedHasType gct Γ base (.class_ cname) →
      FindGMethodType gct cname attrName paramTy returnTy →
      CheckedHasType gct Γ (.attrAccess base attrName) (.class_ boundMethodClass)

  /-- Attribute access on a union-of-class receiver yields a bound-method
      object. -/
  | attrAccessUnion :
      CheckedHasType gct Γ base (.union (.class_ c1) (.class_ c2)) →
      FindGMethodType gct c1 attrName p1 r1 →
      FindGMethodType gct c2 attrName p2 r2 →
      CheckedHasType gct Γ (.attrAccess base attrName) (.class_ boundMethodClass)

  /-- Ordinary call on a callable type. -/
  | call :
      CheckedHasType gct Γ callee
        (.callable (interpTarget paramTy) (interpTarget returnTy)) →
      CheckedHasType gct Γ arg argTy →
      AssignableTo gct argTy (interpTarget paramTy) →
      RuntimePublicCheckedTarget gct paramTy →
      RuntimePublicCheckedTarget gct returnTy →
      WellFormedGTy gct (interpTarget paramTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedHasType gct Γ (.call callee arg paramTy returnTy returnLabels)
        (interpTarget returnTy)

  /-- Ordinary conditional. The test must have exact type `class_ boolClass`.
      Dynamic tests go through an inserted `enforce` first; the elaboration
      ensures only exact-bool values reach the checked `cond`. The result
      type must lie in the admissible target fragment. -/
  | cond :
      CheckedHasType gct Γ condExpr (.class_ boolClass) →
      CheckedHasType gct Γ thenBranch R →
      CheckedHasType gct Γ elseBranch R →
      RuntimePublicAnnotation gct R →
      CheckedHasType gct Γ (.cond condExpr thenBranch elseBranch) R

  /-- Instance check. -/
  | isInstance :
      Γ.lookup x = some _ →
      findGClass gct C = some cls →
      CheckedHasType gct Γ (.isInstance x C) (.class_ boolClass)

  /-- Conditional + isinstance with type narrowing. Both narrowed
      types and the result type must lie in the admissible target fragment. -/
  | condIsInstance :
      Γ.lookup x = some T →
      findGClass gct C = some cls →
      RuntimePublicAnnotation gct R →
      RuntimePublicAnnotation gct (.intersection T (.class_ C)) →
      RuntimePublicAnnotation gct (.intersection T (.negClass C)) →
      CheckedHasType gct (Γ.update x (.intersection T (.class_ C))) thenBranch R →
      CheckedHasType gct (Γ.update x (.intersection T (.negClass C))) elseBranch R →
      CheckedHasType gct Γ (.cond (.isInstance x C) thenBranch elseBranch) R

  /-- Enforcement: if `e : G`, then `enforce e target labels :
      interpTarget target`. The target type must be
      well-formed and lie in the admissible target fragment. -/
  | enforce :
      CheckedHasType gct Γ e G →
      WellFormedGTy gct (interpTarget target) →
      RuntimePublicCheckedTarget gct target →
      CheckedHasType gct Γ (.enforce e target labels) (interpTarget target)

  /-- Dynamic attribute access: regardless of the receiver's checked
      input type, the result has type `any`. Blames `ℓ` at runtime if
      the attribute is missing. -/
  | dynAttrAccess :
      CheckedHasType gct Γ base G →
      CheckedHasType gct Γ (.dynAttrAccess base attrName ℓ) .any

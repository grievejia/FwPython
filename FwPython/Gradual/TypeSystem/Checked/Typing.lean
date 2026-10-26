import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore
import FwPython.Gradual.TypeSystem.IsInstanceRefinement
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

/-- Checked expression `e` has gradual type `G` under declarations `gct` and environment `Γ`.
All argument comparisons use the supplied structural data for the erased table.

    This judgment covers all source-level forms plus the checked-only
    forms `enforce` and `dynAttrAccess`. Dynamic source calls are not a
    primitive checked rule; they are represented as
    `call (enforce callee ...) arg` using the ordinary `call` rule after
    the callee has been enforced to a callable type. -/
inductive CheckedHasType (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) : CheckedTyEnv → CheckedExpr → GTy → Prop where

  /-- Variable lookup. -/
  | var :
      Γ.lookup x = some G →
      CheckedHasType gct structural Γ (.var x) G

  /-- Constants. -/
  | constNone : CheckedHasType gct structural Γ .constNone (.class_ noneClass)
  | constTrue : CheckedHasType gct structural Γ .constTrue (.class_ boolClass)
  | constFalse : CheckedHasType gct structural Γ .constFalse (.class_ boolClass)

  /-- Object creation (only non-builtin classes are allocatable). -/
  | new :
      findGClass gct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      CheckedHasType gct structural Γ (.new cname) (.class_ cname)

  /-- Attribute access on a class receiver yields a bound-method object.
      The raw checked machine allocates a `BoundMethod` heap object, so the
      result type is `class_ boundMethodClass`. The callable interface is
      recovered through an explicit `enforce` in the elaboration. -/
  | attrAccess :
      CheckedHasType gct structural Γ base (.class_ cname) →
      FindGMethodType gct cname attrName paramTy returnTy →
      CheckedHasType gct structural Γ (.attrAccess base attrName) (.class_ boundMethodClass)

  /-- Attribute access on a union-of-class receiver yields a bound-method
      object. -/
  | attrAccessUnion :
      CheckedHasType gct structural Γ base (.union (.class_ c1) (.class_ c2)) →
      FindGMethodType gct c1 attrName p1 r1 →
      FindGMethodType gct c2 attrName p2 r2 →
      CheckedHasType gct structural Γ (.attrAccess base attrName) (.class_ boundMethodClass)

  /-- Ordinary call on a callable type. -/
  | call :
      CheckedHasType gct structural Γ callee
        (.callable (interpTarget paramTy) (interpTarget returnTy)) →
      CheckedHasType gct structural Γ arg argTy →
      AssignableTo gct structural argTy (interpTarget paramTy) →
      CheckedTargetTy gct (interpTarget paramTy) →
      CheckedTargetTy gct (interpTarget returnTy) →
      WellFormedGTy gct (interpTarget paramTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedHasType gct structural Γ (.call callee arg paramTy returnTy returnObligation)
        (interpTarget returnTy)

  /-- Ordinary conditional. The test must have exact type `class_ boolClass`.
      Dynamic tests go through an inserted `enforce` first; the elaboration
      ensures only exact-bool values reach the checked `cond`. The result
      type must lie in the admissible target fragment. -/
  | cond :
      CheckedHasType gct structural Γ condExpr (.class_ boolClass) →
      CheckedHasType gct structural Γ thenBranch R →
      CheckedHasType gct structural Γ elseBranch R →
      CheckedTargetTy gct R →
      CheckedHasType gct structural Γ (.cond condExpr thenBranch elseBranch) R

  /-- Instance check. -/
  | isInstance :
      Γ.lookup x = some _ →
      findGClass gct C = some cls →
      CheckedHasType gct structural Γ (.isInstance x C) (.class_ boolClass)

  /-- Conditional + isinstance with type narrowing. Both narrowed
      types and the result type must lie in the admissible target fragment. -/
  | condIsInstance :
      Γ.lookup x = some T →
      findGClass gct C = some cls →
      CheckedTargetTy gct R →
      CheckedTargetTy gct (isInstanceThenRefinement T C) →
      CheckedTargetTy gct (isInstanceElseRefinement T C) →
      CheckedHasType gct structural (Γ.update x (isInstanceThenRefinement T C)) thenBranch R →
      CheckedHasType gct structural (Γ.update x (isInstanceElseRefinement T C)) elseBranch R →
      CheckedHasType gct structural Γ (.cond (.isInstance x C) thenBranch elseBranch) R

  /-- Enforcement: if `e : G`, then `enforce e target obligation :
      interpTarget target`. The target type must be
      well-formed and lie in the admissible target fragment. -/
  | enforce :
      CheckedHasType gct structural Γ e G →
      WellFormedGTy gct (interpTarget target) →
      CheckedTargetTy gct (interpTarget target) →
      CheckedHasType gct structural Γ (.enforce e target obligation) (interpTarget target)

  /-- Dynamic attribute access: regardless of the receiver's checked
      input type, the result has type `any`. Missing attributes produce
      checked-machine `BlameInfo` with the stored obligation and a missing-attribute
      cause. -/
  | dynAttrAccess :
      CheckedHasType gct structural Γ base G →
      CheckedHasType gct structural Γ (.dynAttrAccess base attrName obligation) .any

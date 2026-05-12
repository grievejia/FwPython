import FwPython.Common.Forall2
import FwPython.Gradual.TypeSystem.Checked.Shape
import FwPython.Gradual.TypeSystem.BoundaryPrecision
import FwPython.Gradual.TypeSystem.CheckedTargetPrecision
import FwPython.Gradual.Statics

/-! ## Step 5: Checked-Side Precision Relations -/

open Checked

/-! ### 5.1 Shape-Expression Precision -/

/-- Structural precision on label-erased checked expressions. Each
    constructor requires the same top-level shape; `call` and `enforce`
    carry precision on the embedded checked-target annotations. -/
inductive ShapeExprPrecision (gct : GClassTable) :
    ShapeExpr → ShapeExpr → Prop where
  | var :
      ShapeExprPrecision gct (.var x) (.var x)
  | new :
      ShapeExprPrecision gct (.new cname) (.new cname)
  | attrAccess :
      ShapeExprPrecision gct e₁ e₂ →
      ShapeExprPrecision gct (.attrAccess e₁ attr) (.attrAccess e₂ attr)
  | call :
      ShapeExprPrecision gct callee₁ callee₂ →
      ShapeExprPrecision gct arg₁ arg₂ →
      CompileTargetPrecision paramTy₁ paramTy₂ →
      CompileTargetPrecision resultTy₁ resultTy₂ →
      ShapeExprPrecision gct
        (.call callee₁ arg₁ paramTy₁ resultTy₁)
        (.call callee₂ arg₂ paramTy₂ resultTy₂)
  | constNone :
      ShapeExprPrecision gct .constNone .constNone
  | constTrue :
      ShapeExprPrecision gct .constTrue .constTrue
  | constFalse :
      ShapeExprPrecision gct .constFalse .constFalse
  | cond :
      ShapeExprPrecision gct test₁ test₂ →
      ShapeExprPrecision gct then₁ then₂ →
      ShapeExprPrecision gct else₁ else₂ →
      ShapeExprPrecision gct
        (.cond test₁ then₁ else₁)
        (.cond test₂ then₂ else₂)
  | isInstance :
      ShapeExprPrecision gct (.isInstance x cname) (.isInstance x cname)
  | enforce :
      ShapeExprPrecision gct e₁ e₂ →
      CompileTargetPrecision target₁ target₂ →
      ShapeExprPrecision gct (.enforce e₁ target₁) (.enforce e₂ target₂)
  | dynAttrAccess :
      ShapeExprPrecision gct e₁ e₂ →
      ShapeExprPrecision gct (.dynAttrAccess e₁ attr) (.dynAttrAccess e₂ attr)

theorem shapeExprPrecision_refl (gct : GClassTable) :
    ∀ (e : ShapeExpr), ShapeExprPrecision gct e e
  | .var _ => .var
  | .new _ => .new
  | .attrAccess e _ => .attrAccess (shapeExprPrecision_refl gct e)
  | .call callee arg _ _ =>
    .call (shapeExprPrecision_refl gct callee) (shapeExprPrecision_refl gct arg)
      (compileTargetPrecision_refl _) (compileTargetPrecision_refl _)
  | .constNone => .constNone
  | .constTrue => .constTrue
  | .constFalse => .constFalse
  | .cond t th el =>
    .cond (shapeExprPrecision_refl gct t) (shapeExprPrecision_refl gct th)
      (shapeExprPrecision_refl gct el)
  | .isInstance _ _ => .isInstance
  | .enforce e c =>
    .enforce (shapeExprPrecision_refl gct e) (compileTargetPrecision_refl c)
  | .dynAttrAccess e _ => .dynAttrAccess (shapeExprPrecision_refl gct e)

theorem shapeExprPrecision_trans {gct : GClassTable}
    {e₁ e₂ e₃ : ShapeExpr}
    (h₁ : ShapeExprPrecision gct e₁ e₂) (h₂ : ShapeExprPrecision gct e₂ e₃) :
    ShapeExprPrecision gct e₁ e₃ := by
  induction h₁ generalizing e₃ with
  | var => exact h₂
  | new => exact h₂
  | attrAccess _ ih => cases h₂ with | attrAccess h₂' => exact .attrAccess (ih h₂')
  | call _ _ hp hr ihc iha =>
    cases h₂ with | call hc' ha' hp' hr' =>
      exact .call
        (ihc hc')
        (iha ha')
        (compileTargetPrecision_trans hp hp')
        (compileTargetPrecision_trans hr hr')
  | constNone => exact h₂
  | constTrue => exact h₂
  | constFalse => exact h₂
  | cond _ _ _ iht ihth ihel =>
    cases h₂ with | cond ht' hth' hel' =>
      exact .cond (iht ht') (ihth hth') (ihel hel')
  | isInstance => exact h₂
  | enforce _ hc ihe =>
    cases h₂ with | enforce he' hc' =>
      exact .enforce (ihe he') (compileTargetPrecision_trans hc hc')
  | dynAttrAccess _ ih => cases h₂ with | dynAttrAccess h₂' => exact .dynAttrAccess (ih h₂')

/-! ### 5.2 Shape Methods, Classes, Programs -/

structure ShapeMethodPrecision (gct : GClassTable)
    (m₁ m₂ : ShapeMethod) : Prop where
  name_eq : m₁.name = m₂.name
  receiver_eq : m₁.receiverParam = m₂.receiverParam
  param_eq : m₁.param = m₂.param
  paramTy_prec : CheckedTargetPrecision m₁.paramTy m₂.paramTy
  returnTy_prec : CheckedTargetPrecision m₁.returnTy m₂.returnTy
  body_prec : ShapeExprPrecision gct m₁.body m₂.body

structure ShapeClassPrecision (gct : GClassTable)
    (c₁ c₂ : ShapeClass) : Prop where
  name_eq : c₁.name = c₂.name
  baseClasses_eq : c₁.baseClasses = c₂.baseClasses
  methods_prec : Forall₂ (ShapeMethodPrecision gct) c₁.methods c₂.methods

structure ShapeProgramPrecision (gct : GClassTable)
    (p₁ p₂ : ShapeProgram) : Prop where
  classes_prec : Forall₂ (ShapeClassPrecision gct) p₁.classes p₂.classes
  main_prec : ShapeExprPrecision gct p₁.main p₂.main

/-! ### 5.3 Raw checked-syntax precision aliases -/

/-- Runtime-facing checked-method precision is defined through label erasure
into the foundational shape relation. -/
abbrev CheckedMethodPrecision (gct : GClassTable)
    (m₁ m₂ : CheckedMethod) : Prop :=
  ShapeMethodPrecision gct (eraseLabelsMethod m₁) (eraseLabelsMethod m₂)

/-- Runtime-facing checked-class precision is defined through label erasure
into the foundational shape relation. -/
abbrev CheckedClassPrecision (gct : GClassTable)
    (c₁ c₂ : CheckedClass) : Prop :=
  ShapeClassPrecision gct (eraseLabelsClass c₁) (eraseLabelsClass c₂)

/-- Runtime-facing checked-class-table precision is defined through label
erasure into the foundational shape relation. -/
abbrev CheckedClassTablePrecision (gct : GClassTable)
    (cct₁ cct₂ : CheckedClassTable) : Prop :=
  Forall₂ (CheckedClassPrecision gct) cct₁ cct₂

/-- Runtime-facing checked-program precision is defined through label erasure
into the foundational shape relation. -/
abbrev CheckedProgramPrecision (gct : GClassTable)
    (p₁ p₂ : CheckedProgram) : Prop :=
  ShapeProgramPrecision gct (eraseLabelsProgram p₁) (eraseLabelsProgram p₂)

theorem shapeMethodPrecision_refl (gct : GClassTable) (m : ShapeMethod) :
    ShapeMethodPrecision gct m m :=
  ⟨rfl, rfl, rfl,
    checkedTargetPrecision_refl _,
    checkedTargetPrecision_refl _,
    shapeExprPrecision_refl gct m.body⟩

theorem shapeMethodPrecision_trans {gct : GClassTable}
    {m₁ m₂ m₃ : ShapeMethod}
    (h₁ : ShapeMethodPrecision gct m₁ m₂)
    (h₂ : ShapeMethodPrecision gct m₂ m₃) :
    ShapeMethodPrecision gct m₁ m₃ :=
  ⟨h₁.name_eq.trans h₂.name_eq,
   h₁.receiver_eq.trans h₂.receiver_eq,
   h₁.param_eq.trans h₂.param_eq,
   checkedTargetPrecision_trans h₁.paramTy_prec h₂.paramTy_prec,
   checkedTargetPrecision_trans h₁.returnTy_prec h₂.returnTy_prec,
   shapeExprPrecision_trans h₁.body_prec h₂.body_prec⟩

theorem shapeMethodPrecision_parameterContract_prec
    (h : ShapeMethodPrecision gct m₁ m₂) :
    CompiledBoundaryPrecision gct m₁.parameterContract m₂.parameterContract :=
  compiledBoundaryPrecision_of_checkedTargetPrecision h.paramTy_prec

theorem shapeMethodPrecision_parameterContract_prec_compat
    (h : ShapeMethodPrecision gct m₁ m₂)
    (_hcontract₁ : m₁.parameterContract = compileBoundaryRaw m₁.paramTy)
    (_hcontract₂ : m₂.parameterContract = compileBoundaryRaw m₂.paramTy) :
    CompiledBoundaryPrecision gct m₁.parameterContract m₂.parameterContract :=
  shapeMethodPrecision_parameterContract_prec h

theorem shapeMethodPrecision_returnContract_prec
    (h : ShapeMethodPrecision gct m₁ m₂) :
    CompiledBoundaryPrecision gct m₁.returnContract m₂.returnContract :=
  compiledBoundaryPrecision_of_checkedTargetPrecision h.returnTy_prec

theorem shapeMethodPrecision_returnContract_prec_compat
    (h : ShapeMethodPrecision gct m₁ m₂)
    (_hcontract₁ : m₁.returnContract = compileBoundaryRaw m₁.returnTy)
    (_hcontract₂ : m₂.returnContract = compileBoundaryRaw m₂.returnTy) :
    CompiledBoundaryPrecision gct m₁.returnContract m₂.returnContract :=
  shapeMethodPrecision_returnContract_prec h

theorem shapeClassPrecision_refl (gct : GClassTable) (c : ShapeClass) :
    ShapeClassPrecision gct c c :=
  ⟨rfl, rfl, forall₂_refl (shapeMethodPrecision_refl gct) c.methods⟩

theorem shapeClassPrecision_trans {gct : GClassTable}
    {c₁ c₂ c₃ : ShapeClass}
    (h₁ : ShapeClassPrecision gct c₁ c₂)
    (h₂ : ShapeClassPrecision gct c₂ c₃) :
    ShapeClassPrecision gct c₁ c₃ :=
  ⟨h₁.name_eq.trans h₂.name_eq,
   h₁.baseClasses_eq.trans h₂.baseClasses_eq,
   forall₂_trans (R := ShapeMethodPrecision gct)
     (fun _ _ _ => shapeMethodPrecision_trans) h₁.methods_prec h₂.methods_prec⟩

theorem shapeProgramPrecision_refl (gct : GClassTable) (p : ShapeProgram) :
    ShapeProgramPrecision gct p p :=
  ⟨forall₂_refl (shapeClassPrecision_refl gct) p.classes,
   shapeExprPrecision_refl gct p.main⟩

theorem shapeProgramPrecision_trans {gct : GClassTable}
    {p₁ p₂ p₃ : ShapeProgram}
    (h₁ : ShapeProgramPrecision gct p₁ p₂)
    (h₂ : ShapeProgramPrecision gct p₂ p₃) :
    ShapeProgramPrecision gct p₁ p₃ :=
  ⟨forall₂_trans (R := ShapeClassPrecision gct)
     (fun _ _ _ => shapeClassPrecision_trans) h₁.classes_prec h₂.classes_prec,
   shapeExprPrecision_trans h₁.main_prec h₂.main_prec⟩

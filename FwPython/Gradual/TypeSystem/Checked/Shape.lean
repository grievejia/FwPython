import FwPython.Gradual.Checked.Core

/-! ## Shape types and label-erasure functions

Label-erased counterparts of `CheckedExpr`, `CheckedMethod`, `CheckedClass`, and
`CheckedProgram`, together with erasure functions that strip blame labels while
preserving program structure. These are the building blocks for label-independent
structural comparison of checked programs. -/

open Checked

/-- Label-erased checked expression: same structure as `CheckedExpr`
    but with blame labels removed. -/
inductive ShapeExpr : Type where
  | var : Identifier → ShapeExpr
  | new : Identifier → ShapeExpr
  | attrAccess : ShapeExpr → Identifier → ShapeExpr
  | call : ShapeExpr → ShapeExpr → CheckedTarget → CheckedTarget → ShapeExpr
  | constNone : ShapeExpr
  | constTrue : ShapeExpr
  | constFalse : ShapeExpr
  | cond : ShapeExpr → ShapeExpr → ShapeExpr → ShapeExpr
  | isInstance : Identifier → Identifier → ShapeExpr
  | enforce : ShapeExpr → CheckedTarget → ShapeExpr
  | dynAttrAccess : ShapeExpr → Identifier → ShapeExpr
  deriving DecidableEq, Repr

/-- Label-erased checked method. -/
structure ShapeMethod where
  name : Identifier
  receiverParam : Identifier
  param : Identifier
  paramTy : CheckedTarget
  returnTy : CheckedTarget
  body : ShapeExpr
  deriving DecidableEq, Repr

namespace ShapeMethod

def parameterContract (m : ShapeMethod) : BoundaryContract :=
  compileBoundaryTarget m.paramTy

def returnContract (m : ShapeMethod) : BoundaryContract :=
  compileBoundaryTarget m.returnTy

@[simp] theorem parameterContract_eq
    (m : ShapeMethod) :
    m.parameterContract = compileBoundaryTarget m.paramTy :=
  rfl

@[simp] theorem returnContract_eq
    (m : ShapeMethod) :
    m.returnContract = compileBoundaryTarget m.returnTy :=
  rfl

end ShapeMethod

/-- Label-erased checked class. -/
structure ShapeClass where
  name : Identifier
  baseClasses : List Identifier
  methods : List ShapeMethod
  deriving DecidableEq, Repr

/-- Label-erased checked program. -/
structure ShapeProgram where
  classes : List ShapeClass
  main : ShapeExpr
  deriving DecidableEq, Repr

/-- Erase all blame labels from a checked expression. -/
def eraseLabelsExpr : CheckedExpr → ShapeExpr
  | .var x => .var x
  | .new c => .new c
  | .attrAccess e attr => .attrAccess (eraseLabelsExpr e) attr
  | .call callee arg p r _ => .call (eraseLabelsExpr callee) (eraseLabelsExpr arg) p r
  | .constNone => .constNone
  | .constTrue => .constTrue
  | .constFalse => .constFalse
  | .cond test thenBr elseBr =>
    .cond (eraseLabelsExpr test) (eraseLabelsExpr thenBr) (eraseLabelsExpr elseBr)
  | .isInstance x c => .isInstance x c
  | .enforce e c _ => .enforce (eraseLabelsExpr e) c
  | .dynAttrAccess e attr _ => .dynAttrAccess (eraseLabelsExpr e) attr

/-- Erase all blame labels from a checked method. -/
def eraseLabelsMethod (m : CheckedMethod) : ShapeMethod where
  name := m.name
  receiverParam := m.receiverParam
  param := m.param
  paramTy := m.paramTy
  returnTy := m.returnTy
  body := eraseLabelsExpr m.body

/-- Erase all blame labels from a checked class. -/
def eraseLabelsClass (c : CheckedClass) : ShapeClass where
  name := c.name
  baseClasses := c.baseClasses
  methods := c.methods.map eraseLabelsMethod

/-- Erase all blame labels from a checked program. -/
def eraseLabelsProgram (p : CheckedProgram) : ShapeProgram where
  classes := p.classes.map eraseLabelsClass
  main := eraseLabelsExpr p.main

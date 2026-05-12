import FwPython.Gradual.Checked.Core

/-! # Boundary origins

Core vocabulary for syntactic blame origins, plus the label-scope and
owner projections attached to each origin. -/

namespace Checked

/-- Syntactic origins for labels appearing in a compiled checked program. -/
inductive BoundaryOrigin : Type where
  | mainEnforce
      (exprPath : ExprPath)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  | mainDynAttr (exprPath : ExprPath)
  | mainCallReturn
      (exprPath : ExprPath)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  | methodParameter
      (definerName methodName : Identifier)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  | methodReturn
      (definerName methodName : Identifier)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  | methodBodyEnforce
      (definerName methodName : Identifier)
      (exprPath : ExprPath)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  | methodBodyDynAttr (definerName methodName : Identifier) (exprPath : ExprPath)
  | methodBodyCallReturn
      (definerName methodName : Identifier)
      (exprPath : ExprPath)
      (target : CheckedTarget)
      (p : BoundaryPath (compileBoundaryTarget target))
  deriving Repr, DecidableEq

def BoundaryOrigin.labelScope : BoundaryOrigin → LabelScope
  | .mainEnforce .. => .main
  | .mainDynAttr .. => .main
  | .mainCallReturn .. => .main
  | .methodParameter definerName methodName _ _ => .methodParameter definerName methodName
  | .methodReturn definerName methodName _ _ => .methodReturn definerName methodName
  | .methodBodyEnforce definerName methodName _ _ _ => .methodBody definerName methodName
  | .methodBodyDynAttr definerName methodName _ => .methodBody definerName methodName
  | .methodBodyCallReturn definerName methodName _ _ _ => .methodBody definerName methodName

def BoundaryOrigin.expectedOwner : BoundaryOrigin → BlameOwner
  | .mainEnforce _ _ p => p.ownerFrom .positive
  | .mainDynAttr _ => .context
  | .mainCallReturn _ _ p => p.ownerFrom .positive
  | .methodParameter _ _ _ p => p.ownerFrom .negative
  | .methodReturn _ _ _ p => p.ownerFrom .positive
  | .methodBodyEnforce _ _ _ _ p => p.ownerFrom .positive
  | .methodBodyDynAttr _ _ _ => .context
  | .methodBodyCallReturn _ _ _ _ p => p.ownerFrom .positive

end Checked

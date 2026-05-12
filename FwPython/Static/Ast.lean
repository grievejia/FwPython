import FwPython.Common.Identifier

/-! # Expression AST for the Mini Object-Oriented Language -/

/-- The language has the following kinds of expressions:
    - Variable reference
    - Object creation (`new ClassName`)
    - Attribute access (`base.attr_name`) — returns a bound method
    - Call expression (`callee(arg)`) — invokes an invokable value with one argument
    - Built-in constants (`NONE`, `TRUE`, `FALSE`)
    - Conditional expression (`if cond then x else y`)
    - Instance check (`isinstance(x, C)`) where `x` is a variable name -/
inductive Expr : Type where
  | var : Identifier → Expr
  | new : Identifier → Expr
  | attrAccess : Expr → Identifier → Expr
  | call : Expr → Expr → Expr
  | constNone : Expr
  | constTrue : Expr
  | constFalse : Expr
  | cond : Expr → Expr → Expr → Expr
  | isInstance : Identifier → Identifier → Expr
  deriving DecidableEq, Repr

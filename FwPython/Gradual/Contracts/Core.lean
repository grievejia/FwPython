import FwPython.Gradual.Types
import FwPython.Common.Identifier

/-! # Runtime boundary contracts

A runtime contract language separate from `GTy`. Contracts are the
compiled form of gradual type annotations: the checked runtime enforces
`BoundaryContract` values, never raw `GTy`. The `.unknown` contract is
the compiled form of `any` (the unknown fully static type) and acts as
a no-op boundary: no blame, no wrapper allocation, original value
returned unchanged. -/

/-! ## Contract types -/

/-- A boundary contract is the compiled runtime form of a gradual type
    annotation. The `.unknown` constructor corresponds to `any` and its
    derived forms: it carries no runtime obligation. The `.negClass`
    constructor mirrors `GTy.negClass`: gradual negation only targets
    class atoms, so the compiled form follows the same restriction. -/
inductive BoundaryContract where
  | unknown
  | class_ : Identifier → BoundaryContract
  | callable : BoundaryContract → BoundaryContract → BoundaryContract
  | union : BoundaryContract → BoundaryContract → BoundaryContract
  | intersection : BoundaryContract → BoundaryContract → BoundaryContract
  | bottom
  | negClass : Identifier → BoundaryContract
  deriving DecidableEq, Repr

/-- A callable boundary contract specifies the domain and codomain
    contracts for a callable enforcement boundary. -/
structure CallableBoundaryContract where
  domain : BoundaryContract
  codomain : BoundaryContract
  deriving DecidableEq, Repr

/-! ## Blame labels -/

/-- Boundary polarity follows ordinary contract polarity. Callable
    domains flip; all other constructors preserve polarity. -/
inductive BoundaryPolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Flip boundary polarity across a callable domain. -/
def BoundaryPolarity.flip : BoundaryPolarity → BoundaryPolarity
  | .positive => .negative
  | .negative => .positive

/-- Runtime blame is attributed either to the context or the provider. -/
inductive BlameOwner where
  | context
  | provider
  deriving DecidableEq, Repr

/-- Positive boundaries blame the provider; negative boundaries blame the context. -/
def BlameOwner.ofPolarity : BoundaryPolarity → BlameOwner
  | .positive => .provider
  | .negative => .context

/-- A label scope identifies which compiled region allocated a site range. -/
inductive LabelScope where
  | main
  | methodBody : Identifier → Identifier → LabelScope
  | methodParameter : Identifier → Identifier → LabelScope
  | methodReturn : Identifier → Identifier → LabelScope
  deriving DecidableEq, Repr

namespace LabelScope

@[simp] theorem main_ne_methodBody (definerName methodName : Identifier) :
    LabelScope.main ≠ LabelScope.methodBody definerName methodName := nofun

@[simp] theorem main_ne_methodParameter (definerName methodName : Identifier) :
    LabelScope.main ≠ LabelScope.methodParameter definerName methodName := nofun

@[simp] theorem main_ne_methodReturn (definerName methodName : Identifier) :
    LabelScope.main ≠ LabelScope.methodReturn definerName methodName := nofun

@[simp] theorem methodBody_ne_main (definerName methodName : Identifier) :
    LabelScope.methodBody definerName methodName ≠ LabelScope.main := nofun

@[simp] theorem methodParameter_ne_main (definerName methodName : Identifier) :
    LabelScope.methodParameter definerName methodName ≠ LabelScope.main := nofun

@[simp] theorem methodReturn_ne_main (definerName methodName : Identifier) :
    LabelScope.methodReturn definerName methodName ≠ LabelScope.main := nofun

@[simp] theorem methodBody_ne_methodParameter
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodBody definerName₁ methodName₁ ≠
      LabelScope.methodParameter definerName₂ methodName₂ := nofun

@[simp] theorem methodBody_ne_methodReturn
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodBody definerName₁ methodName₁ ≠
      LabelScope.methodReturn definerName₂ methodName₂ := nofun

@[simp] theorem methodParameter_ne_methodBody
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodParameter definerName₁ methodName₁ ≠
      LabelScope.methodBody definerName₂ methodName₂ := nofun

@[simp] theorem methodParameter_ne_methodReturn
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodParameter definerName₁ methodName₁ ≠
      LabelScope.methodReturn definerName₂ methodName₂ := nofun

@[simp] theorem methodReturn_ne_methodBody
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodReturn definerName₁ methodName₁ ≠
      LabelScope.methodBody definerName₂ methodName₂ := nofun

@[simp] theorem methodReturn_ne_methodParameter
    (definerName₁ methodName₁ definerName₂ methodName₂ : Identifier) :
    LabelScope.methodReturn definerName₁ methodName₁ ≠
      LabelScope.methodParameter definerName₂ methodName₂ := nofun

end LabelScope

/-- A blame label is identified by a compilation scope, a numeric site,
    and the owner determined by boundary polarity. -/
structure Label where
  scope : LabelScope
  site : Nat
  owner : BlameOwner
  deriving DecidableEq, Repr


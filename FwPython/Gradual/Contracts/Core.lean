import FwPython.Gradual.Types
import FwPython.Common.Identifier

/-! # Runtime boundary contracts

A runtime contract language separate from `GTy`. Contracts are the
compiled form of gradual type annotations: the checked runtime enforces
`BoundaryContract` values, never raw `GTy`. The `.unknown` contract is
the compiled form of `any` (the unknown fully static type) and acts as
a no-op boundary: no blame, no heap allocation, and the original value
is returned unchanged. -/

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

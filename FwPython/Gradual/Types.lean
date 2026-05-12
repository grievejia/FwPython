import FwPython.Common.Identifier

/-! # Gradual Types for the Mini Object-Oriented Language -/

/-- The gradual type language for FwPython.
    - `any` : an unknown fully static type — represents incomplete type information
    - `class_` : instance of class `C` or any subclass
    - `callable` : a bound method taking an argument of type `T` and returning type `U`
    - `union` : union type `T | U`
    - `intersection` : intersection type `T & U`
    - `bottom` : the empty type, subtype of everything
    - `negClass` : negation of a class — the only form of gradual negation.
      It may arise from `isInstance` refinement and may also appear in user
      annotations. General gradual negation is excluded by construction, so
      the only inhabitants are `negClass C`.

    The universal supertype is `class_ objectClass`, not a dedicated constructor. -/
inductive GTy : Type where
  | any : GTy
  | class_ : Identifier → GTy
  | callable : GTy → GTy → GTy
  | union : GTy → GTy → GTy
  | intersection : GTy → GTy → GTy
  | bottom : GTy
  | negClass : Identifier → GTy
  deriving DecidableEq, Repr

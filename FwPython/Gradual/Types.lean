import FwPython.Common.Identifier

/-! # Gradual Types for the Mini Object-Oriented Language -/

/-- The gradual type language for FwPython.
    - `any` : an unknown fully static type — represents incomplete type information
    - `class_` : instance of class `C` or any subclass
    - `callable` : a requirement for a bound method with accepted input type `T`
      and type `U` for every returned result. Calls may run forever;
      `T` and `U` can contain `any`
    - `union` : union type `T | U`
    - `intersection` : intersection type `T & U`
    - `bottom` : the empty type, subtype of everything
    - `negClass` : excludes class `C` and its subclasses; the object's actual class
      MRO must not contain `C`. It may arise from `isInstance` refinement or appear
      in user annotations. Exclusions are limited to class names.

    The universal supertype is `class_ objectClass`. -/
inductive GTy : Type where
  | any : GTy
  | class_ : Identifier → GTy
  | callable : GTy → GTy → GTy
  | union : GTy → GTy → GTy
  | intersection : GTy → GTy → GTy
  | bottom : GTy
  | negClass : Identifier → GTy
  deriving DecidableEq, Repr

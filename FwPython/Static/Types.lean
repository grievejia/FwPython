import FwPython.Common.Identifier

/-! # Types for the Mini Object-Oriented Language -/

/-- The static type language for FwPython.
    - `class_` : instance of class `C` or any subclass
    - `negClass` : excludes class `C` and its subclasses; the object's actual class
      MRO must not contain `C`. `ValueHasType.objRefNegClass` records this fact
      for a heap reference
    - `callable` : a requirement for a bound method with accepted input type `T`
      and type `U` for every returned result. Calls may run forever
    - `union` : union type `T | U`
    - `intersection` : intersection type `T & U`
    - `bottom` : the empty type, subtype of everything

    The universal supertype is `class_ objectClass`. -/
inductive Ty : Type where
  | class_ : Identifier → Ty
  | negClass : Identifier → Ty
  | callable : Ty → Ty → Ty
  | union : Ty → Ty → Ty
  | intersection : Ty → Ty → Ty
  | bottom : Ty
  deriving DecidableEq, Repr

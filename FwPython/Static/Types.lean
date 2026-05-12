import FwPython.Common.Identifier

/-! # Types for the Mini Object-Oriented Language -/

/-- The static type language for FwPython.
    - `class_` : instance of class `C` or any subclass
    - `negClass` : atom whose intended reading is "the runtime class's MRO
      excludes `C`"; the witness-carrying interpretation lives in
      the semantic subtyping denotation and `ValueHasType.objRefNegClass`
    - `callable` : a bound method taking an argument of type `T` and returning type `U`
    - `union` : union type `T | U`
    - `intersection` : intersection type `T & U`
    - `bottom` : the empty type, subtype of everything

    The universal supertype is `class_ objectClass`, not a dedicated constructor. -/
inductive Ty : Type where
  | class_ : Identifier → Ty
  | negClass : Identifier → Ty
  | callable : Ty → Ty → Ty
  | union : Ty → Ty → Ty
  | intersection : Ty → Ty → Ty
  | bottom : Ty
  deriving DecidableEq, Repr

/-- Structural size of static types. -/
def Ty.size : Ty → Nat
  | .class_ _ => 1
  | .negClass _ => 1
  | .callable paramTy returnTy => 1 + paramTy.size + returnTy.size
  | .union T U => 1 + T.size + U.size
  | .intersection T U => 1 + T.size + U.size
  | .bottom => 1

theorem Ty.size_pos (T : Ty) : 1 ≤ T.size := by
  cases T <;> simp [Ty.size] <;> omega

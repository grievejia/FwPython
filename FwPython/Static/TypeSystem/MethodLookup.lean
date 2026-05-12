import FwPython.Static.MRO.Lookup

/-! ## Method type resolution -/

/-- `FindMethodType ct cname methodName paramTy returnTy` holds when MRO lookup
    on class `cname` for `methodName` finds a method with the given signature. -/
abbrev FindMethodType (ct : ClassTable) (cname : Identifier)
    (methodName : Identifier) (paramTy returnTy : Ty) : Prop :=
  FindMethodTypeOf ComputeMro ct cname methodName paramTy returnTy

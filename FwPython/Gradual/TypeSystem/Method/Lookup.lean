import FwPython.Gradual.MRO.Lookup

/-! ## Gradual method type resolution -/

/-- `FindGMethodType gct cname methodName paramTy returnTy` holds when MRO lookup
    on class `cname` for `methodName` finds a gradual method with the given signature. -/
abbrev FindGMethodType (gct : GClassTable) (cname : Identifier)
    (methodName : Identifier) (paramTy returnTy : GTy) : Prop :=
  FindMethodTypeOf GComputeMro gct cname methodName paramTy returnTy

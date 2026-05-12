import FwPython.Gradual.Statics

/-! # Surface-static gradual embedding regression examples

The bridge `embedTy_gradualSubtype_iff` makes gradual subtyping
on the embedded surface fragment coincide with internal subtyping on
the erased class table. -/

example
    (gct : GClassTable) (T₁ T₂ : Ty) :
    GradualSubtype gct (embedTy T₁) (embedTy T₂) ↔
      IsSubtype (eraseClassTable gct) T₁ T₂ :=
  embedTy_gradualSubtype_iff gct T₁ T₂

example (s : Ty) : lowerBound (embedTy s) = s :=
  embedTy_lowerBound s

example (s : Ty) : upperBound (embedTy s) = s :=
  embedTy_upperBound s

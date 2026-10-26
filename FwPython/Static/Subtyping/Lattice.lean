import FwPython.Static.Subtyping.Core

/-! ## Lattice properties -/

open FwPython.Static.Subtyping

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- Union is the least upper bound: `T | U <: V` iff both `T <: V` and `U <: V`. -/
theorem subtype_union_iff :
    IsSubtype structural (.union T U) V ↔ IsSubtype structural T V ∧ IsSubtype structural U V :=
  ⟨fun h => ⟨.trans (.unionLeft (.refl h.sourceWellFormed.union_left) h.sourceWellFormed.union_right) h,
    .trans (.unionRight (.refl h.sourceWellFormed.union_right) h.sourceWellFormed.union_left) h⟩,
    fun ⟨h1, h2⟩ => .unionElim h1 h2⟩

/-- Intersection is the greatest lower bound: `V <: T & U` iff both `V <: T` and `V <: U`. -/
theorem subtype_inter_iff :
    IsSubtype structural V (.intersection T U) ↔ IsSubtype structural V T ∧ IsSubtype structural V U :=
  ⟨fun h => ⟨.trans h (.interLeft (.refl h.targetWellFormed.intersection_left) h.targetWellFormed.intersection_right),
    .trans h (.interRight (.refl h.targetWellFormed.intersection_right) h.targetWellFormed.intersection_left)⟩,
    fun ⟨h1, h2⟩ => .interIntro h1 h2⟩

/-- `T & U` is a subtype of `U & T`. -/
theorem subtype_inter_comm (validT : WellFormedTy ct T) (validU : WellFormedTy ct U) :
    IsSubtype structural (.intersection T U) (.intersection U T) :=
  TypeEquivalence.toSubtype (TypeEquivalence.intersectionCommutative
    (context := structural.typeContext)
    (T := validT.toType) (U := validU.toType))

/-- Intersection distributes over union.
    `T & (U | V) <: (T & U) | (T & V)` -/
theorem subtype_inter_union_distrib (validT : WellFormedTy ct T)
    (validU : WellFormedTy ct U) (validV : WellFormedTy ct V) :
    IsSubtype structural (.intersection T (.union U V))
      (.union (.intersection T U) (.intersection T V)) :=
  TypeEquivalence.toSubtype (TypeEquivalence.intersectionDistributes
    (context := structural.typeContext)
    (T := validT.toType) (U := validU.toType) (V := validV.toType))

/-- Union idempotence: `T | T <: T`. -/
theorem subtype_union_idem (validT : WellFormedTy ct T) :
    IsSubtype structural (.union T T) T :=
  TypeEquivalence.toSubtype (TypeEquivalence.unionIdempotent (context := structural.typeContext) (T := validT.toType))

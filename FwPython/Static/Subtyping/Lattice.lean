import FwPython.Static.Subtyping.Core

/-! ## Lattice properties -/

/-- Union is the least upper bound: `T | U <: V` iff both `T <: V` and `U <: V`. -/
theorem subtype_union_iff :
    IsSubtype ct (.union T U) V ↔ IsSubtype ct T V ∧ IsSubtype ct U V :=
  ⟨fun h => ⟨.trans (.unionLeft .refl) h, .trans (.unionRight .refl) h⟩, fun ⟨h1, h2⟩ => .unionElim h1 h2⟩

/-- Intersection is the greatest lower bound: `V <: T & U` iff both `V <: T` and `V <: U`. -/
theorem subtype_inter_iff :
    IsSubtype ct V (.intersection T U) ↔ IsSubtype ct V T ∧ IsSubtype ct V U :=
  ⟨fun h => ⟨.trans h (.interLeft .refl), .trans h (.interRight .refl)⟩, fun ⟨h1, h2⟩ => .interIntro h1 h2⟩

/-! ## Commutativity -/

/-- Intersection is commutative (as subtyping, not equality). -/
theorem subtype_inter_comm : IsSubtype ct (.intersection T U) (.intersection U T) :=
  .interIntro (.interRight .refl) (.interLeft .refl)

/-- Union is commutative (as subtyping, not equality). -/
theorem subtype_union_comm : IsSubtype ct (.union T U) (.union U T) :=
  .unionElim (.unionRight .refl) (.unionLeft .refl)

/-! ## Distributivity -/

/-- Intersection distributes over union (forward).
    `T & (U | V) <: (T & U) | (T & V)` -/
theorem subtype_inter_union_distrib :
    IsSubtype ct (.intersection T (.union U V))
      (.union (.intersection T U) (.intersection T V)) :=
  .interUnionDistrib

/-- Intersection distributes over union (reverse).
    `(T & U) | (T & V) <: T & (U | V)` -/
theorem subtype_union_inter_distrib :
    IsSubtype ct (.union (.intersection T U) (.intersection T V))
      (.intersection T (.union U V)) :=
  .unionElim (.interIntro (.interLeft .refl) (.unionLeft (.interRight .refl)))
    (.interIntro (.interLeft .refl) (.unionRight (.interRight .refl)))

/-- Union distributes over intersection (forward).
    `T | (U & V) <: (T | U) & (T | V)` -/
theorem subtype_union_inter_distrib' :
    IsSubtype ct (.union T (.intersection U V))
      (.intersection (.union T U) (.union T V)) :=
  .unionElim (.interIntro (.unionLeft .refl) (.unionLeft .refl))
    (.interIntro (.unionRight (.interLeft .refl)) (.unionRight (.interRight .refl)))

/-- Union distributes over intersection (reverse).
    `(T | U) & (T | V) <: T | (U & V)` -/
theorem subtype_inter_union_distrib' :
    IsSubtype ct (.intersection (.union T U) (.union T V))
      (.union T (.intersection U V)) :=
  .trans subtype_inter_union_distrib
    (.unionElim (.unionLeft (.interRight .refl))
      (.trans subtype_inter_comm (.trans subtype_inter_union_distrib
        (.unionElim (.unionLeft (.interRight .refl))
          (.unionRight (.interIntro (.interRight .refl) (.interLeft .refl)))))))


/-! ## Idempotence -/

/-- Union idempotence (forward): `T | T <: T`. -/
theorem subtype_union_idem : IsSubtype ct (.union T T) T :=
  .unionElim .refl .refl

/-- Union idempotence (reverse): `T <: T | T`. -/
theorem subtype_union_idem' : IsSubtype ct T (.union T T) :=
  .unionLeft .refl

/-- Intersection idempotence (forward): `T & T <: T`. -/
theorem subtype_inter_idem : IsSubtype ct (.intersection T T) T :=
  .interLeft .refl

/-- Intersection idempotence (reverse): `T <: T & T`. -/
theorem subtype_inter_idem' : IsSubtype ct T (.intersection T T) :=
  .interIntro .refl .refl

/-! ## Associativity -/

/-- Union associativity (forward): `(T | U) | V <: T | (U | V)`. -/
theorem subtype_union_assoc :
    IsSubtype ct (.union (.union T U) V) (.union T (.union U V)) :=
  .unionElim (.unionElim (.unionLeft .refl) (.unionRight (.unionLeft .refl)))
    (.unionRight (.unionRight .refl))

/-- Union associativity (reverse): `T | (U | V) <: (T | U) | V`. -/
theorem subtype_union_assoc' :
    IsSubtype ct (.union T (.union U V)) (.union (.union T U) V) :=
  .unionElim (.unionLeft (.unionLeft .refl))
    (.unionElim (.unionLeft (.unionRight .refl)) (.unionRight .refl))

/-- Intersection associativity (forward): `(T & U) & V <: T & (U & V)`. -/
theorem subtype_inter_assoc :
    IsSubtype ct (.intersection (.intersection T U) V) (.intersection T (.intersection U V)) :=
  .interIntro (.interLeft (.interLeft .refl))
    (.interIntro (.interLeft (.interRight .refl)) (.interRight .refl))

/-- Intersection associativity (reverse): `T & (U & V) <: (T & U) & V`. -/
theorem subtype_inter_assoc' :
    IsSubtype ct (.intersection T (.intersection U V)) (.intersection (.intersection T U) V) :=
  .interIntro (.interIntro (.interLeft .refl) (.interRight (.interLeft .refl)))
    (.interRight (.interRight .refl))

/-! ## Identity and Annihilator Laws -/

/-- Union identity (forward): `T | bottom <: T`. -/
theorem subtype_union_bottom : IsSubtype ct (.union T .bottom) T :=
  .unionElim .refl .bottom

/-- Union identity (reverse): `T <: T | bottom`. -/
theorem subtype_union_bottom' : IsSubtype ct T (.union T .bottom) :=
  .unionLeft .refl

/-- Intersection identity (forward): `T & class_ Object <: T`. -/
theorem subtype_inter_object : IsSubtype ct (.intersection T (.class_ objectClass)) T :=
  .interLeft .refl

/-- Intersection identity (reverse): `T <: T & class_ Object`. -/
theorem subtype_inter_object' : IsSubtype ct T (.intersection T (.class_ objectClass)) :=
  .interIntro .refl .objectTop

/-- Intersection annihilator (forward): `T & bottom <: bottom`. -/
theorem subtype_inter_bottom : IsSubtype ct (.intersection T .bottom) .bottom :=
  .interRight .refl

/-- Intersection annihilator (reverse): `bottom <: T & bottom`. -/
theorem subtype_inter_bottom' : IsSubtype ct .bottom (.intersection T .bottom) :=
  .bottom

/-- Union annihilator (forward): `T | class_ Object <: class_ Object`. -/
theorem subtype_union_object : IsSubtype ct (.union T (.class_ objectClass)) (.class_ objectClass) :=
  .unionElim .objectTop .refl

/-- Union annihilator (reverse): `class_ Object <: T | class_ Object`. -/
theorem subtype_union_object' : IsSubtype ct (.class_ objectClass) (.union T (.class_ objectClass)) :=
  .unionRight .refl

/-! ## Absorption -/

/-- Absorption (forward): `T & (T | U) <: T`. -/
theorem subtype_inter_union_absorb : IsSubtype ct (.intersection T (.union T U)) T :=
  .interLeft .refl

/-- Absorption (reverse): `T <: T & (T | U)`. -/
theorem subtype_inter_union_absorb' : IsSubtype ct T (.intersection T (.union T U)) :=
  .interIntro .refl (.unionLeft .refl)

/-- Absorption (forward): `T | (T & U) <: T`. -/
theorem subtype_union_inter_absorb : IsSubtype ct (.union T (.intersection T U)) T :=
  .unionElim .refl (.interLeft .refl)

/-- Absorption (reverse): `T <: T | (T & U)`. -/
theorem subtype_union_inter_absorb' : IsSubtype ct T (.union T (.intersection T U)) :=
  .unionLeft .refl

/-! ## Transitivity -/

/-- Transitivity: if `T <: U` and `U <: V`, then `T <: V`. -/
theorem subtype_trans (h1 : IsSubtype ct T U) (h2 : IsSubtype ct U V) :
    IsSubtype ct T V :=
  .trans h1 h2

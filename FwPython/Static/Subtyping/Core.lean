import FwPython.Static.MRO.Properties

/-! # Subtyping for the Mini Object-Oriented Language

Declarative subtyping relation parameterized by a class table.
Transitivity is primitive, so the relation serves as a specification-oriented
foundation for soundness and the class-only negative fragment. -/

/-! ## Leaf built-in classes -/

/-- A leaf built-in is one of the three designated built-in class names
    (`Bool`, `NoneType`, `BoundMethod`) together with evidence that it is
    sealed in the given class table — i.e. the only class whose MRO
    contains that name is the built-in itself.

    This is a factoring of the existing leaf invariants in
    `WellFormedClassTable` (`builtinsLeaf`, `noneLeaf`, `boundMethodLeaf`).
    Unlike the earlier generic `ClassesDisjoint` predicate, `LeafBuiltin`
    is restricted by construction to the three designated built-ins. It
    cannot be instantiated for arbitrary user-defined classes, so the
    resulting negative facts are open-world-safe. -/
inductive LeafBuiltin (ct : ClassTable) : Identifier → Prop where
  | bool :
      (∀ cname c mro, findClass ct cname = some c →
        ComputeMro ct c mro → boolClass ∈ mro → cname = boolClass) →
      LeafBuiltin ct boolClass
  | none :
      (∀ cname c mro, findClass ct cname = some c →
        ComputeMro ct c mro → noneClass ∈ mro → cname = noneClass) →
      LeafBuiltin ct noneClass
  | boundMethod :
      (∀ cname c mro, findClass ct cname = some c →
        ComputeMro ct c mro → boundMethodClass ∈ mro → cname = boundMethodClass) →
      LeafBuiltin ct boundMethodClass

/-- Extract the sealing property from a `LeafBuiltin` proof. -/
theorem LeafBuiltin.sealed (h : LeafBuiltin ct B) :
    ∀ cname c mro, findClass ct cname = some c →
      ComputeMro ct c mro → B ∈ mro → cname = B :=
  match h with
  | .bool hleaf => hleaf
  | .none hleaf => hleaf
  | .boundMethod hleaf => hleaf

/-- `IsSubtype ct T U` means `T` is a subtype of `U` under class table `ct`. -/
inductive IsSubtype : ClassTable → Ty → Ty → Prop where

  -- Group 1: Preorder

  /-- Reflexivity: every type is a subtype of itself. -/
  | refl :
      IsSubtype ct T T

  /-- Transitivity. -/
  | trans :
      IsSubtype ct T U →
      IsSubtype ct U V →
      IsSubtype ct T V

  -- Group 2: Bounded distributive lattice

  /-- Bottom is a subtype of every type. -/
  | bottom :
      IsSubtype ct .bottom T

  /-- Every type is a subtype of `class_ objectClass`. -/
  | objectTop :
      IsSubtype ct T (.class_ objectClass)

  /-- Intersection left projection: `T & U <: V` if `T <: V`. -/
  | interLeft :
      IsSubtype ct T V →
      IsSubtype ct (.intersection T U) V

  /-- Intersection right projection: `T & U <: V` if `U <: V`. -/
  | interRight :
      IsSubtype ct U V →
      IsSubtype ct (.intersection T U) V

  /-- Intersection on the right decomposes: `T <: U & V` if both `T <: U` and `T <: V`. -/
  | interIntro :
      IsSubtype ct T U →
      IsSubtype ct T V →
      IsSubtype ct T (.intersection U V)

  /-- Union on the left decomposes: `T | U <: V` if both `T <: V` and `U <: V`. -/
  | unionElim :
      IsSubtype ct T V →
      IsSubtype ct U V →
      IsSubtype ct (.union T U) V

  /-- Union left injection: `T <: U | V` if `T <: U`. -/
  | unionLeft :
      IsSubtype ct T U →
      IsSubtype ct T (.union U V)

  /-- Union right injection: `T <: U | V` if `T <: V`. -/
  | unionRight :
      IsSubtype ct T V →
      IsSubtype ct T (.union U V)

  /-- Forward distributivity of intersection over union. -/
  | interUnionDistrib :
      IsSubtype ct (.intersection T (.union U V))
        (.union (.intersection T U) (.intersection T V))

  -- Group 3: Nominal classes

  /-- Class subtyping via MRO. -/
  | class_ :
      findClass ct cname = some c →
      ComputeMro ct c mro →
      aname ∈ mro →
      IsSubtype ct (.class_ cname) (.class_ aname)

  -- Group 4: Arrows

  /-- Callable subtyping: contravariant in the parameter type,
      covariant in the return type. -/
  | callable :
      IsSubtype ct T' T →
      IsSubtype ct U U' →
      IsSubtype ct (.callable T U) (.callable T' U')

  /-- Every callable type is a subtype of `class_ BoundMethod`. -/
  | callableBoundMethod :
      findClass ct boundMethodClass = some bmCls →
      ComputeMro ct bmCls bmMro →
      IsSubtype ct (.callable P R) (.class_ boundMethodClass)

  /-- Callable intersections summarize to a callable with the unioned domain
      and intersected codomain:
      `(P → R) & (Q → S) <: (P | Q) → (R & S)`. -/
  | callableInterUnion :
      IsSubtype ct
        (.intersection (.callable P R) (.callable Q S))
        (.callable (.union P Q) (.intersection R S))

  -- Group 5: Class-only negative facts

  /-- Object-level excluded middle lifted from `class_ objectClass`:
      `class_ Object <: class_ C | negClass C`. -/
  | objectClassUnionNegClass :
      IsSubtype ct (.class_ objectClass) (.union (.class_ C) (.negClass C))

  /-- Designated leaf built-ins exclude every class outside their MRO. -/
  | sealedClassNegClass :
      LeafBuiltin ct B →
      findClass ct B = some bcls →
      ComputeMro ct bcls bmro →
      C ∉ bmro →
      IsSubtype ct (.class_ B) (.negClass C)

  /-- Every class contradicts its own negative atom. -/
  | classSelfNegClassBottom :
      IsSubtype ct (.intersection (.class_ C) (.negClass C)) .bottom

/-- Every type is a subtype of `class Object`. -/
theorem class_subtype_object :
    IsSubtype ct (.class_ cname) (.class_ objectClass) :=
  .objectTop

/-- A union of callables subsumes to a safe summary callable:
    `(P1 → R1) | (P2 → R2) <: (P1 & P2) → (R1 | R2)`. -/
theorem subtype_union_callable_summary :
    IsSubtype ct
      (.union (.callable p1 r1) (.callable p2 r2))
      (.callable (.intersection p1 p2) (.union r1 r2)) :=
  .unionElim (.callable (.interLeft .refl) (.unionLeft .refl))
    (.callable (.interRight .refl) (.unionRight .refl))

/-! ## Well-formedness -/

/-- A type is well-formed under a class table if every class name it mentions
    exists in the class table and has a valid MRO. -/
inductive WellFormedTy : ClassTable → Ty → Prop where
  | bottom : WellFormedTy ct .bottom
  | class_ : findClass ct cname = some c → ComputeMro ct c mro → WellFormedTy ct (.class_ cname)
  | negClass : findClass ct cname = some c → ComputeMro ct c mro → WellFormedTy ct (.negClass cname)
  | union : WellFormedTy ct T → WellFormedTy ct U → WellFormedTy ct (.union T U)
  | intersection : WellFormedTy ct T → WellFormedTy ct U → WellFormedTy ct (.intersection T U)
  | callable : WellFormedTy ct T → WellFormedTy ct U → WellFormedTy ct (.callable T U)

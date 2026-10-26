import FwPython.Static.Subtyping.Algebra

/-! # Static subtyping from type equations

A source type is a subtype when adding it as a union alternative leaves the target unchanged.
The lattice, function, and class equations derive the subtype rules in this module.
`WellFormedClassHierarchy` supplies the known class names and their valid MROs.
-/

open FwPython.Static.Subtyping

/-- Subtyping combines valid source and target annotations with the equation
that adding the source to the target union leaves the target unchanged.
The hierarchy supplies the class context and valid MROs. -/
def IsSubtype {ct : ClassTable} (structural : WellFormedClassHierarchy ct)
    (source target : Ty) : Prop :=
  TypeEquivalence.Subtype structural.typeContext source target

section

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

namespace IsSubtype

/-! Each subtype rule follows from the generated lattice, function, or class equations. -/

/-- Equal declaration lists and their unique hierarchy data give the same subtype judgment. -/
theorem transport {firstTable secondTable : ClassTable}
    {first : WellFormedClassHierarchy firstTable} {second : WellFormedClassHierarchy secondTable}
    {source target : Ty} (tablesEqual : firstTable = secondTable) :
    IsSubtype first source target ↔ IsSubtype second source target := by
  subst secondTable
  cases Subsingleton.elim first second
  rfl

/-- The source of every subtype proof is a valid type. -/
theorem sourceWellFormed (included : IsSubtype structural T U) : WellFormedTy ct T :=
  included.sourceNamesKnown

/-- The target of every subtype proof is a valid type. -/
theorem targetWellFormed (included : IsSubtype structural T U) : WellFormedTy ct U :=
  included.targetNamesKnown

/-- Every valid type is below itself. -/
theorem refl (valid : WellFormedTy ct T) : IsSubtype structural T T :=
  TypeEquivalence.Subtype.refl valid

/-- Subtype proofs compose within the same table context. -/
theorem trans (first : IsSubtype structural T U) (second : IsSubtype structural U V) : IsSubtype structural T V :=
  TypeEquivalence.Subtype.trans first second

/-- Bottom is below every valid type. -/
theorem bottom (valid : WellFormedTy ct T) : IsSubtype structural .bottom T :=
  TypeEquivalence.Subtype.bottom valid

/-- Object is above every valid type. -/
theorem objectTop (valid : WellFormedTy ct T) : IsSubtype structural T (.class_ objectClass) :=
  TypeEquivalence.Subtype.objectTop valid

/-- If the first component is below the target, its intersection with a valid type is also below it. -/
theorem interLeft (included : IsSubtype structural T V) (rightValid : WellFormedTy ct U) :
    IsSubtype structural (.intersection T U) V :=
  TypeEquivalence.Subtype.interLeft included rightValid

/-- If the second component is below the target, its intersection with a valid type is also below it. -/
theorem interRight (included : IsSubtype structural U V) (leftValid : WellFormedTy ct T) :
    IsSubtype structural (.intersection T U) V :=
  TypeEquivalence.Subtype.interRight included leftValid

/-- A type below both targets is below their intersection. -/
theorem interIntro (left : IsSubtype structural T U) (right : IsSubtype structural T V) :
    IsSubtype structural T (.intersection U V) :=
  TypeEquivalence.Subtype.interIntro left right

/-- A union is below the target when both alternatives are below it. -/
theorem unionElim (left : IsSubtype structural T V) (right : IsSubtype structural U V) :
    IsSubtype structural (.union T U) V :=
  TypeEquivalence.Subtype.unionElim left right

/-- A type below the left alternative is below the union. -/
theorem unionLeft (included : IsSubtype structural T U) (rightValid : WellFormedTy ct V) :
    IsSubtype structural T (.union U V) :=
  TypeEquivalence.Subtype.unionLeft included rightValid

/-- A type below the right alternative is below the union. -/
theorem unionRight (included : IsSubtype structural T V) (leftValid : WellFormedTy ct U) :
    IsSubtype structural T (.union U V) :=
  TypeEquivalence.Subtype.unionRight included leftValid

/-- Enlarging each alternative enlarges their union. -/
theorem unionMono (left : IsSubtype structural T U) (right : IsSubtype structural V W) :
    IsSubtype structural (.union T V) (.union U W) :=
  .unionElim (.unionLeft left right.targetWellFormed) (.unionRight right left.targetWellFormed)

/-- Enlarging each requirement enlarges their intersection. -/
theorem interMono (left : IsSubtype structural T U) (right : IsSubtype structural V W) :
    IsSubtype structural (.intersection T V) (.intersection U W) :=
  .interIntro (.interLeft left right.sourceWellFormed) (.interRight right left.sourceWellFormed)

/-- The class found by lookup is below each class in its computed MRO. -/
theorem class_ (lookup : findClass ct cname = some declaration)
    (computed : ComputeMro ct declaration linearization) (member : aname ∈ linearization) :
    IsSubtype structural (.class_ cname) (.class_ aname) := by
  have known := findClass_name_known lookup
  have ancestor := (structural.typeContext_mro lookup computed).symm ▸ member
  exact TypeEquivalence.Subtype.inheritance known ancestor

/-- Function subtyping reverses the input relation and preserves the result relation. -/
theorem callable (domain : IsSubtype structural Q P) (result : IsSubtype structural R S) :
    IsSubtype structural (.callable P R) (.callable Q S) :=
  TypeEquivalence.Subtype.callable domain result

/-- Every valid function type requires a callable value. -/
theorem callableBoundMethod (inputValid : WellFormedTy ct P) (resultValid : WellFormedTy ct R) :
    IsSubtype structural (.callable P R) (.class_ boundMethodClass) :=
  TypeEquivalence.Subtype.callableBoundMethod inputValid resultValid

/-- Every callable value satisfies a valid function requirement with an empty input. -/
theorem boundMethodEmptyDomain (resultValid : WellFormedTy ct R) :
    IsSubtype structural (.class_ boundMethodClass) (.callable .bottom R) :=
  TypeEquivalence.toSubtype (context := structural.typeContext)
    (TypeEquivalence.functionEmptyInput (context := structural.typeContext) (R := resultValid.toType)).symm

/-- Function types with the same valid input intersect their result types. -/
theorem callableSharedDomain (inputValid : WellFormedTy ct P)
    (leftValid : WellFormedTy ct R) (rightValid : WellFormedTy ct S) : IsSubtype structural
    (.intersection (.callable P R) (.callable P S)) (.callable P (.intersection R S)) :=
  TypeEquivalence.toSubtype (context := structural.typeContext)
    (TypeEquivalence.functionIntersectionResult (context := structural.typeContext)
      (P := inputValid.toType) (R := leftValid.toType) (S := rightValid.toType)).symm

/-- Two requirements of the same function accept the shared input and require both results. -/
theorem callableMeet (left : IsSubtype structural X (.callable P₁ R₁))
    (right : IsSubtype structural X (.callable P₂ R₂)) :
    IsSubtype structural X (.callable (.intersection P₁ P₂) (.intersection R₁ R₂)) :=
  .trans
    (.interIntro
      (.trans left (.callable
        (.interLeft (.refl left.targetWellFormed.callable_param) right.targetWellFormed.callable_param)
        (.refl left.targetWellFormed.callable_return)))
      (.trans right (.callable
        (.interRight (.refl right.targetWellFormed.callable_param) left.targetWellFormed.callable_param)
        (.refl right.targetWellFormed.callable_return))))
    (.callableSharedDomain
      (.intersection left.targetWellFormed.callable_param right.targetWellFormed.callable_param)
      left.targetWellFormed.callable_return right.targetWellFormed.callable_return)

/-- The intersection of `P -> R` and `Q -> S` lies below `(P | Q) -> (R | S)`.
The combined requirement covers both input alternatives and allows either result type. -/
theorem callableCorrelatedSummary (validP : WellFormedTy ct P) (validQ : WellFormedTy ct Q)
    (validR : WellFormedTy ct R) (validS : WellFormedTy ct S) : IsSubtype structural
    (.intersection (.callable P R) (.callable Q S)) (.callable (.union P Q) (.union R S)) :=
  .trans
    (.interIntro
      (.interLeft (.callable (.refl validP) (.unionLeft (.refl validR) validS)) (.callable validQ validS))
      (.interRight (.callable (.refl validQ) (.unionRight (.refl validS) validR)) (.callable validP validR)))
    (TypeEquivalence.toSubtype (context := structural.typeContext)
      (TypeEquivalence.functionUnionInput (context := structural.typeContext)
        (P := validP.toType) (Q := validQ.toType) (R := .union validR.toType validS.toType)).symm)

/-- A known class type or its complement covers Object. -/
theorem objectClassUnionNegClass (classValid : WellFormedTy ct (.class_ C)) : IsSubtype structural
    (.class_ objectClass) (.union (.class_ C) (.negClass C)) :=
  TypeEquivalence.toSubtype (context := structural.typeContext) (TypeEquivalence.classComplement
    (by cases classValid; assumption)).symm

/-- A sealed builtin excludes known classes outside its computed MRO. -/
theorem sealedClassNegClass (sealed : B ∈ sealedClasses)
    (lookup : findClass ct B = some declaration) (computed : ComputeMro ct declaration linearization)
    (excluded : C ∉ linearization) (classValid : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.class_ B) (.negClass C) := by
  cases classValid with
  | class_ known =>
      exact TypeEquivalence.Subtype.sealedClassNegClass sealed known
        (by simpa only [structural.typeContext_mro lookup computed] using excluded)

/-- A known class type contradicts its complement. -/
theorem classSelfNegClassBottom (classValid : WellFormedTy ct (.class_ C)) :
    IsSubtype structural (.intersection (.class_ C) (.negClass C)) .bottom :=
  TypeEquivalence.toSubtype (context := structural.typeContext) (TypeEquivalence.classContradiction
    (by cases classValid; assumption))

end IsSubtype

/-- A union of function types accepts inputs below both parameter types and unions their results. -/
theorem subtype_union_callable_summary (validP1 : WellFormedTy ct p1) (validP2 : WellFormedTy ct p2)
    (validR1 : WellFormedTy ct r1) (validR2 : WellFormedTy ct r2) : IsSubtype structural
    (.union (.callable p1 r1) (.callable p2 r2))
    (.callable (.intersection p1 p2) (.union r1 r2)) :=
  .unionElim (.callable (.interLeft (.refl validP1) validP2) (.unionLeft (.refl validR1) validR2))
    (.callable (.interRight (.refl validP2) validP1) (.unionRight (.refl validR2) validR1))

end

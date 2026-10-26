import FwPython.Static
import FwPython.Examples.Static.Subtyping

set_option autoImplicit false

/-! # Examples of subtyping from equations

These examples derive comparisons from the type equations.
`FwPython/Examples/Static/Subtyping.lean` checks subtype decisions, call inference,
and how typing the preallocated None reference justifies result inversion.
-/

namespace FwPython.Examples.Static.Algebra

open FwPython.Static.Subtyping
open FwPython.Examples.Static.Subtyping

/-- The validated context lists the sealed builtin Bool class. -/
private theorem boolKnown (context : ValidatedClassContext) : boolClass ∈ context.names :=
  context.valid.sealedKnown _ (by simp [sealedClasses])

/-- The validated Bool annotation supplied by the context's builtin declarations. -/
private def booleanTypePackage (context : ValidatedClassContext) : WellFormedType context.names :=
  .class_ boolClass (boolKnown context)

/-- The validated NoneType annotation supplied by the context's builtin declarations. -/
private def noneTypePackage (context : ValidatedClassContext) : WellFormedType context.names :=
  .class_ noneClass (context.valid.sealedKnown _ (by simp [sealedClasses]))

variable {context : ValidatedClassContext} {T U V P R S : WellFormedType context.names}

/-- Requiring Object adds no restriction to Bool. -/
example :
    TypeEquivalence context
      (.intersection (booleanTypePackage context) context.objectType)
      (booleanTypePackage context) := .intersectionObject

/-- Object absorbs every union alternative; this example applies that law to Bool. -/
example :
    TypeEquivalence context (.union (booleanTypePackage context) context.objectType)
      context.objectType := TypeEquivalence.unionObject

/-- Repeating a requirement does not change a type; this follows from absorption. -/
example : TypeEquivalence context (.intersection T T) T :=
  TypeEquivalence.intersectionIdempotent

/-- Repeating a union alternative does not change a type; this also follows from absorption. -/
example : TypeEquivalence context (.union T T) T :=
  TypeEquivalence.unionIdempotent

/-- A requirement combined with either alternative equals the two combined alternatives. -/
example : TypeEquivalence context (.intersection T (.union U V))
    (.union (.intersection T U) (.intersection T V)) :=
  .intersectionDistributes

/-- An Object-input, Bool-result function type is below a Bool-input, Object-result type. -/
example :
    TypeEquivalence.Subtype context (.callable objectType booleanType)
    (.callable booleanType objectType) :=
  .callable (.objectTop (booleanTypePackage context).namesKnown)
    (.objectTop (booleanTypePackage context).namesKnown)

/-- An empty input imposes no result restriction, regardless of the result type. -/
example :
    TypeEquivalence context (.callable .bottom R) context.boundMethodType :=
  .functionEmptyInput

/-- Two function requirements with the same input intersect their result types. -/
example : TypeEquivalence context (.intersection (.callable P R) (.callable P S))
    (.callable P (.intersection R S)) :=
  TypeEquivalence.functionIntersectionResult.symm

/-- Together, these requirements are below the Bool-or-NoneType input and result function type.
Each result is widened to Bool | NoneType; `functionUnionInput` then combines the
input types for that shared result. -/
example :
    TypeEquivalence.Subtype context correlated correlatedSummary := by
  have booleanKnown : TypeNamesKnown context.names booleanType := (booleanTypePackage context).namesKnown
  have noneKnown : TypeNamesKnown context.names noneType := (noneTypePackage context).namesKnown
  exact .trans
    (.interIntro
      (.interLeft (.callable (.refl booleanKnown) (.unionLeft (.refl booleanKnown) noneKnown)) (.callable noneKnown noneKnown))
      (.interRight (.callable (.refl noneKnown) (.unionRight (.refl noneKnown) booleanKnown))
        (.callable booleanKnown booleanKnown)))
    (TypeEquivalence.toSubtype (TypeEquivalence.functionUnionInput
      (P := booleanTypePackage context) (Q := noneTypePackage context)
      (R := .union (booleanTypePackage context) (noneTypePackage context))).symm)

/-- Sealed Bool and NoneType cannot share a value. -/
example : TypeEquivalence builtinContext
    (.intersection (booleanTypePackage builtinContext) (noneTypePackage builtinContext)) .bottom :=
  .sealedExclusion (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A class and its exclusion cover Object. -/
example :
    TypeEquivalence context (.union (booleanTypePackage context) (.negClass boolClass (boolKnown context)))
      context.objectType := .classComplement (boolKnown context)

/-- Adding a listed ancestor to a class does not change the class type. -/
example : TypeEquivalence builtinContext
    (.intersection (booleanTypePackage builtinContext) builtinContext.objectType)
    (booleanTypePackage builtinContext) :=
  .inheritance (by decide +kernel) (by decide +kernel)

/-- A nested function imposes no result restriction on an empty input.
The target result can be any valid type, independently of the source result. -/
example (result : WellFormedType builtinContext.names) : TypeEquivalence.Subtype builtinContext
    (nestedType 4) (WellFormedType.callable .bottom result).raw := by
  let nested : WellFormedType builtinContext.names := ⟨nestedType 3, by decide +kernel⟩
  have methodBound : TypeEquivalence.Subtype builtinContext
      (nestedType 4) builtinContext.boundMethodType.raw :=
    .trans (.callable (.bottom nested.namesKnown) (.refl nested.namesKnown))
      (TypeEquivalence.toSubtype (TypeEquivalence.functionEmptyInput (R := nested)))
  exact .trans methodBound
    (TypeEquivalence.toSubtype (TypeEquivalence.symm (TypeEquivalence.functionEmptyInput (R := result))))

end FwPython.Examples.Static.Algebra

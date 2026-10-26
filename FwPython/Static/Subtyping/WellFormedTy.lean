import FwPython.Static.Language
import FwPython.Static.MRO.Structure

/-! # Valid type annotations

A type is valid when each class name occurs in the class table. A structural
table supplies the MROs for those names. A package stores the annotation with
its name-validity proof, so type operations can preserve validity as they run.
-/

namespace FwPython.Static.Subtyping

/-- Every class type and class exclusion in the type names a listed class.
This checks names only. The hierarchy supplies their valid MROs. -/
inductive TypeNamesKnown (names : List Identifier) : Ty → Prop where
  /-- Bottom mentions no class. -/
  | bottom : TypeNamesKnown names .bottom
  /-- The class type names a listed class. -/
  | class_ {name : Identifier} (known : name ∈ names) : TypeNamesKnown names (.class_ name)
  /-- The exclusion names a listed class. -/
  | negClass {name : Identifier} (known : name ∈ names) : TypeNamesKnown names (.negClass name)
  /-- Both union alternatives mention only listed classes. -/
  | union {left right : Ty} (leftKnown : TypeNamesKnown names left)
      (rightKnown : TypeNamesKnown names right) : TypeNamesKnown names (.union left right)
  /-- Both intersection requirements mention only listed classes. -/
  | intersection {left right : Ty} (leftKnown : TypeNamesKnown names left)
      (rightKnown : TypeNamesKnown names right) : TypeNamesKnown names (.intersection left right)
  /-- Both the input and the result mention only listed classes. -/
  | callable {input result : Ty} (inputKnown : TypeNamesKnown names input)
      (resultKnown : TypeNamesKnown names result) : TypeNamesKnown names (.callable input result)

/-- Decide name validity by checking every class name in the type. -/
def typeNamesKnown_decidable (names : List Identifier) :
    (type : Ty) → Decidable (TypeNamesKnown names type)
  | .bottom => .isTrue .bottom
  | .class_ name =>
      decidable_of_iff (name ∈ names) ⟨TypeNamesKnown.class_, fun h => by cases h; assumption⟩
  | .negClass name =>
      decidable_of_iff (name ∈ names) ⟨TypeNamesKnown.negClass, fun h => by cases h; assumption⟩
  | .union left right =>
      letI := typeNamesKnown_decidable names left
      letI := typeNamesKnown_decidable names right
      decidable_of_iff (TypeNamesKnown names left ∧ TypeNamesKnown names right)
        ⟨fun h => .union h.1 h.2, fun h => by cases h; constructor <;> assumption⟩
  | .intersection left right =>
      letI := typeNamesKnown_decidable names left
      letI := typeNamesKnown_decidable names right
      decidable_of_iff (TypeNamesKnown names left ∧ TypeNamesKnown names right)
        ⟨fun h => .intersection h.1 h.2, fun h => by cases h; constructor <;> assumption⟩
  | .callable input result =>
      letI := typeNamesKnown_decidable names input
      letI := typeNamesKnown_decidable names result
      decidable_of_iff (TypeNamesKnown names input ∧ TypeNamesKnown names result)
        ⟨fun h => .callable h.1 h.2, fun h => by cases h; constructor <;> assumption⟩

/-- Name validity has a constructive decision for every raw type. -/
instance (names : List Identifier) (type : Ty) : Decidable (TypeNamesKnown names type) :=
  typeNamesKnown_decidable names type

/-- Type syntax together with proof that its class names are known.
Operations on packages preserve this proof as they construct each result. -/
structure WellFormedType (names : List Identifier) where
  /-- The type annotation represented by this package. -/
  raw : Ty
  /-- Each class type and exclusion in the annotation names a listed class. -/
  namesKnown : TypeNamesKnown names raw
  deriving DecidableEq

namespace WellFormedType

/-- Packages with equal syntax are equal; their proof fields add no data. -/
theorem ext {first second : WellFormedType names} (equal : first.raw = second.raw) :
    first = second := by
  cases first
  cases second
  cases equal
  rfl

/-- The empty type has no names to validate. -/
def bottom : WellFormedType names := ⟨.bottom, .bottom⟩

/-- The type of the given known class. -/
def class_ (name : Identifier) (known : name ∈ names) : WellFormedType names :=
  ⟨.class_ name, .class_ known⟩

/-- An exclusion of the given known class. -/
def negClass (name : Identifier) (known : name ∈ names) : WellFormedType names :=
  ⟨.negClass name, .negClass known⟩

/-- A class type when `positive` is true, and that class's exclusion otherwise.
The transparent package lets clients reduce either literal to its type constructor. -/
abbrev classLiteral (name : Identifier) (known : name ∈ names) (positive : Bool) : WellFormedType names :=
  ⟨if positive then .class_ name else .negClass name,
    by cases positive <;> constructor <;> exact known⟩

/-- Either of two valid type alternatives. -/
def union (left right : WellFormedType names) : WellFormedType names :=
  ⟨.union left.raw right.raw, .union left.namesKnown right.namesKnown⟩

/-- Both of two valid type requirements. -/
def intersection (left right : WellFormedType names) : WellFormedType names :=
  ⟨.intersection left.raw right.raw, .intersection left.namesKnown right.namesKnown⟩

/-- A function requirement with valid input and result types. -/
def callable (input result : WellFormedType names) : WellFormedType names :=
  ⟨.callable input.raw result.raw, .callable input.namesKnown result.namesKnown⟩

/-- All listed requirements, with Object for the empty list. -/
def meetTypes (objectKnown : objectClass ∈ names) :
    List (WellFormedType names) → WellFormedType names
  | [] => class_ objectClass objectKnown
  | head :: tail => intersection head (meetTypes objectKnown tail)

/-- All listed alternatives, with bottom for the empty list. -/
def joinTypes : List (WellFormedType names) → WellFormedType names
  | [] => bottom
  | head :: tail => union head (joinTypes tail)

end WellFormedType
end FwPython.Static.Subtyping

open FwPython.Static.Subtyping

/-- Each class type and exclusion uses a name occurring in the declaration table. -/
abbrev WellFormedTy (table : ClassTable) (type : Ty) : Prop :=
  TypeNamesKnown (table.map ClassDecl.name) type

/-- A successful class lookup validates the name in a class type. -/
theorem WellFormedTy.class_of_lookup (lookup : findClass table name = some declaration) :
    WellFormedTy table (.class_ name) :=
  .class_ (findClass_name_known lookup)

/-- A successful class lookup validates the name in a class exclusion. -/
theorem WellFormedTy.negClass_of_lookup (lookup : findClass table name = some declaration) :
    WellFormedTy table (.negClass name) :=
  .negClass (findClass_name_known lookup)

/-- Package a type with its name validity proof. -/
def WellFormedTy.toType (valid : WellFormedTy table type) :
    WellFormedType (table.map ClassDecl.name) := ⟨type, valid⟩

/-- Object is a valid type in a well-formed class hierarchy. -/
theorem WellFormedTy.object (structural : WellFormedClassHierarchy ct) :
    WellFormedTy ct (.class_ objectClass) :=
  WellFormedTy.class_of_lookup structural.objectExists.hfind

/-- Bool is a valid type in a well-formed class hierarchy. -/
theorem WellFormedTy.bool (structural : WellFormedClassHierarchy ct) :
    WellFormedTy ct (.class_ boolClass) :=
  WellFormedTy.class_of_lookup structural.boolExists.hfind

/-- NoneType is a valid type in a well-formed class hierarchy. -/
theorem WellFormedTy.none (structural : WellFormedClassHierarchy ct) :
    WellFormedTy ct (.class_ noneClass) :=
  WellFormedTy.class_of_lookup structural.noneExists.hfind

/-- BoundMethod is a valid type in a well-formed class hierarchy. -/
theorem WellFormedTy.boundMethod (structural : WellFormedClassHierarchy ct) :
    WellFormedTy ct (.class_ boundMethodClass) :=
  WellFormedTy.class_of_lookup structural.boundMethodExists.hfind

namespace FwPython.Static.Subtyping.TypeNamesKnown

/-- The first union alternative mentions only known classes. -/
theorem union_left (known : TypeNamesKnown names (.union left right)) : TypeNamesKnown names left := by
  cases known; assumption

/-- The second union alternative mentions only known classes. -/
theorem union_right (known : TypeNamesKnown names (.union left right)) : TypeNamesKnown names right := by
  cases known; assumption

/-- The first intersection requirement mentions only known classes. -/
theorem intersection_left (known : TypeNamesKnown names (.intersection left right)) : TypeNamesKnown names left := by
  cases known; assumption

/-- The second intersection requirement mentions only known classes. -/
theorem intersection_right (known : TypeNamesKnown names (.intersection left right)) : TypeNamesKnown names right := by
  cases known; assumption

/-- The function input mentions only known classes. -/
theorem callable_param (known : TypeNamesKnown names (.callable input result)) : TypeNamesKnown names input := by
  cases known; assumption

/-- The function result mentions only known classes. -/
theorem callable_return (known : TypeNamesKnown names (.callable input result)) : TypeNamesKnown names result := by
  cases known; assumption

/-- The class type corresponding to a valid exclusion uses the same known name. -/
theorem class_of_neg (known : TypeNamesKnown names (.negClass name)) : TypeNamesKnown names (.class_ name) := by
  cases known with
  | negClass known => exact .class_ known

/-- The exclusion corresponding to a valid class type uses the same known name. -/
theorem neg_of_class (known : TypeNamesKnown names (.class_ name)) : TypeNamesKnown names (.negClass name) := by
  cases known with
  | class_ known => exact .negClass known

end FwPython.Static.Subtyping.TypeNamesKnown

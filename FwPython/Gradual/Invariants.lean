import FwPython.Gradual.MRO
import FwPython.Builtins

/-! # Raw gradual class-table invariants

Runtime-only invariants for the gradual class table. These do not include
method typing, Liskov conditions, or any typing-related constraints.
Those belong to a future milestone. -/

/-- Constructive lookup witness for a gradual class name together with its MRO. -/
abbrev GClassLookupWitness (ct : GClassTable) (cname : Identifier) :=
  ClassLookupWitnessOf findGClass GComputeMro ct cname

/-- Constructive MRO witness for an already chosen gradual class. -/
abbrev GClassMroWitness (ct : GClassTable) (cls : GClass) :=
  ClassMroWitnessOf GComputeMro ct cls

/-- Constructive witness that `Object` exists and has no explicit bases. -/
abbrev GObjectExistsWitness (ct : GClassTable) :=
  ObjectExistsWitnessOf findGClass ClassDecl.baseClasses objectClass ct

instance gClassLookupWitness_subsingleton :
    Subsingleton (GClassLookupWitness ct cname) :=
  ClassLookupWitnessOf.subsingleton gComputeMro_determinism

instance gClassMroWitness_subsingleton :
    Subsingleton (GClassMroWitness ct cls) :=
  ClassMroWitnessOf.subsingleton gComputeMro_determinism

instance gObjectExistsWitness_subsingleton :
    Subsingleton (GObjectExistsWitness ct) :=
  ObjectExistsWitnessOf.subsingleton

/-- A well-formed gradual class table satisfies the basic structural invariants
    required by the runtime. -/
structure WellFormedGClassTable (ct : GClassTable) where
  /-- Object exists in the class table and has no explicit base class. -/
  objectExists : GObjectExistsWitness ct
  /-- Bool exists in the class table with a valid MRO. -/
  boolExists : GClassLookupWitness ct boolClass
  /-- NoneType exists in the class table with a valid MRO. -/
  noneExists : GClassLookupWitness ct noneClass
  /-- BoundMethod exists in the class table with a valid MRO. -/
  boundMethodExists : GClassLookupWitness ct boundMethodClass
  /-- Every class in the table has a valid MRO (no cycles). -/
  allMrosExist : ∀ cname c,
    findGClass ct cname = some c → GClassMroWitness ct c
  /-- Class names in the class table are unique. -/
  classNamesUnique : ∀ c₁ c₂,
    c₁ ∈ ct → c₂ ∈ ct → c₁.name = c₂.name → c₁ = c₂
  /-- Direct parent lists are duplicate-free. -/
  baseClassesDistinct : ∀ cname c,
    findGClass ct cname = some c → c.baseClasses.Nodup
  /-- A selected class whose MRO contains a sealed builtin is that builtin itself. -/
  sealedLeaf : ∀ builtin, builtin ∈ sealedClasses → ∀ cname c mro, findGClass ct cname = some c →
    GComputeMro ct c mro → builtin ∈ mro → cname = builtin

instance wellFormedGClassTable_subsingleton :
    Subsingleton (WellFormedGClassTable ct) :=
  ⟨fun ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ => by
    congr 1 <;>
      first
      | exact Subsingleton.elim _ _
      | (funext _ _ _; exact Subsingleton.elim _ _)⟩

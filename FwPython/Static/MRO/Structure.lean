import FwPython.Static.MRO.Properties

/-! # Class lookup and inheritance data

Lookup selects the first declaration with the requested class name.
Later declarations with the same name do not add ancestors.
`WellFormedClassHierarchy` records the selected classes, their MROs, and sealed
builtin classes. These inheritance facts support subtyping before method typing
is defined. `WellTypedClassHierarchy` combines the hierarchy with method typing
and declaration consistency. -/

/-- A selected class declaration, its method resolution order (MRO), and proofs of lookup and MRO computation. -/
abbrev ClassLookupWitness (ct : ClassTable) (cname : Identifier) :=
  ClassLookupWitnessOf findClass ComputeMro ct cname

/-- The MRO of an already selected class and its computation proof. -/
abbrev ClassMroWitness (ct : ClassTable) (cls : Class) :=
  ClassMroWitnessOf ComputeMro ct cls

/-- The selected Object declaration and proof that it has no explicit parents. -/
abbrev ObjectExistsWitness (ct : ClassTable) :=
  ObjectExistsWitnessOf findClass ClassDecl.baseClasses objectClass ct

instance classLookupWitness_subsingleton : Subsingleton (ClassLookupWitness ct cname) :=
  ClassLookupWitnessOf.subsingleton determinism

instance classMroWitness_subsingleton : Subsingleton (ClassMroWitness ct cls) :=
  ClassMroWitnessOf.subsingleton determinism

instance objectExistsWitness_subsingleton : Subsingleton (ObjectExistsWitness ct) :=
  ObjectExistsWitnessOf.subsingleton

/-- The validated inheritance hierarchy of `ct`: selected class declarations,
computed MROs, and restrictions on sealed builtin classes.
Subtyping uses these facts before method bodies are typechecked. -/
structure WellFormedClassHierarchy (ct : ClassTable) where
  /-- The selected Object declaration has no explicit parents. -/
  objectExists : ObjectExistsWitness ct
  /-- The selected Bool declaration exists with a successful MRO. -/
  boolExists : ClassLookupWitness ct boolClass
  /-- The selected NoneType declaration exists with a successful MRO. -/
  noneExists : ClassLookupWitness ct noneClass
  /-- The selected BoundMethod declaration exists with a successful MRO. -/
  boundMethodExists : ClassLookupWitness ct boundMethodClass
  /-- Each selected class has a stored MRO and computation proof. -/
  allMrosExist : ∀ cname c, findClass ct cname = some c → ClassMroWitness ct c
  /-- A selected class whose MRO contains a sealed builtin is that builtin itself. -/
  sealedLeaf : ∀ builtin, builtin ∈ sealedClasses → ∀ cname c mro, findClass ct cname = some c →
    ComputeMro ct c mro → builtin ∈ mro → cname = builtin

/-- Deterministic lookup and MRO computation give the same data in any two records for this table. -/
instance wellFormedClassHierarchy_subsingleton : Subsingleton (WellFormedClassHierarchy ct) :=
  ⟨fun ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ => by
    congr 1 <;>
      first
      | exact Subsingleton.elim _ _
      | (funext _ _ _; exact Subsingleton.elim _ _)⟩

/-- Each selected declaration has an MRO. -/
theorem WellFormedClassHierarchy.allMrosExist_exists (structural : WellFormedClassHierarchy ct) :
    ∀ cname c, findClass ct cname = some c → ∃ mro, ComputeMro ct c mro :=
  fun _ _ hfind => (structural.allMrosExist _ _ hfind).exists

/-- The selected BoundMethod declaration exists. -/
theorem WellFormedClassHierarchy.boundMethodExists_find (structural : WellFormedClassHierarchy ct) :
    ∃ c, findClass ct boundMethodClass = some c :=
  structural.boundMethodExists.exists_find

/-- Look up a name known to occur in the table and return its declaration and MRO. -/
def WellFormedClassHierarchy.lookupKnown (structural : WellFormedClassHierarchy ct)
    (name : Identifier) (known : name ∈ ct.map ClassDecl.name) :
    ClassLookupWitness ct name :=
  match lookup : findClass ct name with
  | some declaration =>
    ⟨declaration, (structural.allMrosExist name declaration lookup).mro, lookup,
      (structural.allMrosExist name declaration lookup).hmro⟩
  | none => False.elim (by
    obtain ⟨declaration, member, equal⟩ := List.mem_map.mp known
    exact (findByName_eq_none_iff.mp lookup) declaration member equal)

import FwPython.Static.Language
import FwPython.Builtins
import FwPython.Static.MRO.Structure

set_option autoImplicit false

/-! # Class contexts for type equations

A context lists known class names and their method resolution orders (MROs).
Each MRO is a list of class names that determines the order of method lookup.
Validity requires each MRO to contain its own class and Object, known ancestors,
distinct names within each MRO, preservation of ancestor order, and sealed builtin
classes.
Well-formed class hierarchies supply these facts from their validated declarations.
Names repeat when several declarations share a name. Lookup uses the first declaration,
so repeated names refer to the same class.

`classMros` collects the MROs for known names in its `members` argument.
`hasValidClassOrder` uses C3 to decide whether one order without repeated names
contains those MROs in order. A failed merge rules out a common subclass: its MRO would have to
preserve the ancestor order of each requested class.
-/

namespace FwPython.Static.Subtyping

/-- Known class names and their ordered MRO lists. -/
structure ClassContext where
  /-- Known class names. The list can contain repetitions. -/
  names : List Identifier
  /-- The MRO assigned to each name, in method resolution order.
  `classContextOf` puts the class itself first and assigns `[]` to unknown names. -/
  ancestors : Identifier → List Identifier

/-- Inheritance, MRO order, and sealed class requirements for the class context. -/
structure ValidContext (context : ClassContext) : Prop where
  /-- The context contains each sealed builtin class. -/
  sealedKnown : ∀ name, name ∈ sealedClasses → name ∈ context.names
  /-- Every known class is one of its own ancestors. -/
  selfAncestor : ∀ name, name ∈ context.names → name ∈ context.ancestors name
  /-- Every known class inherits Object. -/
  objectAncestor : ∀ name, name ∈ context.names → objectClass ∈ context.ancestors name
  /-- Each ancestor of a known class is a known class. -/
  ancestorsKnown : ∀ name, name ∈ context.names →
    ∀ ancestor, ancestor ∈ context.ancestors name → ancestor ∈ context.names
  /-- Each class MRO contains no repeated name. -/
  ancestorDistinct : ∀ name, name ∈ context.names → (context.ancestors name).Nodup
  /-- Each ancestor's complete MRO occurs in the child's MRO in the same order. -/
  ancestorOrder : ∀ name, name ∈ context.names →
    ∀ ancestor, ancestor ∈ context.ancestors name →
      (context.ancestors ancestor).Sublist (context.ancestors name)
  /-- A known class inheriting a sealed builtin is that builtin itself. -/
  sealed : ∀ builtin, builtin ∈ sealedClasses →
    ∀ name, name ∈ context.names → builtin ∈ context.ancestors name → name = builtin

/-- Object is known because Bool is known and inherits Object. -/
theorem ValidContext.objectKnown {context : ClassContext} (valid : ValidContext context) :
    objectClass ∈ context.names :=
  valid.ancestorsKnown boolClass (valid.sealedKnown _ (by simp [sealedClasses])) _
    (valid.objectAncestor _ (valid.sealedKnown _ (by simp [sealedClasses])))

/-- BoundMethod is known because the context contains each sealed builtin. -/
theorem ValidContext.boundMethodKnown {context : ClassContext} (valid : ValidContext context) :
    boundMethodClass ∈ context.names := valid.sealedKnown _ (by simp [sealedClasses])

/-- Class names and MROs together with the facts required by the type equations. -/
structure ValidatedClassContext extends ClassContext where
  /-- The context's names and MROs obey inheritance, order, and sealed class requirements. -/
  valid : ValidContext toClassContext

/-- A validated context exposes its known names and ordered MROs. -/
instance : Coe ValidatedClassContext ClassContext := ⟨ValidatedClassContext.toClassContext⟩

/-- The MROs for names occurring in both `context.names` and `members`.
Filtering the context's names makes the query independent of the order and
repetitions in `members`. -/
def classMros (context : ClassContext) (members : List Identifier) : List (List Identifier) :=
  (context.names.filter (fun name => members.contains name)).map context.ancestors

/-- Check whether the known classes in `members` share a common MRO order: a list
without repeated names that contains each MRO in order. C3 merges these MROs;
success supplies such an order, and failure rules one out. -/
def hasValidClassOrder (context : ClassContext) (members : List Identifier) : Bool :=
  (c3Merge (classMros context members)).isSome

/-- A common distinct-name order proves that the known classes in `members`
pass C3. -/
theorem hasValidClassOrder_of_sublist {context : ClassContext} {members : List Identifier}
    (order : List Identifier) (distinct : order.Nodup)
    (inputs : ∀ name, name ∈ context.names → name ∈ members →
      (context.ancestors name).Sublist order) : hasValidClassOrder context members = true := by
  apply c3Merge_of_common_order order distinct
  intro input member
  obtain ⟨name, included, rfl⟩ := List.mem_map.mp member
  have facts := List.mem_filter.mp included
  exact inputs name facts.1 (List.contains_iff_mem.mp facts.2)

/-- Each known class in `members` has its full MRO in the successful common order. -/
theorem classMro_sublist {context : ClassContext} {members order : List Identifier}
    (merged : c3Merge (classMros context members) = some order)
    {name : Identifier} (known : name ∈ context.names) (present : name ∈ members) :
    (context.ancestors name).Sublist order :=
  c3Merge_sublist merged _ (List.mem_map.mpr ⟨name,
    List.mem_filter.mpr ⟨known, List.contains_iff_mem.mpr present⟩, rfl⟩)

/-- Every name in a successful common order belongs to the MRO of a known class
in `members`. -/
theorem classMro_of_mem_order {context : ClassContext} {members order : List Identifier}
    (merged : c3Merge (classMros context members) = some order)
    {name : Identifier} (present : name ∈ order) :
    ∃ className, className ∈ context.names ∧ className ∈ members ∧ name ∈ context.ancestors className := by
  obtain ⟨_, chosen, inherited⟩ := c3Merge_sound merged name present
  obtain ⟨className, member, rfl⟩ := List.mem_map.mp chosen
  have knownAndIncluded := List.mem_filter.mp member
  exact ⟨className, knownAndIncluded.1, List.contains_iff_mem.mp knownAndIncluded.2, inherited⟩

/-- A successful common-order check supplies the order returned by C3. -/
theorem hasValidClassOrder_exists {context : ClassContext} {members : List Identifier}
    (accepted : hasValidClassOrder context members = true) :
    ∃ order, c3Merge (classMros context members) = some order :=
  Option.isSome_iff_exists.mp accepted

/-- Removing classes from the requested list preserves a common MRO order. -/
theorem hasValidClassOrder_of_subset {context : ClassContext} {source target : List Identifier}
    (accepted : hasValidClassOrder context source = true)
    (subset : ∀ name, name ∈ context.names → name ∈ target → name ∈ source) :
    hasValidClassOrder context target = true := by
  obtain ⟨order, merged⟩ := hasValidClassOrder_exists accepted
  exact hasValidClassOrder_of_sublist order (c3Merge_nodup merged)
    (fun name known present => classMro_sublist merged known (subset name known present))

/-- Record known class names and the MRO of the first declaration found for each name.
An unknown class name is assigned an empty ancestor list. -/
def classContextOf (table : ClassTable) (wellFormed : WellFormedClassHierarchy table) : ClassContext where
  names := table.map ClassDecl.name
  ancestors name := match lookup : findClass table name with
    | some declaration => (wellFormed.allMrosExist name declaration lookup).mro
    | none => []

/-- Every known name has a declaration; lookup returns the first match. -/
theorem known_lookup {table : ClassTable} (structural : WellFormedClassHierarchy table)
    {name : Identifier} (known : name ∈ (classContextOf table structural).names) :
    ∃ declaration, findClass table name = some declaration :=
  (structural.lookupKnown name known).exists_find

/-- A known class's ancestor list equals the computed MRO of its first declaration. -/
theorem context_ancestors {table : ClassTable} (wellFormed : WellFormedClassHierarchy table)
    {name : Identifier} {declaration : Class} (lookup : findClass table name = some declaration) :
    (classContextOf table wellFormed).ancestors name = (wellFormed.allMrosExist name declaration lookup).mro := by
  unfold classContextOf
  dsimp only
  split
  · rename_i actual found
    have equal : actual = declaration := Option.some.inj (found.symm.trans lookup)
    subst actual
    rfl
  · rename_i missing
    rw [lookup] at missing
    cases missing

/-- An unknown class name has an empty ancestor list. -/
theorem context_missing {table : ClassTable} (structural : WellFormedClassHierarchy table)
    {name : Identifier} (missing : findClass table name = none) :
    (classContextOf table structural).ancestors name = [] := by
  unfold classContextOf
  dsimp only
  split
  · rename_i _ lookup
    rw [missing] at lookup
    cases lookup
  · rfl

/-- The class table's MRO and builtin rules imply the context requirements. -/
theorem classContextOf_valid (table : ClassTable) (wellFormed : WellFormedClassHierarchy table) :
    ValidContext (classContextOf table wellFormed) := by
  have ancestorKnown : ∀ name, name ∈ (classContextOf table wellFormed).names →
      ∀ ancestor, ancestor ∈ (classContextOf table wellFormed).ancestors name →
        ancestor ∈ (classContextOf table wellFormed).names := by
    intro name known ancestor inherited
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    rw [context_ancestors wellFormed lookup] at inherited
    obtain ⟨_, _, ancestorLookup, _⟩ := mro_member_wellFormedClass
      wellFormed.allMrosExist_exists (findClass_self lookup)
      (wellFormed.allMrosExist name declaration lookup).hmro inherited
    exact findClass_name_known ancestorLookup
  refine ⟨?_, ?_, ?_, ancestorKnown, ?_, ?_, ?_⟩
  · intro name member
    simp only [sealedClasses, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact findClass_name_known wellFormed.boolExists.hfind
    · exact findClass_name_known wellFormed.noneExists.hfind
    · exact findClass_name_known wellFormed.boundMethodExists.hfind
  · intro name known
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    rw [context_ancestors wellFormed lookup]
    simpa [findClass_name lookup] using mro_self_mem (wellFormed.allMrosExist name declaration lookup).hmro
  · intro name known
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    rw [context_ancestors wellFormed lookup]
    exact mro_contains_object (wellFormed.allMrosExist name declaration lookup).hmro
  · intro name known
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    rw [context_ancestors wellFormed lookup]
    exact mro_nodup (findClass_self lookup) (wellFormed.allMrosExist name declaration lookup).hmro
  · intro name known ancestor inherited
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    obtain ⟨ancestorDeclaration, ancestorLookup⟩ := known_lookup wellFormed
      (ancestorKnown name known ancestor inherited)
    rw [context_ancestors wellFormed lookup] at inherited ⊢
    rw [context_ancestors wellFormed ancestorLookup]
    exact mro_sublist table declaration ancestorDeclaration _ _ (findClass_self lookup)
      (wellFormed.allMrosExist name declaration lookup).hmro (findClass_self ancestorLookup)
      (wellFormed.allMrosExist ancestor ancestorDeclaration ancestorLookup).hmro
      (by simpa [findClass_name ancestorLookup] using inherited)
  · intro builtin sealed name known inherited
    obtain ⟨declaration, lookup⟩ := known_lookup wellFormed known
    rw [context_ancestors wellFormed lookup] at inherited
    exact wellFormed.sealedLeaf builtin sealed name declaration _ lookup
      (wellFormed.allMrosExist name declaration lookup).hmro inherited

end FwPython.Static.Subtyping

/-- The validated type-equation context of a well-formed class hierarchy. -/
def WellFormedClassHierarchy.typeContext {table : ClassTable} (structural : WellFormedClassHierarchy table) :
    FwPython.Static.Subtyping.ValidatedClassContext :=
  ⟨FwPython.Static.Subtyping.classContextOf table structural,
    FwPython.Static.Subtyping.classContextOf_valid table structural⟩

/-- The validated type context records the declaration's computed MRO. -/
theorem WellFormedClassHierarchy.typeContext_mro {table : ClassTable}
    (structural : WellFormedClassHierarchy table)
    {name : Identifier} {declaration : Class} {linearization : List Identifier}
    (lookup : findClass table name = some declaration)
    (computed : ComputeMro table declaration linearization) :
    structural.typeContext.ancestors name = linearization := by
  change (FwPython.Static.Subtyping.classContextOf table structural).ancestors name = linearization
  rw [FwPython.Static.Subtyping.context_ancestors structural lookup]
  exact determinism (structural.allMrosExist name declaration lookup).hmro computed

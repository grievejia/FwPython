import FwPython.Static.Subtyping.ClassIntersection

set_option autoImplicit false

/-! # Class hierarchy extensions and complete class conjunctions

`classIntersectionOfExtension` projects a class in a structurally valid extension
to its complete class conjunction over the original names. Conversely,
`extendWithClassIntersection` realizes every conjunction that satisfies the
conjunction constraints. It uses an existing sealed builtin or adds one fresh
empty-method class. Each conjunction has its own extension.

`ValidExtension.noCommonClass` rules out a common subclass when the requested
ancestor MROs have no common order. These guarantees concern class structure;
static program typing also requires typed methods and Liskov compatibility.
-/

namespace FwPython.Static.Subtyping

/-- Appended declarations with valid MROs and builtin sealing in the combined hierarchy.
Full program typing additionally requires method-body typing and compatible
inherited methods under LiskovCondition. -/
structure ValidExtension (table : ClassTable) where
  /-- Class declarations placed after the original table's declarations. -/
  added : ClassTable
  /-- The combined table contains Object, Bool, NoneType and BoundMethod.
  The first declaration found for each known name has a computed MRO, and
  the table obeys builtin sealing. -/
  structural : WellFormedClassHierarchy (table ++ added)

/-- A class name with the first declaration found for it and its computed MRO in the extension. -/
abbrev ValidExtension.SelectedClass {table : ClassTable} (extension : ValidExtension table) :=
  (name : Identifier) × ClassLookupWitness (table ++ extension.added) name

/-- An original ancestor's MRO occurs in the selected extension class's MRO.
Appending preserves its declaration and computed MRO, so MRO sublist inclusion applies. -/
private theorem originalMro_sublist {table : ClassTable} (structural : WellFormedClassHierarchy table)
    (extension : ValidExtension table) {className name : Identifier}
    (selected : ClassLookupWitness (table ++ extension.added) className)
    (known : name ∈ structural.typeContext.names) (present : name ∈ selected.mro) :
    (structural.typeContext.ancestors name).Sublist selected.mro := by
  let ancestor := structural.lookupKnown name known
  let preserved := findClass_append_preserved table extension.added
  rw [structural.typeContext_mro ancestor.hfind ancestor.hmro]
  exact mro_sublist (table ++ extension.added) selected.cls ancestor.cls selected.mro ancestor.mro
    (findClass_self selected.hfind) selected.hmro (findClass_self (preserved _ _ ancestor.hfind))
    (ComputeMro.transport preserved ancestor.hmro)
    (by simpa [findClass_name ancestor.hfind] using present)

/-- Extract the selected class's included original names as a complete class conjunction.
Appending preserves original lookups and MROs. The included names respect
inheritance, sealed builtins, and the selected class's MRO order. -/
def classIntersectionOfExtension {table : ClassTable} (structural : WellFormedClassHierarchy table)
    (extension : ValidExtension table) {className : Identifier}
    (selected : ClassLookupWitness (table ++ extension.added) className) :
    ClassIntersection structural.typeContext := by
  let context := structural.typeContext
  let preserved := findClass_append_preserved table extension.added
  have valid := context.valid
  let members := context.names.filter (fun name => selected.mro.contains name)
  have included (name : Identifier) : name ∈ members ↔ name ∈ context.names ∧ name ∈ selected.mro := by
    simp [members]
  refine ⟨members, (fun present => ((included _).mp present).1), ?_, ?_, ?_, ?_⟩
  · exact (included objectClass).mpr ⟨valid.objectKnown, mro_contains_object selected.hmro⟩
  · intro name known present ancestor inherited
    exact (included ancestor).mpr ⟨valid.ancestorsKnown name known ancestor inherited,
      (originalMro_sublist structural extension selected known ((included name).mp present).2).subset inherited⟩
  · intro builtin sealed present name known
    have isBuiltin := extension.structural.sealedLeaf builtin sealed className selected.cls selected.mro
      selected.hfind selected.hmro ((included builtin).mp present).2
    let original := structural.lookupKnown builtin (valid.sealedKnown builtin sealed)
    have selectedLookup : findClass (table ++ extension.added) builtin = some selected.cls := isBuiltin ▸ selected.hfind
    have equalClasses : selected.cls = original.cls :=
      Option.some.inj (selectedLookup.symm.trans (preserved _ _ original.hfind))
    have equalMros : selected.mro = original.mro :=
      determinism (equalClasses ▸ selected.hmro) (ComputeMro.transport preserved original.hmro)
    rw [included, structural.typeContext_mro original.hfind original.hmro, ← equalMros]
    exact ⟨And.right, fun present => ⟨known, present⟩⟩
  · exact hasValidClassOrder_of_sublist selected.mro
      (mro_nodup (findClass_self selected.hfind) selected.hmro)
      (fun name known present => originalMro_sublist structural extension selected known ((included name).mp present).2)

/-- The projected conjunction includes exactly the original names in the selected class's MRO. -/
theorem classIntersectionOfExtension_includesClass {table : ClassTable} (structural : WellFormedClassHierarchy table)
    (extension : ValidExtension table) {className : Identifier}
    (selected : ClassLookupWitness (table ++ extension.added) className) (name : Identifier) :
    name ∈ (classIntersectionOfExtension structural extension selected).includedClasses ↔
      name ∈ structural.typeContext.names ∧ name ∈ selected.mro := by
  simp [classIntersectionOfExtension]

/-- Construct an empty-method subclass using the complete conjunction's common MRO order.
The dependent pair contains the declaration and its computed MRO; its proof records
the fresh declaration name and exactly the original class names in that MRO. -/
private def prepareSubclass {table : ClassTable} (structural : WellFormedClassHierarchy table)
    (fresh : Identifier) (conjunction : ClassIntersection structural.typeContext) :
    { prepared : (declaration : Class) × ClassMroWitness table declaration //
      prepared.1.name = fresh ∧
        ∀ name, name ∈ prepared.2.mro ↔ name = fresh ∨ name ∈ conjunction.includedClasses } := by
  let context := structural.typeContext
  match merged : c3Merge (classMros context conjunction.includedClasses) with
  | none => exact False.elim (by
      obtain ⟨_, successful⟩ := hasValidClassOrder_exists conjunction.constraints.orderCompatible
      cases merged.symm.trans successful)
  | some order =>
    have orderMembers (name : Identifier) : name ∈ order ↔ name ∈ conjunction.includedClasses := by
      constructor
      · intro present
        obtain ⟨parent, parentKnown, parentIncluded, inherited⟩ := classMro_of_mem_order merged present
        exact conjunction.constraints.inheritance parent parentKnown parentIncluded name inherited
      · intro present
        exact (classMro_sublist merged (conjunction.namesKnown present) present).subset
          (context.valid.selfAncestor name (conjunction.namesKnown present))
    have orderKnown (name : Identifier) (present : name ∈ order) : name ∈ context.names :=
      conjunction.namesKnown ((orderMembers name).mp present)
    have nonempty : order ≠ [] := by
      intro empty
      have present := (orderMembers objectClass).mpr conjunction.constraints.objectMember
      rw [empty] at present
      cases present
    have parents : ∀ bases : List Identifier, (∀ name, name ∈ bases → name ∈ context.names) →
        AllParentMros table bases (bases.map context.ancestors) := by
      intro bases
      induction bases with
      | nil => intro _; exact .nil
      | cons parent _ ih =>
        intro known
        obtain ⟨declaration, lookup⟩ := known_lookup structural (known parent (.head _))
        apply AllParentMros.cons lookup
        · have computed := (structural.allMrosExist parent declaration lookup).hmro
          simpa only [context, structural.typeContext_mro lookup computed] using computed
        · exact ih (fun name present => known name (.tail _ present))
    -- The direct-base order is also a merge input, so the parent merge returns it exactly.
    have mergedAgain : c3Merge (order.map context.ancestors ++ [order]) = some order := by
      apply c3Merge_of_full_order order (c3Merge_nodup merged)
      · intro input member
        rcases List.mem_append.mp member with member | member
        · obtain ⟨parent, present, rfl⟩ := List.mem_map.mp member
          exact classMro_sublist merged (orderKnown parent present) ((orderMembers parent).mp present)
        · have equal : input = order := by simpa using member
          subst input
          exact .refl _
      · exact List.mem_append_right _ (.head _)
    let declaration : Class := ⟨fresh, order, []⟩
    refine ⟨⟨declaration, ⟨fresh :: order, ?_⟩⟩, rfl, ?_⟩
    · apply ComputeMro.step (bases := order) (parentMros := order.map context.ancestors)
      · simp [declaration, ClassDecl.resolvedBases, List.isEmpty_iff, nonempty]
      · exact nonempty
      · exact parents order orderKnown
      · exact mergedAgain
    · intro name
      simp only [List.mem_cons, orderMembers]

/-- A fresh class name whose byte size exceeds every name in the original table. -/
private def freshName (table : ClassTable) : Identifier :=
  String.ofList (List.replicate
    (table.foldr (fun declaration total => declaration.name.utf8ByteSize + total) 0 + 1) '#')

/-- No original declaration can have the larger byte size assigned to a new name. -/
private theorem freshName_missing (table : ClassTable) :
    findClass table (freshName table) = none := by
  apply findByName_eq_none_iff.mpr
  intro declaration member equal
  have bound : declaration.name.utf8ByteSize ≤
      table.foldr (fun declaration total => declaration.name.utf8ByteSize + total) 0 := by
    clear equal
    induction table with
    | nil => cases member
    | cons _ _ ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have := ih member
        omega
  have freshSize : (freshName table).utf8ByteSize =
      table.foldr (fun declaration total => declaration.name.utf8ByteSize + total) 0 + 1 := by
    unfold freshName
    generalize table.foldr (fun declaration total => declaration.name.utf8ByteSize + total) 0 + 1 = count
    induction count with
    | zero => rfl
    | succ _ ih =>
      rw [List.replicate_succ', String.ofList_append, String.utf8ByteSize_append, ih]
      rfl
  have lengths := congrArg String.utf8ByteSize equal
  rw [freshSize] at lengths
  omega

/-- Realize one complete class conjunction by a selected class in a valid appended table.
A conjunction including a sealed builtin uses that builtin without adding declarations.
A conjunction with no sealed builtin adds one fresh class with empty methods
and only original direct parents. -/
def extendWithClassIntersection {table : ClassTable} (structural : WellFormedClassHierarchy table)
    (conjunction : ClassIntersection structural.typeContext) :
    { realization : (extension : ValidExtension table) × extension.SelectedClass //
      ∀ name, name ∈ table.map ClassDecl.name →
        (name ∈ realization.2.2.mro ↔ name ∈ conjunction.includedClasses) } := by
  have valid := structural.typeContext.valid
  match chosen : sealedClasses.find? conjunction.includesClass with
  | some builtin =>
      have sealed := List.mem_of_find?_eq_some chosen
      have present := (conjunction.includesClass_iff_mem builtin).mp (List.find?_some chosen)
      let original := structural.lookupKnown builtin (valid.sealedKnown builtin sealed)
      let extension : ValidExtension table :=
        ⟨[], by simpa only [List.append_nil] using structural⟩
      let selected : ClassLookupWitness (table ++ extension.added) builtin :=
        ⟨original.cls, original.mro,
          by simpa only [extension, List.append_nil] using original.hfind,
          by simpa only [extension, List.append_nil] using original.hmro⟩
      refine ⟨⟨extension, ⟨builtin, selected⟩⟩, ?_⟩
      intro name known
      have sameClasses := conjunction.constraints.sealing builtin sealed present name known
      rw [structural.typeContext_mro original.hfind original.hmro] at sameClasses
      exact sameClasses.symm
  | none =>
      have unsealed (builtin : Identifier) (sealed : builtin ∈ sealedClasses) :
          builtin ∉ conjunction.includedClasses :=
        fun present => List.find?_eq_none.mp chosen builtin sealed
          ((conjunction.includesClass_iff_mem builtin).mpr present)
      let prepared := prepareSubclass structural (freshName table) conjunction
      let declaration := prepared.val.1
      let computed := prepared.val.2
      let added : ClassTable := [declaration]
      let preserved := findClass_append_preserved table added
      have newLookup : findClass (table ++ added) (freshName table) = some declaration := by
        rw [findClass_append, freshName_missing, ← prepared.property.1]
        exact findClass_of_mem (by simp [added]) List.mem_cons_self
      let liftOriginal {name : Identifier} (selected : ClassLookupWitness table name) :
          ClassLookupWitness (table ++ added) name :=
        ⟨selected.cls, selected.mro, preserved _ _ selected.hfind,
          ComputeMro.transport preserved selected.hmro⟩
      let extendedStructural : WellFormedClassHierarchy (table ++ added) :=
        { objectExists := ⟨structural.objectExists.cls, preserved _ _ structural.objectExists.hfind,
            structural.objectExists.hbases⟩
          boolExists := liftOriginal structural.boolExists
          noneExists := liftOriginal structural.noneExists
          boundMethodExists := liftOriginal structural.boundMethodExists
          allMrosExist := by
            intro name candidate lookup
            cases originalLookup : findClass table name with
            | some original =>
                have equal : original = candidate :=
                  Option.some.inj ((preserved _ _ originalLookup).symm.trans lookup)
                subst candidate
                let originalMro := structural.allMrosExist name original originalLookup
                exact ⟨originalMro.mro, ComputeMro.transport preserved originalMro.hmro⟩
            | none =>
                have addedLookup : findClass added name = some candidate := by
                  simpa only [findClass_append, originalLookup] using lookup
                have equal : candidate = declaration := List.mem_singleton.mp (findClass_mem addedLookup)
                subst candidate
                exact ⟨computed.mro, ComputeMro.transport preserved computed.hmro⟩
          sealedLeaf := by
            intro builtin sealed name candidate _ lookup computation present
            cases originalLookup : findClass table name with
            | some original =>
                have equal : original = candidate :=
                  Option.some.inj ((preserved _ _ originalLookup).symm.trans lookup)
                subst candidate
                let originalMro := structural.allMrosExist name original originalLookup
                have same := determinism computation (ComputeMro.transport preserved originalMro.hmro)
                rw [same] at present
                exact structural.sealedLeaf builtin sealed name original originalMro.mro
                  originalLookup originalMro.hmro present
            | none =>
                have addedLookup : findClass added name = some candidate := by
                  simpa only [findClass_append, originalLookup] using lookup
                have equal : candidate = declaration := List.mem_singleton.mp (findClass_mem addedLookup)
                subst candidate
                have same := determinism computation (ComputeMro.transport preserved computed.hmro)
                rw [same] at present
                rcases (prepared.property.2 builtin).mp present with fresh | member
                · obtain ⟨_, builtinLookup⟩ :=
                    known_lookup structural (valid.sealedKnown builtin sealed)
                  rw [fresh, freshName_missing] at builtinLookup
                  cases builtinLookup
                · exact (unsealed builtin sealed member).elim }
      let extension : ValidExtension table := ⟨added, extendedStructural⟩
      let selected : ClassLookupWitness (table ++ extension.added) (freshName table) :=
        ⟨declaration, computed.mro, newLookup, ComputeMro.transport preserved computed.hmro⟩
      refine ⟨⟨extension, ⟨freshName table, selected⟩⟩, ?_⟩
      intro name known
      have notFresh : name ≠ freshName table := by
        obtain ⟨_, lookup⟩ := known_lookup structural known
        intro equal
        rw [equal, freshName_missing] at lookup
        cases lookup
      simpa only [notFresh, false_or] using prepared.property.2 name

/-- No selected class in a structurally valid extension has an MRO containing
all requested class names when their MROs have no common order. -/
theorem ValidExtension.noCommonClass {table : ClassTable}
    (structural : WellFormedClassHierarchy table) (classes : List Identifier)
    (failed : hasValidClassOrder structural.typeContext classes = false)
    (extension : ValidExtension table) (selected : extension.SelectedClass) :
    ¬ ∀ name, name ∈ classes → name ∈ selected.2.mro := by
  intro included
  let conjunction := classIntersectionOfExtension structural extension selected.2
  have compatible : hasValidClassOrder structural.typeContext classes = true :=
    hasValidClassOrder_of_subset conjunction.constraints.orderCompatible fun name known member =>
      (classIntersectionOfExtension_includesClass structural extension selected.2 name).mpr
        ⟨known, included name member⟩
  exact Bool.noConfusion (compatible.symm.trans failed)

end FwPython.Static.Subtyping

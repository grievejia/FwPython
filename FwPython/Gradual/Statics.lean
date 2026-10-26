import FwPython.Gradual.TypeSystem.WellFormedness
import FwPython.Static.TypeSystem.Invariants
import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.MRO.LookupLemmas
import FwPython.Gradual.TypeSystem.Method.Lookup
import FwPython.Static.Subtyping.Core

/-! # Fully static bridge for gradual class tables

Erasing gradual annotations gives a static class table with the same hierarchy.
Static equation subtyping on that table defines the bounds comparisons used by gradual typing.
The module supplies MRO transport, materialization bounds,
and the relations for annotation precision and argument acceptance.

Embedding a static table and then erasing it preserves its class names and
ordered MROs. Equality of these class contexts lets the round-trip proofs
transfer static subtyping to the gradual bounds comparisons. -/

/-- Method lookup through an embedded MRO mirrors static method lookup. -/
theorem findGMethodInMro_embed {ct : ClassTable} {mro : List Identifier}
    {mname : Identifier} {m : Method}
    (h : findMethodInMro ct mro mname = some m) :
    findGMethodInMro (embedClassTable ct) mro mname = some (embedMethod m) := by
  obtain ⟨_, hfind, rfl⟩ :=
    findMemberInHierarchy_transport (ct₂ := embedClassTable ct)
      (getMembers₂ := ClassDecl.methods) (getName₂ := MethodDecl.name)
      (RClass := fun c gc => gc = embedClass c)
      (RMember := fun m gm => gm = embedMethod m)
      (fun hnone => by simp [findGClass_embedClassTable_eq, hnone])
      (fun hsome => ⟨_, findGClass_embedClassTable hsome, rfl⟩)
      (fun hgc hnone => by
        subst hgc
        simpa [findGMethodInList_embedMethods_eq, embedClass] using hnone)
      (fun hgc hsome => by
        subst hgc
        exact ⟨_, by simpa [embedClass] using findGMethodInList_embedMethods hsome, rfl⟩)
      h
  exact hfind

section

/-! ## Lower/upper bound ordering -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

/-- The lower bound of a valid gradual annotation is below its upper bound.
Function inputs reverse the comparison; union and intersection preserve it. -/
theorem lowerBound_le_upperBound (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G : GTy)
    (valid : WellFormedGTy gct G) : IsSubtype structural (lowerBound G) (upperBound G) := by
  induction valid with
  | any => exact .bottom (.object structural)
  | bottom => exact .refl .bottom
  | class_ lookup _ =>
      exact .refl (WellFormedTy.class_of_lookup (findClass_eraseClassTable lookup))
  | negClass lookup _ =>
      exact .refl (WellFormedTy.negClass_of_lookup (findClass_eraseClassTable lookup))
  | callable _ _ input result => exact .callable input result
  | union _ _ left right =>
      exact .unionMono left right
  | intersection _ _ left right =>
      exact .interMono left right

/-! ## Gradual relations from static bounds -/

/-- Test whether static type T lies between the bounds of gradual type G.
This interval approximates filling each `any` occurrence with a static type.
It can include extra types, especially when a function input contains `any`. -/
def MaterializesTo (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G : GTy) (T : Ty) : Prop :=
  IsSubtype structural (lowerBound G) T ∧
  IsSubtype structural T (upperBound G)

/-- The bounds interval of G₁ is contained in that of G₂.
For valid annotations, this comparison is reflexive. It is transitive.
It compares intervals, not the individual fillings of unknown function inputs. -/
def MoreStatic (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G₁ G₂ : GTy) : Prop :=
  IsSubtype structural (lowerBound G₂) (lowerBound G₁) ∧
  IsSubtype structural (upperBound G₁) (upperBound G₂)

/-- A valid annotation has the same bounds interval as itself. -/
theorem moreStatic_refl (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G : GTy)
    (valid : WellFormedGTy gct G) : MoreStatic gct structural G G :=
  ⟨.refl (valid.boundsNamesKnown structural).1, .refl (valid.boundsNamesKnown structural).2⟩

/-- Compare gradual types through their fully static upper bounds.
For fully static annotations, this agrees with `IsSubtype`.
It is reflexive for valid annotations and transitive. -/
def GradualSubtype (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G₁ G₂ : GTy) : Prop :=
  IsSubtype structural (upperBound G₁) (upperBound G₂)

/-- A valid gradual annotation has the same upper bound as itself. -/
theorem gradualSubtype_refl (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G : GTy)
    (valid : WellFormedGTy gct G) : GradualSubtype gct structural G G :=
  .refl (valid.boundsNamesKnown structural).2

theorem gradualSubtype_trans {G₁ G₂ G₃ : GTy}
    (h₁ : GradualSubtype gct structural G₁ G₂) (h₂ : GradualSubtype gct structural G₂ G₃) :
    GradualSubtype gct structural G₁ G₃ :=
  .trans h₁ h₂

theorem gradualSubtype_union_left
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G H : GTy)
    (validG : WellFormedTy (eraseClassTable gct) (upperBound G))
    (validH : WellFormedTy (eraseClassTable gct) (upperBound H)) :
    GradualSubtype gct structural G (.union G H) := by
  simpa [GradualSubtype, upperBound] using IsSubtype.unionLeft (IsSubtype.refl validG) validH

theorem gradualSubtype_union_right
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G H : GTy)
    (validG : WellFormedTy (eraseClassTable gct) (upperBound G))
    (validH : WellFormedTy (eraseClassTable gct) (upperBound H)) :
    GradualSubtype gct structural H (.union G H) := by
  simpa [GradualSubtype, upperBound] using IsSubtype.unionRight (IsSubtype.refl validH) validG

theorem gradualSubtype_union_mono
    (hG : GradualSubtype gct structural G₁ G₂)
    (hH : GradualSubtype gct structural H₁ H₂) :
    GradualSubtype gct structural (.union G₁ H₁) (.union G₂ H₂) := by
  simpa [GradualSubtype, upperBound] using
    IsSubtype.unionMono hG hH

theorem gradualSubtype_intersection_left
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G H : GTy)
    (validG : WellFormedTy (eraseClassTable gct) (upperBound G))
    (validH : WellFormedTy (eraseClassTable gct) (upperBound H)) :
    GradualSubtype gct structural (.intersection G H) G := by
  simpa [GradualSubtype, upperBound] using IsSubtype.interLeft (IsSubtype.refl validG) validH

theorem gradualSubtype_intersection_right
    (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G H : GTy)
    (validG : WellFormedTy (eraseClassTable gct) (upperBound G))
    (validH : WellFormedTy (eraseClassTable gct) (upperBound H)) :
    GradualSubtype gct structural (.intersection G H) H := by
  simpa [GradualSubtype, upperBound] using IsSubtype.interRight (IsSubtype.refl validH) validG

theorem gradualSubtype_intersection_mono
    (hG : GradualSubtype gct structural G₁ G₂)
    (hH : GradualSubtype gct structural H₁ H₂) :
    GradualSubtype gct structural (.intersection G₁ H₁) (.intersection G₂ H₂) := by
  simpa [GradualSubtype, upperBound] using
    IsSubtype.interMono hG hH

/-- Compare lower bounds and compare upper bounds.
This comparison can justify omitting an intersection part at the level of bounds.
It does not account for individual fillings of unknown function inputs. -/
def BoundsSubtype (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (source target : GTy) : Prop :=
  IsSubtype structural (lowerBound source) (lowerBound target) ∧
  IsSubtype structural (upperBound source) (upperBound target)

/-- The lower bound of G₁ is below the upper bound of G₂.
Equivalently, some type in the first bounds interval is below some type in the second.
Assignment and override checks use this approximation.
The relation is reflexive for valid annotations. It is not transitive. -/
def AssignableTo (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct)) (G₁ G₂ : GTy) : Prop :=
  IsSubtype structural (lowerBound G₁) (upperBound G₂)

/-- Every valid annotation is assignable to itself because its lower bound is below its upper bound. -/
theorem assignableTo_refl (gct : GClassTable) (structural : WellFormedClassHierarchy (eraseClassTable gct))
    (G : GTy) (valid : WellFormedGTy gct G) :
    AssignableTo gct structural G G :=
  lowerBound_le_upperBound gct structural G valid

private theorem findClass_eraseEmbedClassTable {ct : ClassTable}
    {cname : Identifier} {c : Class}
    (h : findClass ct cname = some c) :
    findClass (eraseClassTable (embedClassTable ct)) cname =
      some (eraseClass (embedClass c)) :=
  findClass_eraseClassTable (findGClass_embedClassTable h)

private theorem findClass_eraseEmbedClassTable_reverse {ct : ClassTable}
    {cname : Identifier} {c : Class}
    (h : findClass (eraseClassTable (embedClassTable ct)) cname = some c) :
    ∃ c0, findClass ct cname = some c0 ∧ c = eraseClass (embedClass c0) := by
  obtain ⟨gc, hgc, hErase⟩ :=
    findGClass_of_findClass_eraseClassTable (gct := embedClassTable ct) h
  obtain ⟨c0, hfind, hEmbed⟩ := findClass_embedClassTable_reverse hgc
  subst hEmbed
  exact ⟨c0, hfind, hErase.symm⟩

private theorem eraseEmbedClass_resolvedBases (c : Class) :
    (eraseClass (embedClass c)).resolvedBases = c.resolvedBases := by
  rfl

private theorem computeMro_eraseEmbedClassTable_reverse {ct : ClassTable}
    {cname : Identifier} {c : Class} {mro : List Identifier}
    (hfind : findClass ct cname = some c)
    (h : ComputeMro (eraseClassTable (embedClassTable ct))
      (eraseClass (embedClass c)) mro) :
    ComputeMro ct c mro := by
  let key :=
    ComputeMro.rec
      (motive_1 := fun ct' bases parentMros _ =>
        ct' = eraseClassTable (embedClassTable ct) →
          AllParentMros ct bases parentMros)
      (motive_2 := fun ct' c' mro _ =>
        ct' = eraseClassTable (embedClassTable ct) →
          ∀ cname c,
            findClass ct cname = some c →
            c' = eraseClass (embedClass c) →
            ComputeMro ct c mro)
      (fun _ => .nil)
      (fun hfind' _ _ ihMro ihRest hct => by
        subst hct
        obtain ⟨bcls, hfind0, hbcls⟩ := findClass_eraseEmbedClassTable_reverse hfind'
        exact .cons hfind0 (ihMro rfl _ _ hfind0 hbcls) (ihRest rfl))
      (fun hnil hct _ _ _ hc => by
        subst hct
        subst hc
        exact .root (by simpa [eraseEmbedClass_resolvedBases] using hnil))
      (fun hbases hne _ hmerge ihParents hct _ _ _ hc => by
        subst hct
        subst hc
        exact .step (by simpa [eraseEmbedClass_resolvedBases] using hbases) hne
          (ihParents rfl) hmerge)
      h
  exact key rfl _ _ hfind rfl

private theorem computeMro_eraseEmbedClassTable {ct : ClassTable}
    {c : Class} {mro : List Identifier}
    (h : ComputeMro ct c mro) :
    ComputeMro (eraseClassTable (embedClassTable ct))
      (eraseClass (embedClass c)) mro :=
  gComputeMro_eraseClassTable (computeGMro_embedClassTable h)

/-- Recover the selected original declarations and their MROs from structural erased data.

Executable lookup supplies declaration data even when erasure identifies shadowed
method declarations. The selected MRO lists are transported unchanged.
-/
def wellFormedClassHierarchy_eraseEmbed_reverse {ct : ClassTable}
    (erased : WellFormedClassHierarchy (eraseClassTable (embedClassTable ct))) :
    WellFormedClassHierarchy ct := by
  let recover : ∀ name, ClassLookupWitness (eraseClassTable (embedClassTable ct)) name →
      ClassLookupWitness ct name := by
    intro name witness
    cases original : findClass ct name with
    | none =>
        have lookup := witness.hfind
        simp [findClass_eraseClassTable_eq, findGClass_embedClassTable_eq, original] at lookup
    | some declaration =>
        have equal : witness.cls = eraseClass (embedClass declaration) := by
          exact Option.some.inj (witness.hfind.symm.trans (findClass_eraseEmbedClassTable original))
        exact ⟨declaration, witness.mro, original,
          computeMro_eraseEmbedClassTable_reverse original (equal ▸ witness.hmro)⟩
  refine
    { objectExists := ?_
      boolExists := recover boolClass erased.boolExists
      noneExists := recover noneClass erased.noneExists
      boundMethodExists := recover boundMethodClass erased.boundMethodExists
      allMrosExist := fun name declaration lookup =>
        ⟨(erased.allMrosExist name _ (findClass_eraseEmbedClassTable lookup)).mro,
          computeMro_eraseEmbedClassTable_reverse lookup
            (erased.allMrosExist name _ (findClass_eraseEmbedClassTable lookup)).hmro⟩
      sealedLeaf := fun builtin sealed name declaration mro lookup linearization member =>
        erased.sealedLeaf builtin sealed name _ mro (findClass_eraseEmbedClassTable lookup)
          (computeMro_eraseEmbedClassTable linearization) member }
  cases original : findClass ct objectClass with
  | none =>
      have lookup := erased.objectExists.hfind
      simp [findClass_eraseClassTable_eq, findGClass_embedClassTable_eq, original] at lookup
  | some declaration =>
      have equal : erased.objectExists.cls = eraseClass (embedClass declaration) :=
        Option.some.inj (erased.objectExists.hfind.symm.trans (findClass_eraseEmbedClassTable original))
      exact ⟨declaration, original, by simpa [equal] using erased.objectExists.hbases⟩

/-- Reverse structural erasure preserves the complete nominal context, including repeated names. -/
theorem classContextOf_eraseEmbed_reverse {ct : ClassTable}
    (erased : WellFormedClassHierarchy (eraseClassTable (embedClassTable ct))) :
    FwPython.Static.Subtyping.classContextOf ct (wellFormedClassHierarchy_eraseEmbed_reverse erased) =
      FwPython.Static.Subtyping.classContextOf (eraseClassTable (embedClassTable ct)) erased := by
  open FwPython.Static.Subtyping in
    change ClassContext.mk _ _ = ClassContext.mk _ _
    congr 1
    · simp [eraseClassTable, embedClassTable, List.map_map, Function.comp_def]
    · funext name
      change (classContextOf ct (wellFormedClassHierarchy_eraseEmbed_reverse erased)).ancestors name =
        (classContextOf (eraseClassTable (embedClassTable ct)) erased).ancestors name
      by_cases missing : findClass ct name = none
      · have erasedMissing : findClass (eraseClassTable (embedClassTable ct)) name = none := by
          simp [findClass_eraseClassTable_eq, findGClass_embedClassTable_eq, missing]
        rw [context_missing (wellFormedClassHierarchy_eraseEmbed_reverse erased) missing,
          context_missing erased erasedMissing]
      · obtain ⟨declaration, lookup⟩ := Option.ne_none_iff_exists.mp missing
        rw [context_ancestors (wellFormedClassHierarchy_eraseEmbed_reverse erased) lookup.symm,
          context_ancestors erased (findClass_eraseEmbedClassTable lookup.symm)]
        rfl

/-- Subtyping transports through embedding and erasure because the class contexts are equal. -/
theorem staticSubtype_eraseEmbedClassTable {ct : ClassTable}
    {original : WellFormedClassHierarchy ct}
    {erased : WellFormedClassHierarchy (eraseClassTable (embedClassTable ct))}
    {S T : Ty} (included : IsSubtype original S T) : IsSubtype erased S T := by
  simpa only [IsSubtype, WellFormedClassHierarchy.typeContext,
    ← classContextOf_eraseEmbed_reverse erased,
    Subsingleton.elim (wellFormedClassHierarchy_eraseEmbed_reverse erased) original] using included

/-- Static equation subtyping gives assignability of embedded static types. -/
theorem staticSubtype_to_embeddedAssignableTo {ct : ClassTable}
    {original : WellFormedClassHierarchy ct}
    {erased : WellFormedClassHierarchy (eraseClassTable (embedClassTable ct))}
    {S T : Ty} (included : IsSubtype original S T) :
    AssignableTo (embedClassTable ct) erased (embedTy S) (embedTy T) := by
  unfold AssignableTo
  rw [embedTy_lowerBound S, embedTy_upperBound T]
  exact staticSubtype_eraseEmbedClassTable included

/-- Gradual subtyping of embedded static types is exactly static equation subtyping. -/
theorem embedTy_gradualSubtype_iff (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (T₁ T₂ : Ty) :
    GradualSubtype gct structural (embedTy T₁) (embedTy T₂) ↔ IsSubtype structural T₁ T₂ := by
  unfold GradualSubtype
  rw [embedTy_upperBound T₁, embedTy_upperBound T₂]

end

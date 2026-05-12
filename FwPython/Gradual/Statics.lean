import FwPython.Gradual.Embedding
import FwPython.Gradual.Invariants
import FwPython.Static.TypeSystem.Invariants
import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.MRO.LookupLemmas
import FwPython.Gradual.TypeSystem.Method.Lookup
import FwPython.Static.Subtyping.Core

/-! # Fully static bridge for gradual class tables

Bridges `GClassTable` to the fully static semantic-subtyping layer
through `eraseClassTable`. Provides MRO bridge lemmas, leaf-builtin
evidence, and the semantic gradual core (materialization, more static /
more dynamic, assignable to) so that `IsSubtype (eraseClassTable gct)`
can be used for gradual typing. -/

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

/-- Static method-type lookup transports to gradual method-type lookup on the
    embedded class table. -/
theorem FindGMethodType_embed {ct : ClassTable} {cname methodName : Identifier}
    {paramTy returnTy : Ty}
    (h : FindMethodType ct cname methodName paramTy returnTy) :
    FindGMethodType (embedClassTable ct) cname methodName
      (embedTy paramTy) (embedTy returnTy) := by
  obtain ⟨c, mro, m, hfind, hmro, hlookup, hparam, hreturn⟩ := h
  cases hparam
  cases hreturn
  exact ⟨embedClass c, mro, embedMethod m,
    findGClass_embedClassTable hfind,
    computeGMro_embedClassTable hmro,
    findGMethodInMro_embed hlookup,
    rfl,
    rfl⟩

/-! ## Leaf-builtin bridge -/

/-- Helper: the sealing property of a leaf built-in on a gradual class table
    transfers to the erased fully static class table. -/
private theorem leafSealing_of_wellFormed {gct : GClassTable} {B : Identifier}
    (wf : WellFormedGClassTable gct)
    (gleaf : ∀ cname c mro, findGClass gct cname = some c →
      GComputeMro gct c mro → B ∈ mro → cname = B)
    (cname : Identifier) (c : Class) (mro : List Identifier)
    (hfc : findClass (eraseClassTable gct) cname = some c)
    (hmro : ComputeMro (eraseClassTable gct) c mro)
    (hmem : B ∈ mro) : cname = B := by
  obtain ⟨gc, hgc, rfl⟩ := findGClass_of_findClass_eraseClassTable hfc
  let hmro' := (wf.allMrosExist cname gc hgc).hmro
  cases determinism (gComputeMro_eraseClassTable hmro') hmro
  simpa using gleaf cname gc _ hgc hmro' hmem

/-- Bool is a leaf built-in in the erased class table. -/
theorem leafBuiltin_bool_of_wellFormed {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    LeafBuiltin (eraseClassTable gct) boolClass :=
  .bool (leafSealing_of_wellFormed wf wf.boolLeaf)

/-- NoneType is a leaf built-in in the erased class table. -/
theorem leafBuiltin_none_of_wellFormed {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    LeafBuiltin (eraseClassTable gct) noneClass :=
  .none (leafSealing_of_wellFormed wf wf.noneLeaf)

/-- BoundMethod is a leaf built-in in the erased class table. -/
theorem leafBuiltin_boundMethod_of_wellFormed {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    LeafBuiltin (eraseClassTable gct) boundMethodClass :=
  .boundMethod (leafSealing_of_wellFormed wf wf.boundMethodLeaf)

/-! ## Well-formed class-table bridge -/

def eraseClassTable_objectExists {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ObjectExistsWitness (eraseClassTable gct) := by
  exact ⟨
    eraseClass wf.objectExists.cls,
    findClass_eraseClassTable wf.objectExists.hfind,
    by simpa [eraseClass] using wf.objectExists.hbases
  ⟩

private def eraseClassTable_classLookup {gct : GClassTable} (cname : Identifier)
    (hexists : GClassLookupWitness gct cname) :
    ClassLookupWitness (eraseClassTable gct) cname := by
  exact ⟨
    eraseClass hexists.cls,
    hexists.mro,
    findClass_eraseClassTable hexists.hfind,
    gComputeMro_eraseClassTable hexists.hmro
  ⟩

def eraseClassTable_boolExists {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ClassLookupWitness (eraseClassTable gct) boolClass :=
  eraseClassTable_classLookup boolClass wf.boolExists

def eraseClassTable_noneExists {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ClassLookupWitness (eraseClassTable gct) noneClass :=
  eraseClassTable_classLookup noneClass wf.noneExists

def eraseClassTable_boundMethodExists {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ClassLookupWitness (eraseClassTable gct) boundMethodClass :=
  eraseClassTable_classLookup boundMethodClass wf.boundMethodExists

theorem eraseClassTable_builtinsLeaf {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c mro, findClass (eraseClassTable gct) cname = some c →
      ComputeMro (eraseClassTable gct) c mro → boolClass ∈ mro → cname = boolClass :=
  (leafBuiltin_bool_of_wellFormed wf).sealed

theorem eraseClassTable_noneLeaf {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c mro, findClass (eraseClassTable gct) cname = some c →
      ComputeMro (eraseClassTable gct) c mro → noneClass ∈ mro → cname = noneClass :=
  (leafBuiltin_none_of_wellFormed wf).sealed

theorem eraseClassTable_boundMethodLeaf {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c mro, findClass (eraseClassTable gct) cname = some c →
      ComputeMro (eraseClassTable gct) c mro → boundMethodClass ∈ mro → cname = boundMethodClass :=
  (leafBuiltin_boundMethod_of_wellFormed wf).sealed

def eraseClassTable_allMrosExist {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c, findClass (eraseClassTable gct) cname = some c →
      ClassMroWitness (eraseClassTable gct) c := by
  intro cname c hfind
  cases hgc : findGClass gct cname with
  | none =>
      simp [findClass_eraseClassTable_eq, hgc] at hfind
  | some gc =>
      have hErase : eraseClass gc = c := by
        simpa [findClass_eraseClassTable_eq, hgc] using hfind
      subst hErase
      exact ⟨
        (wf.allMrosExist cname gc hgc).mro,
        gComputeMro_eraseClassTable (wf.allMrosExist cname gc hgc).hmro
      ⟩

theorem eraseClassTable_baseClassesDistinct {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c, findClass (eraseClassTable gct) cname = some c → c.baseClasses.Nodup := by
  intro cname c hfind
  obtain ⟨gc, hgc, rfl⟩ := findGClass_of_findClass_eraseClassTable hfind
  simpa [eraseClass] using wf.baseClassesDistinct cname gc hgc

theorem eraseClassTable_allMethodNamesDistinct {gct : GClassTable}
    (hmethodNamesDistinct : ∀ cname c, findGClass gct cname = some c →
      List.Nodup (c.methods.map MethodDecl.name)) :
    ∀ cname c, findClass (eraseClassTable gct) cname = some c →
      List.Nodup (c.methods.map MethodDecl.name) := by
  intro cname c hfind
  obtain ⟨gc, hgc, rfl⟩ := findGClass_of_findClass_eraseClassTable hfind
  simpa [eraseClass, eraseMethod] using hmethodNamesDistinct cname gc hgc

private theorem eraseClass_method_mem_shape {gc : GClass} {m : Method}
    (hmem : m ∈ (eraseClass gc).methods) :
    m.paramTy = Ty.bottom ∧
      m.returnTy = Ty.class_ noneClass ∧
      m.body = .constNone := by
  unfold eraseClass at hmem
  rcases List.mem_map.mp hmem with ⟨gm, _, rfl⟩
  simp [eraseMethod]

theorem eraseClassTable_allMethodSignaturesWellFormed {gct : GClassTable}
    (wf : WellFormedGClassTable gct) :
    ∀ cname c m, findClass (eraseClassTable gct) cname = some c →
      m ∈ c.methods →
      WellFormedTy (eraseClassTable gct) m.paramTy ∧
        WellFormedTy (eraseClassTable gct) m.returnTy := by
  intro cname c m hfind hm
  have hnone := eraseClassTable_noneExists wf
  have hwfNone : WellFormedTy (eraseClassTable gct) (.class_ noneClass) :=
    .class_ hnone.hfind hnone.hmro
  obtain ⟨gc, hgc, rfl⟩ := findGClass_of_findClass_eraseClassTable hfind
  rcases eraseClass_method_mem_shape hm with ⟨hparam, hreturn, _⟩
  constructor
  · simpa [hparam] using (WellFormedTy.bottom (ct := eraseClassTable gct))
  · simpa [hreturn] using hwfNone

theorem eraseClassTable_allMethodsWellTyped (gct : GClassTable) :
    AllMethodsWellTyped (eraseClassTable gct) := by
  intro cname c m hfind hm
  obtain ⟨gc, _, rfl⟩ := findGClass_of_findClass_eraseClassTable hfind
  rcases List.mem_map.mp hm with ⟨gm, _, rfl⟩
  simpa [eraseMethod] using
    (HasType.constNone
      (ct := eraseClassTable gct)
      (Γ := [(gm.param, Ty.bottom), (gm.receiverParam, (.class_ cname : Ty))]))

theorem eraseClassTable_liskovCondition (gct : GClassTable) :
    LiskovCondition (eraseClassTable gct) := by
  intro cname aname c_cls a_cls mro_c mro_a methodName m_c m_a
    hfc hmro_c haname hfa hmro_a hlookup_c hlookup_a
  obtain ⟨dnameC, dC, _, hfinddC, hmInC⟩ := findMethodInMro_provenance hlookup_c
  obtain ⟨dnameA, dA, _, hfinddA, hmInA⟩ := findMethodInMro_provenance hlookup_a
  obtain ⟨gcC, hgcC, rfl⟩ := findGClass_of_findClass_eraseClassTable hfinddC
  obtain ⟨gcA, hgcA, rfl⟩ := findGClass_of_findClass_eraseClassTable hfinddA
  rcases eraseClass_method_mem_shape hmInC with ⟨hparamC, hreturnC, _⟩
  rcases eraseClass_method_mem_shape hmInA with ⟨hparamA, hreturnA, _⟩
  constructor
  · simpa [hparamA, hparamC] using
      (IsSubtype.refl (ct := eraseClassTable gct) (T := (.bottom : Ty)))
  · simpa [hreturnC, hreturnA] using
      (IsSubtype.refl (ct := eraseClassTable gct) (T := (.class_ noneClass : Ty)))

def eraseClassTable_wellFormed {gct : GClassTable}
    (wf : WellFormedGClassTable gct)
    (hmethodNamesDistinct : ∀ cname c, findGClass gct cname = some c →
      List.Nodup (c.methods.map MethodDecl.name)) :
    WellFormedClassTable (eraseClassTable gct) := by
  refine
    { allMethodsWellTyped := eraseClassTable_allMethodsWellTyped gct
      liskovCondition := eraseClassTable_liskovCondition gct
      boolExists := eraseClassTable_boolExists wf
      noneExists := eraseClassTable_noneExists wf
      boundMethodExists := eraseClassTable_boundMethodExists wf
      builtinsLeaf := eraseClassTable_builtinsLeaf wf
      noneLeaf := eraseClassTable_noneLeaf wf
      boundMethodLeaf := eraseClassTable_boundMethodLeaf wf
      allMrosExist := eraseClassTable_allMrosExist wf
      allMethodNamesDistinct := eraseClassTable_allMethodNamesDistinct hmethodNamesDistinct
      allMethodSignaturesWellFormed := eraseClassTable_allMethodSignaturesWellFormed wf
      classNamesUnique := eraseClassTable_classNamesUnique wf.classNamesUnique
      baseClassesDistinct := eraseClassTable_baseClassesDistinct wf
      objectExists := eraseClassTable_objectExists wf }

/-! ## Lower/upper bound ordering -/

/-- The fully static lower bound is always a subtype of the fully static
    upper bound. This is the key semantic invariant: the interval
    `[lowerBound G, upperBound G]` is well-formed for every gradual
    type `G`. -/
theorem lowerBound_le_upperBound (gct : GClassTable) (G : GTy) :
    IsSubtype (eraseClassTable gct) (lowerBound G) (upperBound G) := by
  induction G with
  | any => exact .bottom
  | class_ _ => exact .refl
  | callable _ _ ih_p ih_r => exact .callable ih_p ih_r
  | union _ _ ih_t ih_u =>
    exact .unionElim (.trans ih_t (.unionLeft .refl)) (.trans ih_u (.unionRight .refl))
  | intersection _ _ ih_t ih_u =>
    exact .interIntro (.trans (.interLeft .refl) ih_t) (.trans (.interRight .refl) ih_u)
  | bottom => exact .refl
  | negClass _ => exact .refl

/-! ## Semantic gradual relations -/

/-- A fully static type `T` materializes a gradual type `G` when `T`
    lies in the interval `[lowerBound G, upperBound G]`. -/
def MaterializesTo (gct : GClassTable) (G : GTy) (T : Ty) : Prop :=
  IsSubtype (eraseClassTable gct) (lowerBound G) T ∧
  IsSubtype (eraseClassTable gct) T (upperBound G)

/-- Materialization is exactly the bounds interval. -/
theorem materializes_iff_bounds (gct : GClassTable) (G : GTy) (T : Ty) :
    MaterializesTo gct G T ↔
      IsSubtype (eraseClassTable gct) (lowerBound G) T ∧
      IsSubtype (eraseClassTable gct) T (upperBound G) :=
  Iff.rfl

/-- `G₁` is more static than `G₂` (equivalently, `G₂` is more dynamic
    than `G₁`) when the materialization interval of `G₁` is contained
    in that of `G₂`. Reflexive and transitive. -/
def MoreStatic (gct : GClassTable) (G₁ G₂ : GTy) : Prop :=
  IsSubtype (eraseClassTable gct) (lowerBound G₂) (lowerBound G₁) ∧
  IsSubtype (eraseClassTable gct) (upperBound G₁) (upperBound G₂)

theorem moreStatic_refl (gct : GClassTable) (G : GTy) : MoreStatic gct G G :=
  ⟨.refl, .refl⟩

theorem moreStatic_trans {gct : GClassTable} {G₁ G₂ G₃ : GTy}
    (h₁ : MoreStatic gct G₁ G₂) (h₂ : MoreStatic gct G₂ G₃) :
    MoreStatic gct G₁ G₃ :=
  ⟨.trans h₂.1 h₁.1, .trans h₁.2 h₂.2⟩

/-- Auxiliary conservative subtype-like preorder on gradual types:
    `G₁` is a gradual subtype of `G₂` when the fully static upper bound
    of `G₁` is a subtype of the fully static upper bound of `G₂`. For
    the fully static embedded fragment this coincides with `IsSubtype`.
    Reflexive and transitive. -/
def GradualSubtype (gct : GClassTable) (G₁ G₂ : GTy) : Prop :=
  IsSubtype (eraseClassTable gct) (upperBound G₁) (upperBound G₂)

theorem gradualSubtype_refl (gct : GClassTable) (G : GTy) :
    GradualSubtype gct G G :=
  .refl

theorem gradualSubtype_trans {gct : GClassTable} {G₁ G₂ G₃ : GTy}
    (h₁ : GradualSubtype gct G₁ G₂) (h₂ : GradualSubtype gct G₂ G₃) :
    GradualSubtype gct G₁ G₃ :=
  .trans h₁ h₂

/-- The "assignable to" relation: `G₁` is assignable to `G₂` when some
    materialization of `G₁` is a fully static subtype of some
    materialization of `G₂`. This is the gradual analogue of subtyping
    used at assignment-like boundaries (including override compatibility).
    Reflexive but not transitive. -/
def AssignableTo (gct : GClassTable) (G₁ G₂ : GTy) : Prop :=
  IsSubtype (eraseClassTable gct) (lowerBound G₁) (upperBound G₂)

theorem assignableTo_refl (gct : GClassTable) (G : GTy) :
    AssignableTo gct G G :=
  lowerBound_le_upperBound gct G

/-- Every gradual type is assignable to `any`. -/
theorem assignableTo_any (gct : GClassTable) (G : GTy) :
    AssignableTo gct G .any :=
  .objectTop

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

private theorem leafBuiltin_eraseEmbedClassTable {ct : ClassTable} {B : Identifier}
    (h : LeafBuiltin ct B) :
    LeafBuiltin (eraseClassTable (embedClassTable ct)) B := by
  have liftSeal :
      (∀ cname c mro, findClass ct cname = some c →
          ComputeMro ct c mro → B ∈ mro → cname = B) →
      ∀ cname c mro, findClass (eraseClassTable (embedClassTable ct)) cname = some c →
        ComputeMro (eraseClassTable (embedClassTable ct)) c mro → B ∈ mro → cname = B := by
    intro hseal cname c mro hfind hmro hmem
    obtain ⟨c0, hfind0, hc⟩ := findClass_eraseEmbedClassTable_reverse hfind
    have hmro' :
        ComputeMro (eraseClassTable (embedClassTable ct))
          (eraseClass (embedClass c0)) mro := by
      simpa [hc] using hmro
    exact hseal cname c0 mro hfind0
      (computeMro_eraseEmbedClassTable_reverse hfind0 hmro') hmem
  cases h with
  | bool hseal => exact .bool (liftSeal hseal)
  | none hseal => exact .none (liftSeal hseal)
  | boundMethod hseal => exact .boundMethod (liftSeal hseal)

private theorem staticSubtype_eraseEmbedClassTable {ct : ClassTable}
    {S T : Ty} (h : IsSubtype ct S T) :
    IsSubtype (eraseClassTable (embedClassTable ct)) S T := by
  induction h with
  | refl => exact .refl
  | trans _ _ ihST ihTU => exact .trans ihST ihTU
  | bottom => exact .bottom
  | objectTop => exact .objectTop
  | interLeft _ ih => exact .interLeft ih
  | interRight _ ih => exact .interRight ih
  | interIntro _ _ ihU ihV => exact .interIntro ihU ihV
  | unionElim _ _ ihT ihU => exact .unionElim ihT ihU
  | unionLeft _ ih => exact .unionLeft ih
  | unionRight _ ih => exact .unionRight ih
  | interUnionDistrib => exact .interUnionDistrib
  | class_ hfind hmro hmem =>
      exact .class_ (findClass_eraseEmbedClassTable hfind)
        (computeMro_eraseEmbedClassTable hmro) hmem
  | callable _ _ ihDom ihCod => exact .callable ihDom ihCod
  | callableBoundMethod hfind hmro =>
      exact .callableBoundMethod
        (findClass_eraseEmbedClassTable hfind)
        (computeMro_eraseEmbedClassTable hmro)
  | callableInterUnion => exact .callableInterUnion
  | objectClassUnionNegClass => exact .objectClassUnionNegClass
  | sealedClassNegClass hleaf hfind hmro hnotmem =>
      exact .sealedClassNegClass
        (leafBuiltin_eraseEmbedClassTable hleaf)
        (findClass_eraseEmbedClassTable hfind)
        (computeMro_eraseEmbedClassTable hmro) hnotmem
  | classSelfNegClassBottom => exact .classSelfNegClassBottom

/-- Static subtyping transports to gradual subtyping on the embedded gradual
    class table. -/
theorem staticSubtype_to_embeddedGradualSubtype {ct : ClassTable}
    {S T : Ty} (h : IsSubtype ct S T) :
    GradualSubtype (embedClassTable ct) (embedTy S) (embedTy T) := by
  unfold GradualSubtype
  rw [embedTy_upperBound S, embedTy_upperBound T]
  exact staticSubtype_eraseEmbedClassTable h

/-- Static subtyping transports to gradual assignability on the embedded gradual
    class table. -/
theorem staticSubtype_to_embeddedAssignableTo {ct : ClassTable}
    {S T : Ty} (h : IsSubtype ct S T) :
    AssignableTo (embedClassTable ct) (embedTy S) (embedTy T) := by
  unfold AssignableTo
  rw [embedTy_lowerBound S, embedTy_upperBound T]
  exact staticSubtype_eraseEmbedClassTable h

/-- For the fully static bridge, gradual subtyping coincides exactly
    with fully static subtyping after structural embedding of the
    source-facing static language. -/
theorem embedTy_gradualSubtype_iff (gct : GClassTable) (T₁ T₂ : Ty) :
    GradualSubtype gct (embedTy T₁) (embedTy T₂) ↔
      IsSubtype (eraseClassTable gct) T₁ T₂ := by
  unfold GradualSubtype
  rw [embedTy_upperBound T₁, embedTy_upperBound T₂]

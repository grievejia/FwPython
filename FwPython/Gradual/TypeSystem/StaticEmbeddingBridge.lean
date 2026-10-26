import FwPython.Static.TypeSystem
import FwPython.Gradual.Embedding
import FwPython.Gradual.Statics
import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile

/-! # Static-to-gradual embedding bridge

Proof data connecting static programs to gradual source typing and compilation. -/

/-- A valid static table whose method annotations can be checked at runtime. -/
structure EmbeddableStaticClassTable (ct : ClassTable) : Type where
  /-- Inheritance, declarations, and method bodies satisfy the static rules. -/
  hwf : WellTypedClassHierarchy ct
  /-- Each selected method input and result translates to a permitted runtime check target. -/
  methodSigChecked : ∀ cname c m,
    findClass ct cname = some c →
    m ∈ c.methods →
    CheckedTargetTy (embedClassTable ct) (embedTy m.paramTy) ∧
      CheckedTargetTy (embedClassTable ct) (embedTy m.returnTy)

/-- Name-valid static annotations embed as valid gradual annotations in a hierarchy. -/
theorem wellFormedGTy_embedTy (structural : WellFormedClassHierarchy ct)
    (valid : WellFormedTy ct T) : WellFormedGTy (embedClassTable ct) (embedTy T) := by
  induction valid with
  | bottom => exact .bottom
  | class_ known =>
      let selected := structural.lookupKnown _ known
      exact .class_ (findGClass_embedClassTable selected.hfind)
        (computeGMro_embedClassTable selected.hmro)
  | negClass known =>
      let selected := structural.lookupKnown _ known
      exact .negClass (findGClass_embedClassTable selected.hfind)
        (computeGMro_embedClassTable selected.hmro)
  | union _ _ left right => exact .union left right
  | intersection _ _ left right => exact .intersection left right
  | callable _ _ input result => exact .callable input result

theorem computeMro_embedClassTable_reverse {ct : ClassTable}
    {cname : Identifier} {c : Class} {mro : List Identifier}
    (hfind : findClass ct cname = some c)
    (h : GComputeMro (embedClassTable ct) (embedClass c) mro) :
    ComputeMro ct c mro := by
  let key :=
    ComputeMro.rec
      (motive_1 := fun gct bases parentMros _ =>
        gct = embedClassTable ct →
          AllParentMros ct bases parentMros)
      (motive_2 := fun gct gc mro _ =>
        gct = embedClassTable ct →
          ∀ cname c,
            findClass ct cname = some c →
            gc = embedClass c →
            ComputeMro ct c mro)
      (fun _ => .nil)
      (fun hfind' _ _ ihMro ihRest hgct => by
        subst hgct
        obtain ⟨bcls, hfind0, hbcls⟩ := findClass_embedClassTable_reverse hfind'
        exact .cons hfind0 (ihMro rfl _ _ hfind0 hbcls.symm) (ihRest rfl))
      (fun hnil hgct _ _ _ hcls => by
        subst hgct
        subst hcls
        exact .root (by simpa [embedClass_resolvedBases] using hnil))
      (fun hbases hne _ hmerge ihParents hgct _ _ _ hcls => by
        subst hgct
        subst hcls
        exact .step (by simpa [embedClass_resolvedBases] using hbases) hne
          (ihParents rfl) hmerge)
      h
  exact key rfl _ _ hfind rfl

private theorem findMethodInList_embedMethods_reverse
    {ms : List Method} {mname : Identifier} {gm : GMethod}
    (h : findGMethodInList (ms.map embedMethod) mname = some gm) :
    ∃ m, findMethodInList ms mname = some m ∧ embedMethod m = gm := by
  cases hfind : findMethodInList ms mname with
  | none =>
      simp [findGMethodInList_embedMethods_eq, hfind] at h
  | some m =>
      simp [findGMethodInList_embedMethods_eq, hfind] at h
      cases h
      exact ⟨m, rfl, rfl⟩

theorem findMethodInMro_embed_reverse {ct : ClassTable}
    {mro : List Identifier} {mname : Identifier} {gm : GMethod}
    (h : findGMethodInMro (embedClassTable ct) mro mname = some gm) :
    ∃ m, findMethodInMro ct mro mname = some m ∧ embedMethod m = gm :=
  findMemberInHierarchy_transport (findClass₁ := findGClass) (ct₂ := ct)
    (getMembers₂ := ClassDecl.methods) (getName₂ := MethodDecl.name)
    (RClass := fun gc c => gc = embedClass c)
    (RMember := fun gm m => embedMethod m = gm)
    (fun hnone => by
      cases hfind : findClass ct _ with
      | none => rfl
      | some c => rw [findGClass_embedClassTable hfind] at hnone; cases hnone)
    (fun hsome => by
      obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hsome
      exact ⟨c, hfind, hgc.symm⟩)
    (fun hgc hnone => by
      subst hgc
      simpa [findGMethodInList_embedMethods_eq, embedClass] using hnone)
    (fun hgc hsome => by
      subst hgc
      exact findMethodInList_embedMethods_reverse (by simpa [embedClass] using hsome))
    h

private def wellFormedGClassTable_embedClassTable
    (hemb : EmbeddableStaticClassTable ct) :
    WellFormedGClassTable (embedClassTable ct) where
  objectExists := by
    obtain ⟨c, hfind, hbases⟩ := hemb.hwf.objectExists
    exact ⟨embedClass c, findGClass_embedClassTable hfind, by simpa [embedClass] using hbases⟩
  boolExists :=
    ⟨embedClass hemb.hwf.boolExists.cls,
      hemb.hwf.boolExists.mro,
      findGClass_embedClassTable hemb.hwf.boolExists.hfind,
      computeGMro_embedClassTable hemb.hwf.boolExists.hmro⟩
  noneExists :=
    ⟨embedClass hemb.hwf.noneExists.cls,
      hemb.hwf.noneExists.mro,
      findGClass_embedClassTable hemb.hwf.noneExists.hfind,
      computeGMro_embedClassTable hemb.hwf.noneExists.hmro⟩
  boundMethodExists :=
    ⟨embedClass hemb.hwf.boundMethodExists.cls,
      hemb.hwf.boundMethodExists.mro,
      findGClass_embedClassTable hemb.hwf.boundMethodExists.hfind,
      computeGMro_embedClassTable hemb.hwf.boundMethodExists.hmro⟩
  allMrosExist := by
    intro cname gc hfindG
    cases hfind : findClass ct cname with
    | none =>
        simp [findGClass_embedClassTable_eq, hfind] at hfindG
    | some c =>
        have hgc : embedClass c = gc := by
          simpa [findGClass_embedClassTable_eq, hfind] using hfindG
        subst hgc
        exact ⟨(hemb.hwf.allMrosExist _ _ hfind).mro,
          computeGMro_embedClassTable (hemb.hwf.allMrosExist _ _ hfind).hmro⟩
  classNamesUnique := by
    intro gc₁ gc₂ hmem₁ hmem₂ hname
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.mp hmem₁
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hmem₂
    exact congrArg embedClass (hemb.hwf.classNamesUnique c₁ c₂ hc₁ hc₂ hname)
  baseClassesDistinct := by
    intro cname gc hfindG
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    simpa [embedClass] using hemb.hwf.baseClassesDistinct cname c hfind
  sealedLeaf := by
    intro builtin sealed cname gc mro hfindG hmroG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    exact hemb.hwf.sealedLeaf builtin sealed cname c mro hfind
      (computeMro_embedClassTable_reverse hfind hmroG) hmem

private theorem gradualLiskovCondition_embedClassTable
    (hemb : EmbeddableStaticClassTable ct) :
    GradualLiskovCondition (embedClassTable ct)
      (eraseClassTable_structural (wellFormedGClassTable_embedClassTable hemb)) := by
  intro cname aname c_cls a_cls mro_c mro_a methodName m_c m_a
    hfindC hmroC hmemA hfindA hmroA hlookupC hlookupA
  obtain ⟨c, hfindC', hc⟩ := findClass_embedClassTable_reverse hfindC
  obtain ⟨a, hfindA', ha⟩ := findClass_embedClassTable_reverse hfindA
  subst hc ha
  obtain ⟨mc, hlookupC', hmc⟩ := findMethodInMro_embed_reverse hlookupC
  obtain ⟨ma, hlookupA', hma⟩ := findMethodInMro_embed_reverse hlookupA
  subst hmc hma
  have hmroC' : ComputeMro ct c mro_c :=
    computeMro_embedClassTable_reverse hfindC' hmroC
  have hmroA' : ComputeMro ct a mro_a :=
    computeMro_embedClassTable_reverse hfindA' hmroA
  have hstatic :=
    hemb.hwf.liskovCondition cname aname c a mro_c mro_a methodName mc ma
      hfindC' hmroC' hmemA hfindA' hmroA' hlookupC' hlookupA'
  exact ⟨
    staticSubtype_to_embeddedAssignableTo hstatic.1,
    staticSubtype_to_embeddedAssignableTo hstatic.2
  ⟩

def wellFormedGClassTableCore_embedClassTable
    (hemb : EmbeddableStaticClassTable ct) :
    WellFormedGClassTableCore (embedClassTable ct) where
  raw := wellFormedGClassTable_embedClassTable hemb
  gradualLiskovCondition := gradualLiskovCondition_embedClassTable hemb
  allMethodNamesDistinct := by
    intro cname gc hfindG
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    change List.Nodup ((c.methods.map embedMethod).map MethodDecl.name)
    simpa [List.map_map, embedMethod] using
      hemb.hwf.allMethodNamesDistinct cname c hfind
  allMethodSignaturesWellFormed := by
    intro cname gc gm hfindG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    rcases List.mem_map.mp hmem with ⟨m, hm, rfl⟩
    obtain ⟨hwfP, hwfR⟩ := hemb.hwf.allMethodSignaturesWellFormed cname c m hfind hm
    exact ⟨wellFormedGTy_embedTy hemb.hwf.toWellFormedClassHierarchy hwfP, wellFormedGTy_embedTy hemb.hwf.toWellFormedClassHierarchy hwfR⟩
  allMethodSignaturesCheckedTarget := by
    intro cname gc gm hfindG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    rcases List.mem_map.mp hmem with ⟨m, hm, rfl⟩
    exact hemb.methodSigChecked cname c m hfind hm

/-- Recover the static table's structural data from its embedded gradual table.
All static types in an expression bridge use this same data. -/
def WellFormedGClassTableCore.toOriginalWellFormedClassHierarchy {ct : ClassTable}
    (core : WellFormedGClassTableCore (embedClassTable ct)) : WellFormedClassHierarchy ct :=
  wellFormedClassHierarchy_eraseEmbed_reverse core.toWellFormedClassHierarchy

def embedTyEnv : TyEnv → SBindingEnv
  | [] => []
  | (x, T) :: Γ => { name := x, sourceTy := embedTy T } :: embedTyEnv Γ

theorem embedTyEnv_lookupBinding
    {Γ : TyEnv} {x : Identifier} {T : Ty}
    (h : Γ.lookup x = some T) :
    (embedTyEnv Γ).lookupBinding x = some { name := x, sourceTy := embedTy T } := by
  induction Γ with
  | nil =>
      simp [NamedEnv.lookup] at h
  | cons hd tl ih =>
      by_cases hhd : hd.1 = x
      · subst hhd
        simp [embedTyEnv, SBindingEnv.lookupBinding, NamedEnv.lookup] at h ⊢
        cases h
        rfl
      · have htail : NamedEnv.lookup tl x = some T := by
          simpa [NamedEnv.lookup, hhd] using h
        simpa [embedTyEnv, SBindingEnv.lookupBinding, hhd] using ih htail

theorem embedTyEnv_update
    (Γ : TyEnv) (x : Identifier) (T : Ty) :
    embedTyEnv (Γ.update x T) =
      (embedTyEnv Γ).updateSource x (embedTy T) := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      by_cases hhd : hd.1 = x
      · subst hhd
        simp [TyEnv.update, NamedEnv.update, embedTyEnv, SBindingEnv.updateSource]
      · simpa [TyEnv.update, NamedEnv.update, embedTyEnv, SBindingEnv.updateSource, hhd] using ih

theorem embedTyEnv_update_class
    (Γ : TyEnv) (x : Identifier) (T : Ty) (C : Identifier) :
    embedTyEnv (Γ.update x (.intersection T (.class_ C))) =
      (embedTyEnv Γ).updateSource x
        (.intersection (embedTy T) (.class_ C)) :=
  embedTyEnv_update Γ x (.intersection T (.class_ C))

theorem embedTyEnv_update_negClass
    (Γ : TyEnv) (x : Identifier) (T : Ty) (C : Identifier) :
    embedTyEnv (Γ.update x (.intersection T (.negClass C))) =
      (embedTyEnv Γ).updateSource x
        (.intersection (embedTy T) (.negClass C)) :=
  embedTyEnv_update Γ x (.intersection T (.negClass C))

theorem embedTyEnv_update_isInstanceThen
    (Γ : TyEnv) (x : Identifier) (T : Ty) (C : Identifier) :
    embedTyEnv (Γ.update x (.intersection T (.class_ C))) =
      (embedTyEnv Γ).updateSource x
        (isInstanceThenRefinement (embedTy T) C) := by
  rw [embedTyEnv_update_class, ← isInstanceThenRefinement_embedTy T C]

theorem embedTyEnv_update_isInstanceElse
    (Γ : TyEnv) (x : Identifier) (T : Ty) (C : Identifier) :
    embedTyEnv (Γ.update x (.intersection T (.negClass C))) =
      (embedTyEnv Γ).updateSource x
        (isInstanceElseRefinement (embedTy T) C) := by
  rw [embedTyEnv_update_negClass, ← isInstanceElseRefinement_embedTy T C]

/-- Connect a directly derived static type to its gradual source type.
`EmbeddedExprBridge.output_subtype` separately proves that the directly derived type
is a subtype of the type requested by the caller. -/
inductive CoreViewOnSrc (ct : ClassTable) : Ty → GTy → Type where
  /-- The expression has a static type and unknown gradual source type. -/
  | any :
      CoreViewOnSrc ct T .any
  /-- Translate the static type directly into gradual source syntax. -/
  | embed :
      CoreViewOnSrc ct T (embedTy T)
  /-- Connect the two static union members to the corresponding gradual union members. -/
  | union :
      CoreViewOnSrc ct T G →
      CoreViewOnSrc ct U H →
      CoreViewOnSrc ct (.union T U) (.union G H)
  /-- The expression has both static types and the same gradual source type. -/
  | interIntro :
      CoreViewOnSrc ct T G →
      CoreViewOnSrc ct U G →
      CoreViewOnSrc ct (.intersection T U) G

/-- The method type selected from a receiver type.
The indices state the receiver type, attribute name, and selected method type. -/
inductive AttrSelection (ct : ClassTable) :
    Ty → Identifier → Ty → Type where
  /-- Find the method on the named receiver class. -/
  | class_ :
      FindMethodType ct cname attrName paramTy returnTy →
      AttrSelection ct (.class_ cname) attrName (.callable paramTy returnTy)
  /-- Either receiver class can supply the method; retain both possible method types. -/
  | union :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrSelection ct
        (.union (.class_ c1) (.class_ c2))
        attrName
        (.union (.callable p1 r1) (.callable p2 r2))
  /-- The receiver has both class types; its method satisfies both selected types. -/
  | inter :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrSelection ct
        (.intersection (.class_ c1) (.class_ c2))
        attrName
        (.intersection (.callable p1 r1) (.callable p2 r2))

/-- A selected method type uses valid class names in its input and result. -/
theorem attrSelection_result_wellFormed
    (tableValid : WellTypedClassHierarchy ct)
    (selection : AttrSelection ct receiverTy attributeName resultTy) :
    WellFormedTy ct resultTy := by
  cases selection with
  | class_ method => exact findMethodType_wellFormed tableValid method
  | union left right =>
      exact .union (findMethodType_wellFormed tableValid left)
        (findMethodType_wellFormed tableValid right)
  | inter left right =>
      exact .intersection (findMethodType_wellFormed tableValid left)
        (findMethodType_wellFormed tableValid right)

/-- An input and result requirement justified by a static callee type.
The three type indices are the callee type, input type, and result type. -/
inductive CallSelection {ct : ClassTable} (structural : WellFormedClassHierarchy ct) :
    Ty → Ty → Ty → Type where
  /-- The callee type has no values. Equation subtyping to bottom proves this fact. -/
  | empty :
      IsSubtype structural calleeTy .bottom →
      CallSelection structural calleeTy paramTy .bottom
  /-- Use the input and result types of the function directly. -/
  | callable :
      CallSelection structural (.callable paramTy returnTy) paramTy returnTy
  /-- The actual function can come from either alternative.
  The input must fit both parameter types. The result can have either result type. -/
  | union :
      CallSelection structural calleeTy₁ paramTy₁ returnTy₁ →
      CallSelection structural calleeTy₂ paramTy₂ returnTy₂ →
      CallSelection structural
        (.union calleeTy₁ calleeTy₂)
        (.intersection paramTy₁ paramTy₂)
        (.union returnTy₁ returnTy₂)
  /-- The left alternative has no values. Use the right requirement. -/
  | union_empty_left :
      IsSubtype structural emptyTy .bottom →
      CallSelection structural calleeTy paramTy returnTy →
      CallSelection structural (.union emptyTy calleeTy) paramTy returnTy
  /-- The right alternative has no values. Use the left requirement. -/
  | union_empty_right :
      IsSubtype structural emptyTy .bottom →
      CallSelection structural calleeTy paramTy returnTy →
      CallSelection structural (.union calleeTy emptyTy) paramTy returnTy
  /-- The same function has both types. Use the left input and result requirement. -/
  | inter_left :
      CallSelection structural calleeTy₁ paramTy returnTy →
      CallSelection structural
        (.intersection calleeTy₁ calleeTy₂)
        paramTy
        returnTy
  /-- The same function has both types. Use the right input and result requirement. -/
  | inter_right :
      CallSelection structural calleeTy₂ paramTy returnTy →
      CallSelection structural
        (.intersection calleeTy₁ calleeTy₂)
        paramTy
        returnTy
  /-- Use two requirements of the same function.
  The input must fit both parameter types. The result must have both result types. -/
  | inter_shared :
      CallSelection structural calleeTy paramTy₁ returnTy₁ →
      CallSelection structural calleeTy paramTy₂ returnTy₂ →
      CallSelection structural
        calleeTy
        (.intersection paramTy₁ paramTy₂)
        (.intersection returnTy₁ returnTy₂)
  /-- The same function satisfies both requirements.
  Permit inputs of either parameter type and results of either result type. -/
  | inter_correlated :
      CallSelection structural calleeTy₁ paramTy₁ returnTy₁ →
      CallSelection structural calleeTy₂ paramTy₂ returnTy₂ →
      CallSelection structural
        (.intersection calleeTy₁ calleeTy₂)
        (.union paramTy₁ paramTy₂)
        (.union returnTy₁ returnTy₂)

/-- A selection from valid callee and input types implies its stated function requirement. -/
theorem callSelection_subtype_callable {structural : WellFormedClassHierarchy ct}
    (selection : CallSelection structural calleeTy paramTy returnTy)
    (calleeValid : WellFormedTy ct calleeTy) (inputValid : WellFormedTy ct paramTy) :
    IsSubtype structural calleeTy (.callable paramTy returnTy) := by
  induction selection with
  | empty empty => exact .trans empty (.bottom (.callable inputValid .bottom))
  | callable => exact .refl calleeValid
  | union _ _ ihLeft ihRight =>
      have left := ihLeft calleeValid.union_left inputValid.intersection_left
      have right := ihRight calleeValid.union_right inputValid.intersection_right
      exact .unionElim
        (.trans left (.callable (.interLeft (.refl inputValid.intersection_left) inputValid.intersection_right)
          (.unionLeft (.refl left.targetWellFormed.callable_return) right.targetWellFormed.callable_return)))
        (.trans right (.callable (.interRight (.refl inputValid.intersection_right) inputValid.intersection_left)
          (.unionRight (.refl right.targetWellFormed.callable_return) left.targetWellFormed.callable_return)))
  | union_empty_left empty _ ih =>
      have selected := ih calleeValid.union_right inputValid
      exact .unionElim (.trans empty (.bottom selected.targetWellFormed)) selected
  | union_empty_right empty _ ih =>
      have selected := ih calleeValid.union_left inputValid
      exact .unionElim selected (.trans empty (.bottom selected.targetWellFormed))
  | inter_left _ ih =>
      exact .interLeft (ih calleeValid.intersection_left inputValid) calleeValid.intersection_right
  | inter_right _ ih =>
      exact .interRight (ih calleeValid.intersection_right inputValid) calleeValid.intersection_left
  | inter_shared _ _ ihLeft ihRight =>
      have left := ihLeft calleeValid inputValid.intersection_left
      have right := ihRight calleeValid inputValid.intersection_right
      exact .callableMeet left right
  | inter_correlated _ _ ihLeft ihRight =>
      have left := ihLeft calleeValid.intersection_left inputValid.union_left
      have right := ihRight calleeValid.intersection_right inputValid.union_right
      exact .trans
        (.interMono left right)
        (.callableCorrelatedSummary inputValid.union_left inputValid.union_right
          left.targetWellFormed.callable_return right.targetWellFormed.callable_return)

/-- Proof data connecting a static expression to its gradual source typing.
The first static type is proved directly for the expression.
The final static type can be a less specific type requested by the caller. -/
inductive EmbeddedExprBridgeCore
    (ct : ClassTable)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct)) :
    (Γ : TyEnv) → (e : Expr) → (producerTy : Ty) → (srcTy : GTy) →
      GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy →
      (advertisedTy : Ty) → Type where
  /-- The variable has the type assigned by its static environment. -/
  | var
      -- The variable lookup gives its directly derived static type.
      (lookup : Γ.lookup x = some producerTy)
      -- The variable type is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy producerTy advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ (.var x) producerTy (embedTy producerTy)
        (GSrcInfer.var (embedTyEnv_lookupBinding lookup)) advertisedTy
  /-- Translate None with its static and source types. -/
  | constNone
      -- NoneType is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.class_ noneClass) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ .constNone (.class_ noneClass)
        (.class_ noneClass) GSrcInfer.constNone advertisedTy
  /-- Translate True with its static and source types. -/
  | constTrue
      -- Bool is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.class_ boolClass) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ .constTrue (.class_ boolClass)
        (.class_ boolClass) GSrcInfer.constTrue advertisedTy
  /-- Translate False with its static and source types. -/
  | constFalse
      -- Bool is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.class_ boolClass) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ .constFalse (.class_ boolClass)
        (.class_ boolClass) GSrcInfer.constFalse advertisedTy
  /-- Translate allocation of an ordinary user class. -/
  | new
      -- Static lookup for the allocated class.
      (class_lookup : findClass ct cname = some c)
      -- Source lookup for the embedded allocated class.
      (source_lookup : findGClass (embedClassTable ct) cname = some sourceClass)
      -- The allocated class is not the builtin `Bool` class.
      (notBool : cname ≠ boolClass)
      -- The allocated class is not the builtin `None` class.
      (notNone : cname ≠ noneClass)
      -- The allocated class is not the runtime bound-method class.
      (notBoundMethod : cname ≠ boundMethodClass)
      -- The allocated class type is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.class_ cname) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ (.new cname) (.class_ cname)
        (embedTy (.class_ cname))
        (GSrcInfer.new source_lookup notBool notNone notBoundMethod)
        advertisedTy
  /-- Translation proof for attribute access.
  Compute the source result from the receiver's gradual type.
  Keep both the directly derived static result and the result requested by the caller. -/
  | attrAccess
      -- Source inference for the receiver expression.
      (receiverHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr base) receiverSrc)
      -- Proofs connecting the receiver's static and source types.
      (receiver :
        EmbeddedExprBridgeCore ct hwfct Γ base receiverProducer receiverSrc
          receiverHsrc receiverAdvertised)
      -- The attribute type selected from the directly derived receiver type.
      (producerSelection :
        AttrSelection ct receiverProducer attrName producerResult)
      -- The source attribute check gives this result type.
      (attr_source_eq :
        attrSourceTy? (embedClassTable ct) receiverSrc attrName =
          some producerSrcResult)
      -- The relation between the directly derived static and source result types.
      (result_view : CoreViewOnSrc ct producerResult producerSrcResult)
      -- The directly derived result is a subtype of the requested result.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy producerResult advertisedResult) :
      EmbeddedExprBridgeCore ct hwfct Γ (.attrAccess base attrName)
        producerResult producerSrcResult
        (GSrcInfer.attrAccess receiverHsrc attr_source_eq)
        advertisedResult
  /-- Translation proof for a call.
  Compute its source result from the function and argument source types. -/
  | call
      -- The function expression has this gradual source type.
      (calleeHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr callee) calleeSrc)
      -- Proofs connecting the function's static and source types.
      (calleeBridge :
        EmbeddedExprBridgeCore ct hwfct Γ callee calleeProducer calleeSrc
          calleeHsrc calleeAdvertised)
      -- The argument expression has this gradual source type.
      (argumentHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr arg) argumentSrc)
      -- Proofs connecting the argument's static and source types.
      (argumentBridge :
        EmbeddedExprBridgeCore ct hwfct Γ arg argumentProducer argumentSrc
          argumentHsrc argumentAdvertised)
      -- The input and result types selected from the directly derived function type.
      (producerSelection :
        CallSelection hwfct.toOriginalWellFormedClassHierarchy calleeProducer producerParam producerReturn)
      -- The directly derived argument type is a subtype of the selected parameter type.
      (argument_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy argumentProducer producerParam)
      -- The source call check gives this result type.
      (call_source_eq :
        callSourceTy? (embedClassTable ct) calleeSrc argumentSrc hwfct
          = some callSrcResult)
      -- The relation between the directly derived static and source result types.
      (return_view : CoreViewOnSrc ct producerReturn callSrcResult)
      -- The directly derived result is a subtype of the requested result.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy producerReturn advertisedReturn) :
      EmbeddedExprBridgeCore ct hwfct Γ (.call callee arg)
        producerReturn callSrcResult
        (GSrcInfer.call calleeHsrc argumentHsrc call_source_eq)
        advertisedReturn
  /-- Translation proof for an ordinary conditional.
  Its static and source result types are the corresponding unions of the branch types. -/
  | cond
      -- The condition expression is not an `isInstance` test.
      (test_not_isInstance : (embedExpr condition).notIsInstance)
      -- Source inference for the condition expression.
      (conditionHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr condition) conditionSrc)
      -- Bridge for the condition expression.
      (conditionBridge :
        EmbeddedExprBridgeCore ct hwfct Γ condition conditionProducer conditionSrc
          conditionHsrc conditionAdvertised)
      -- The directly derived condition type is a subtype of Bool.
      (condition_bool_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy conditionProducer (.class_ boolClass))
      -- Source compatibility of the condition source type with `Bool`.
      (test_assignable :
        AssignableTo (embedClassTable ct) hwfct.toWellFormedClassHierarchy conditionSrc (.class_ boolClass))
      -- Source inference for the `then` branch.
      (thenHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr thenBranch) thenSrc)
      -- Bridge for the `then` branch.
      (thenBridge :
        EmbeddedExprBridgeCore ct hwfct Γ thenBranch thenProducer thenSrc
          thenHsrc thenAdvertised)
      -- Source inference for the `else` branch.
      (elseHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr elseBranch) elseSrc)
      -- Bridge for the `else` branch.
      (elseBridge :
        EmbeddedExprBridgeCore ct hwfct Γ elseBranch elseProducer elseSrc
          elseHsrc elseAdvertised)
      -- The union of the directly derived branch types is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.union thenProducer elseProducer) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ (.cond condition thenBranch elseBranch)
        (.union thenProducer elseProducer) (.union thenSrc elseSrc)
        (GSrcInfer.cond test_not_isInstance conditionHsrc test_assignable
          thenHsrc elseHsrc)
        advertisedTy
  /-- Translate a class membership test with a Bool result. -/
  | isInstance
      -- Static lookup for the tested variable.
      (lookup : Γ.lookup x = some variableTy)
      -- Static lookup for the tested class.
      (class_lookup : findClass ct C = some c)
      -- Source lookup for the embedded tested class.
      (source_class_lookup : findGClass (embedClassTable ct) C = some sourceClass)
      -- Bool is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.class_ boolClass) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ (.isInstance x C) (.class_ boolClass)
        (.class_ boolClass)
        (GSrcInfer.isInstance (embedTyEnv_lookupBinding lookup) source_class_lookup)
        advertisedTy
  /-- Conditional `isInstance` bridge with source and static refinements. -/
  | condIsInstance
      -- Static lookup for the refined variable.
      (lookup : Γ.lookup x = some variableTy)
      -- Static lookup for the refined class.
      (class_lookup : findClass ct C = some c)
      -- Source lookup for the embedded refined class.
      (source_class_lookup : findGClass (embedClassTable ct) C = some sourceClass)
      -- The positive branch has this source type after adding class membership information.
      (thenHsrc :
        GSrcInfer (embedClassTable ct) hwfct
          (embedTyEnv (Γ.update x (.intersection variableTy (.class_ C))))
          (embedExpr thenBranch) thenSrc)
      -- Bridge for the positive branch under the refined static environment.
      (thenBridge :
        EmbeddedExprBridgeCore ct hwfct
          (Γ.update x (.intersection variableTy (.class_ C)))
          thenBranch thenProducer thenSrc thenHsrc thenAdvertised)
      -- Source inference for the negative branch under the refined source environment.
      (elseHsrc :
        GSrcInfer (embedClassTable ct) hwfct
          (embedTyEnv (Γ.update x (.intersection variableTy (.negClass C))))
          (embedExpr elseBranch) elseSrc)
      -- Bridge for the negative branch under the refined static environment.
      (elseBridge :
        EmbeddedExprBridgeCore ct hwfct
          (Γ.update x (.intersection variableTy (.negClass C)))
          elseBranch elseProducer elseSrc elseHsrc elseAdvertised)
      -- The union of the directly derived branch types is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.union thenProducer elseProducer) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ
        (.cond (.isInstance x C) thenBranch elseBranch)
        (.union thenProducer elseProducer) (.union thenSrc elseSrc)
        (GSrcInfer.condIsInstance
          (embedTyEnv_lookupBinding lookup)
          source_class_lookup
          (cast (by
            rw [embedTyEnv_update_isInstanceThen
              (Γ := Γ) (x := x) (T := variableTy) (C := C)])
            thenHsrc)
          (cast (by
            rw [embedTyEnv_update_isInstanceElse
              (Γ := Γ) (x := x) (T := variableTy) (C := C)])
            elseHsrc))
        advertisedTy
  /-- Intersection introduction bridge for one checked source expression. -/
  | interIntro
      -- The source typing proof chosen for this expression.
      (leftHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr e) sharedSrc)
      -- Proofs connecting the left static type to the source type.
      (left :
        EmbeddedExprBridgeCore ct hwfct Γ e leftProducer sharedSrc
          leftHsrc leftAdvertised)
      -- The second typing proof gives the same source type.
      (rightHsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr e) sharedSrc)
      -- Proofs connecting the right static type to the same source type.
      (right :
        EmbeddedExprBridgeCore ct hwfct Γ e rightProducer sharedSrc
          rightHsrc rightAdvertised)
      -- The intersection of the directly derived types is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy (.intersection leftProducer rightProducer) advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ e
        (.intersection leftProducer rightProducer) sharedSrc leftHsrc advertisedTy
  /-- Prove that the directly derived static type is a subtype of the requested type.
  Keep the same source expression and source typing proof. -/
  | sub
      -- Source inference inherited from the inner bridge.
      (hsrc :
        GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ)
          (embedExpr e) srcTy)
      -- The inner translation proof supplies the same directly derived static and source types.
      (inner :
        EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc innerAdvertised)
      -- The directly derived static type is a subtype of the requested type.
      (output_subtype : IsSubtype hwfct.toOriginalWellFormedClassHierarchy producerTy advertisedTy) :
      EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy

/-- A static expression type, its gradual source type, and the proofs that connect them. -/
structure EmbeddedExprBridge
    (ct : ClassTable)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct))
    (Γ : TyEnv) (e : Expr) (advertisedTy : Ty) : Type where
  /-- The static type proved directly for the expression. -/
  producerTy : Ty
  /-- The type computed for the expression in gradual source syntax. -/
  srcTy : GTy
  /-- The source typing proof supplied to `compileCheck`. -/
  hsrc :
    GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy
  /-- Proofs connecting the static type, source type, and type requested by the caller. -/
  core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy

namespace EmbeddedExprBridgeCore

/-- The directly derived static type is a subtype of the requested type. -/
def output_subtype
    {ct : ClassTable}
    {hwfct : WellFormedGClassTableCore (embedClassTable ct)}
    {Γ : TyEnv} {e : Expr} {producerTy : Ty} {srcTy : GTy}
    {hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy}
    {advertisedTy : Ty}
    (core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy) :
    IsSubtype hwfct.toOriginalWellFormedClassHierarchy producerTy advertisedTy :=
  match core with
  | .var _ output_subtype .. => output_subtype
  | .constNone output_subtype .. => output_subtype
  | .constTrue output_subtype .. => output_subtype
  | .constFalse output_subtype .. => output_subtype
  | .new _ _ _ _ _ output_subtype .. => output_subtype
  | .attrAccess _ _ _ _ _ output_subtype .. => output_subtype
  | .call _ _ _ _ _ _ _ _ output_subtype .. => output_subtype
  | .cond _ _ _ _ _ _ _ _ _ output_subtype .. => output_subtype
  | .isInstance _ _ _ output_subtype .. => output_subtype
  | .condIsInstance _ _ _ _ _ _ _ output_subtype .. => output_subtype
  | .interIntro _ _ _ _ output_subtype .. => output_subtype
  | .sub _ _ output_subtype .. => output_subtype

/-- The expression's directly derived static type uses valid class names. -/
def producer_wellFormed
    {ct : ClassTable}
    {hwfct : WellFormedGClassTableCore (embedClassTable ct)}
    {Γ : TyEnv} {e : Expr} {producerTy : Ty} {srcTy : GTy}
    {hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy}
    {advertisedTy : Ty}
    (core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy) :
    WellFormedTy ct producerTy :=
  (output_subtype core).sourceWellFormed

/-- Derive the static typing proof for the expression's directly derived type. -/
def typing
    {ct : ClassTable}
    {hwfct : WellFormedGClassTableCore (embedClassTable ct)}
    {Γ : TyEnv} {e : Expr} {producerTy : Ty} {srcTy : GTy}
    {hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy}
    {advertisedTy : Ty}
    (core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy) :
    HasType hwfct.toOriginalWellFormedClassHierarchy Γ e producerTy :=
  match core with
  | .var lookup .. => .var lookup
  | .constNone .. => .constNone
  | .constTrue .. => .constTrue
  | .constFalse .. => .constFalse
  | .new class_lookup _ notBool notNone notBoundMethod .. =>
      .new class_lookup notBool notNone notBoundMethod
  | .attrAccess _ receiver selection .. => by
      cases selection with
      | class_ method => exact .attrAccess (typing receiver) method
      | union first second => exact .attrAccessUnion (typing receiver) first second
      | inter first second =>
          obtain ⟨_, _, _, firstLookup, firstMro, firstMethod⟩ := first
          obtain ⟨_, _, _, secondLookup, secondMro, secondMethod⟩ := second
          exact HasType.attrAccessInter
            ((typing receiver).sub (.interLeft (.refl (WellFormedTy.class_of_lookup firstLookup))
              (WellFormedTy.class_of_lookup secondLookup)))
            ((typing receiver).sub (.interRight (.refl (WellFormedTy.class_of_lookup secondLookup))
              (WellFormedTy.class_of_lookup firstLookup)))
            ⟨_, _, _, firstLookup, firstMro, firstMethod⟩
            ⟨_, _, _, secondLookup, secondMro, secondMethod⟩
  | .call _ calleeBridge _ argumentBridge selection argument_subtype .. =>
      .call ((typing calleeBridge).sub (callSelection_subtype_callable selection
        (producer_wellFormed calleeBridge) argument_subtype.targetWellFormed))
        (typing argumentBridge) argument_subtype
  | .cond _ _ conditionBridge condition_bool_subtype _ _ thenBridge _ elseBridge .. =>
      .cond (typing conditionBridge) condition_bool_subtype
        (typing thenBridge) (typing elseBridge)
  | .isInstance lookup class_lookup .. => .isInstance lookup class_lookup
  | .condIsInstance lookup class_lookup _ _ thenBridge _ elseBridge .. =>
      .condIsInstance lookup class_lookup (typing thenBridge) (typing elseBridge)
  | .interIntro _ left _ right .. =>
      .interIntro (typing left) (typing right)
  | .sub _ inner .. =>
      typing inner

/-- Connect the directly derived static type to the source type. -/
def view
    {ct : ClassTable}
    {hwfct : WellFormedGClassTableCore (embedClassTable ct)}
    {Γ : TyEnv} {e : Expr} {producerTy : Ty} {srcTy : GTy}
    {hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy}
    {advertisedTy : Ty}
    (core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy) :
    CoreViewOnSrc ct producerTy srcTy :=
  match core with
  | .var .. => .embed
  | .constNone .. => .embed
  | .constTrue .. => .embed
  | .constFalse .. => .embed
  | .new .. => .embed
  | .attrAccess _ _ _ _ result_view .. => result_view
  | .call _ _ _ _ _ _ _ return_view .. => return_view
  | .cond _ _ _ _ _ _ thenBridge _ elseBridge .. =>
      .union (view thenBridge) (view elseBridge)
  | .isInstance .. => .embed
  | .condIsInstance _ _ _ _ thenBridge _ elseBridge .. =>
      .union (view thenBridge) (view elseBridge)
  | .interIntro _ left _ right .. =>
      .interIntro (view left) (view right)
  | .sub _ inner .. => view inner

/-- The requested static type uses valid class names. -/
def output_wellFormed
    {ct : ClassTable}
    {hwfct : WellFormedGClassTableCore (embedClassTable ct)}
    {Γ : TyEnv} {e : Expr} {producerTy : Ty} {srcTy : GTy}
    {hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy}
    {advertisedTy : Ty}
    (core : EmbeddedExprBridgeCore ct hwfct Γ e producerTy srcTy hsrc advertisedTy) :
    WellFormedTy ct advertisedTy :=
  (output_subtype core).targetWellFormed

end EmbeddedExprBridgeCore

namespace EmbeddedExprBridge

/-- Derive the static typing proof for the expression's directly derived type. -/
def typing
    (bridge : EmbeddedExprBridge ct hwfct Γ e T) :
    HasType hwfct.toOriginalWellFormedClassHierarchy Γ e bridge.producerTy :=
  bridge.core.typing

/-- The expression's directly derived static type uses valid class names. -/
def producer_wellFormed
    (bridge : EmbeddedExprBridge ct hwfct Γ e T) :
    WellFormedTy ct bridge.producerTy :=
  bridge.core.producer_wellFormed

/-- Connect the directly derived static type to the source type. -/
def view
    (bridge : EmbeddedExprBridge ct hwfct Γ e T) :
    CoreViewOnSrc ct bridge.producerTy bridge.srcTy :=
  bridge.core.view

/-- The directly derived static type is a subtype of the requested type. -/
def output_subtype
    (bridge : EmbeddedExprBridge ct hwfct Γ e T) :
    IsSubtype hwfct.toOriginalWellFormedClassHierarchy bridge.producerTy T :=
  bridge.core.output_subtype

/-- The requested static type uses valid class names. -/
def output_wellFormed
    (bridge : EmbeddedExprBridge ct hwfct Γ e T) :
    WellFormedTy ct T :=
  bridge.core.output_wellFormed

end EmbeddedExprBridge

/-- A static program together with the explicit gradual source bridges consumed
by the checked compiler. -/
structure BridgeableStaticProgram (p : Program) : Type where
  /-- The static class table and its permitted method boundary types. -/
  classTable : EmbeddableStaticClassTable p.classes
  /-- The static result type requested for the main expression. -/
  mainTy : Ty
  /-- The typing and inheritance data for the translated class table. -/
  core : WellFormedGClassTableCore (embedClassTable p.classes)
  /-- The embedded gradual source bridge for the program main expression. -/
  mainBridge : EmbeddedExprBridge p.classes core [] p.main mainTy
  /-- Embedded gradual source bridges for method bodies. -/
  methodBodiesBridge : ∀ cname c m,
    findClass p.classes cname = some c →
    m ∈ c.methods →
    EmbeddedExprBridge p.classes core
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy

/-- Compile one embedded static method into the checked method record. The
source inference determines the checked body; the method signature determines
the checked parameter and return obligations. -/
def compileEmbeddedMethod
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (cname : Identifier)
    (m : Method)
    {srcTy : GTy}
    (hsrc : GSrcInfer
      (embedClassTable p.classes)
      core
      (embedTyEnv [(m.param, m.paramTy), (m.receiverParam, .class_ cname)])
      (embedExpr m.body)
      srcTy) :
    CheckedMethod where
  name := m.name
  receiverParam := m.receiverParam
  param := m.param
  paramTy := checkedTargetOfGTy (embedTy m.paramTy)
  returnTy := checkedTargetOfGTy (embedTy m.returnTy)
  parameterObligation :=
    .hasType (.methodParameter cname m.name) (embedTy m.paramTy)
  returnObligation :=
    .hasType (.methodReturn cname m.name) (embedTy m.returnTy)
  body :=
    compileCheck
      hsrc
      [(m.param, embedTy m.paramTy),
       (m.receiverParam, .class_ cname)]
      .any
      (.methodBody cname m.name [])

/-- The checked method emitted by `compileEmbeddedMethod` satisfies the checked
class-table compiler relation for the corresponding embedded source method. -/
def compileEmbeddedMethod_compiled
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (hfind : findClass p.classes cname = some c)
    (hm : m ∈ c.methods) :
    Checked.IsCompiledMethodAt
      (embedClassTable p.classes)
      core
      cname
      (embedMethod m)
      (compileEmbeddedMethod p core cname m
        (methodBodiesBridge cname c m hfind hm).hsrc) where
  name_eq := rfl
  receiverParam_eq := rfl
  param_eq := rfl
  paramTy_eq := by simp [compileEmbeddedMethod, embedMethod]
  returnTy_eq := by simp [compileEmbeddedMethod, embedMethod]
  parameterObligation_eq := rfl
  returnObligation_eq := rfl
  body_srcTy := (methodBodiesBridge cname c m hfind hm).srcTy
  body_hsrc := (methodBodiesBridge cname c m hfind hm).hsrc
  body_eq := by
    simp [compileEmbeddedMethod, embedMethod]
    rfl

/-- Compile a list of source methods from one embedded static class. The
membership argument supplies each method's bridge from the enclosing class. -/
def compileEmbeddedMethods
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (c : Class)
    (hfind : findClass p.classes c.name = some c) :
    (ms : List Method) →
    (∀ {m : Method}, m ∈ ms → m ∈ c.methods) →
    List CheckedMethod
  | [], _ => []
  | m :: ms, hmems =>
      compileEmbeddedMethod p core c.name m
        (methodBodiesBridge c.name c m hfind (hmems (.head _))).hsrc ::
      compileEmbeddedMethods p core methodBodiesBridge c hfind ms
        (fun hm => hmems (.tail _ hm))

/-- The list produced by `compileEmbeddedMethods` is pointwise related to the
embedded source methods by checked method compilation. -/
def compileEmbeddedMethods_compiled
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (c : Class)
    (hfind : findClass p.classes c.name = some c) :
    ∀ (ms : List Method)
      (hmems : ∀ {m : Method}, m ∈ ms → m ∈ c.methods),
      Forall2Data
        (Checked.IsCompiledMethodAt (embedClassTable p.classes) core c.name)
        (ms.map embedMethod)
        (compileEmbeddedMethods p core methodBodiesBridge c hfind ms hmems)
  | [], _ => .nil
  | m :: ms, hmems =>
      .cons
        (compileEmbeddedMethod_compiled
          (p := p)
          (core := core)
          (methodBodiesBridge := methodBodiesBridge)
          (cname := c.name)
          (c := c)
          (m := m)
          hfind
          (hmems (.head _)))
        (compileEmbeddedMethods_compiled p core methodBodiesBridge c hfind ms
          (fun hm => hmems (.tail _ hm)))

/-- Compile one embedded static class by preserving its hierarchy fields and
compiling each method body through the supplied source bridge. -/
def compileEmbeddedClass
    (p : Program)
    (staticClassTable : EmbeddableStaticClassTable p.classes)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (c : Class)
    (hmem : c ∈ p.classes) :
    CheckedClass where
  name := c.name
  baseClasses := c.baseClasses
  methods :=
    compileEmbeddedMethods
      p
      core
      methodBodiesBridge
      c
      (findClass_of_mem staticClassTable.hwf.classNamesUnique hmem)
      c.methods
      (fun hm => hm)

/-- The class produced by `compileEmbeddedClass` satisfies the checked
class-table compiler relation for the embedded source class. -/
def compileEmbeddedClass_compiled
    (p : Program)
    (staticClassTable : EmbeddableStaticClassTable p.classes)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (c : Class)
    (hmem : c ∈ p.classes) :
    Checked.IsCompiledClass
      (embedClassTable p.classes)
      core
      (embedClass c)
      (compileEmbeddedClass p staticClassTable core methodBodiesBridge c hmem) where
  name_eq := rfl
  baseClasses_eq := rfl
  methods_compiled := by
    simpa [compileEmbeddedClass] using
      compileEmbeddedMethods_compiled
        (p := p)
        (core := core)
        (methodBodiesBridge := methodBodiesBridge)
        c
        (findClass_of_mem staticClassTable.hwf.classNamesUnique hmem)
        c.methods
        (fun hm => hm)

/-- Compile a class table by compiling each embedded static class in order. -/
def compileEmbeddedClasses
    (p : Program)
    (staticClassTable : EmbeddableStaticClassTable p.classes)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy) :
    (cs : List Class) →
    (∀ {c : Class}, c ∈ cs → c ∈ p.classes) →
    CheckedClassTable
  | [], _ => []
  | c :: cs, hmems =>
      compileEmbeddedClass p staticClassTable core methodBodiesBridge c (hmems (.head _)) ::
      compileEmbeddedClasses p staticClassTable core methodBodiesBridge cs
        (fun hc => hmems (.tail _ hc))

/-- The class table produced by `compileEmbeddedClasses` is pointwise related
to the embedded source class table by checked class compilation. -/
def compileEmbeddedClasses_compiled
    (p : Program)
    (staticClassTable : EmbeddableStaticClassTable p.classes)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy) :
    ∀ (cs : List Class)
      (hmems : ∀ {c : Class}, c ∈ cs → c ∈ p.classes),
      Forall2Data
        (Checked.IsCompiledClass (embedClassTable p.classes) core)
        (cs.map embedClass)
        (compileEmbeddedClasses p staticClassTable core methodBodiesBridge cs hmems)
  | [], _ => .nil
  | c :: cs, hmems =>
      .cons
        (compileEmbeddedClass_compiled
          (p := p)
          (staticClassTable := staticClassTable)
          (core := core)
          (methodBodiesBridge := methodBodiesBridge)
          c
          (hmems (.head _)))
        (compileEmbeddedClasses_compiled p staticClassTable core methodBodiesBridge cs
          (fun hc => hmems (.tail _ hc)))

/-- Compile an embedded static program into a checked program. Classes use the
method bridges in the elaboration package, and the main expression is compiled
at the approximation of its inferred embedded source type. -/
def compileEmbeddedProgram
    (hprog : BridgeableStaticProgram p) :
    CheckedProgram where
  classes :=
    compileEmbeddedClasses
      p
      hprog.classTable
      hprog.core
      hprog.methodBodiesBridge
      p.classes
      (fun hc => hc)
  main :=
    compileCheck
      hprog.mainBridge.hsrc
      []
      (approxTarget hprog.mainBridge.srcTy)
      (.main [])

/-- Source-side defining-class data for one successful MRO method lookup. -/
structure SourceMethodLookupData
    (ct : ClassTable)
    (recvMro : List Identifier)
    (attrName : Identifier)
    (sourceMethod : Method)
    (definingClassName : Identifier) : Type where
  /-- The defining class is an entry in the runtime receiver MRO. -/
  definingClass_mem : definingClassName ∈ recvMro
  /-- The source class that contributes the method. -/
  sourceClass : Class
  /-- Source class lookup for the defining class. -/
  findClass_source :
    findClass ct definingClassName = some sourceClass
  /-- Source method membership in the defining class. -/
  method_mem_source :
    sourceMethod ∈ sourceClass.methods
  /-- The defining class member lookup returns the same method. -/
  method_found_source :
    findMethodInList sourceClass.methods attrName = some sourceMethod

private def sourceMethodLookupData_canonical
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (cct : CheckedClassTable)
    (classesCompiled :
      Checked.IsCompiledClassTable
        (embedClassTable p.classes) core cct)
    {recvMro : List Identifier}
    {attrName : Identifier}
    {sourceMethod : Method}
    (source_lookup :
      findMethodInMro p.classes recvMro attrName = some sourceMethod) :
    SourceMethodLookupData
      p.classes recvMro attrName sourceMethod
      (Checked.isCompiledClassTable_findMethodInMro
        classesCompiled
        (findGMethodInMro_embed source_lookup)).definingClassName :=
  match recvMro with
  | [] => by
      simp [findMethodInMro, findMemberInHierarchy] at source_lookup
  | cname :: rest => by
      cases hfind : findClass p.classes cname with
      | none =>
          have hfindG :
              findGClass (embedClassTable p.classes) cname = none := by
            simp [findGClass_embedClassTable_eq, hfind]
          have rest_lookup :
              findMethodInMro p.classes rest attrName = some sourceMethod := by
            simpa [findMethodInMro, findMemberInHierarchy, hfind] using source_lookup
          let restData :=
            sourceMethodLookupData_canonical
              p core cct classesCompiled rest_lookup
          simp only [Checked.isCompiledClassTable_findMethodInMro,
            findMemberInHierarchy_transportData]
          split
          ·
            exact
              SourceMethodLookupData.mk
                (List.Mem.tail cname restData.definingClass_mem)
                restData.sourceClass
                restData.findClass_source
                restData.method_mem_source
                restData.method_found_source
          · rename_i hfindG'
            rw [hfindG] at hfindG'
            cases hfindG'
      | some cls =>
          have hfindG :
              findGClass (embedClassTable p.classes) cname = some (embedClass cls) :=
            findGClass_embedClassTable hfind
          cases hmethod : findMethodInList cls.methods attrName with
          | none =>
              have hmethodG :
                  findGMethodInList (cls.methods.map embedMethod) attrName = none := by
                simp [findGMethodInList_embedMethods_eq, hmethod]
              have rest_lookup :
                  findMethodInMro p.classes rest attrName = some sourceMethod := by
                simpa [findMethodInMro, findMemberInHierarchy, hfind, hmethod] using source_lookup
              let restData :=
                sourceMethodLookupData_canonical
                  p core cct classesCompiled rest_lookup
              simp only [Checked.isCompiledClassTable_findMethodInMro,
                findMemberInHierarchy_transportData]
              split
              · rename_i hfindG'
                rw [hfindG] at hfindG'
                cases hfindG'
              · rename_i gc hfindG'
                have hgc : gc = embedClass cls := by
                  exact Option.some.inj (hfindG'.symm.trans hfindG)
                cases hgc
                split
                ·
                  exact
                    SourceMethodLookupData.mk
                      (List.Mem.tail cname restData.definingClass_mem)
                      restData.sourceClass
                      restData.findClass_source
                      restData.method_mem_source
                      restData.method_found_source
                · rename_i foundGMethod hmethodG'
                  have hmethodG'' :
                      findGMethodInList (cls.methods.map embedMethod) attrName =
                        some foundGMethod := by
                    simpa [findGMethodInList, embedClass] using hmethodG'
                  rw [hmethodG] at hmethodG''
                  cases hmethodG''
          | some foundMethod =>
              have hfound : foundMethod = sourceMethod := by
                simpa [findMethodInMro, findMemberInHierarchy, hfind, hmethod] using source_lookup
              cases hfound
              have hmethodG :
                  findGMethodInList (cls.methods.map embedMethod) attrName =
                    some (embedMethod sourceMethod) := by
                simp [findGMethodInList_embedMethods_eq, hmethod]
              simp only [Checked.isCompiledClassTable_findMethodInMro,
                findMemberInHierarchy_transportData]
              split
              · rename_i hfindG'
                rw [hfindG] at hfindG'
                cases hfindG'
              · rename_i gc hfindG'
                have hgc : gc = embedClass cls := by
                  exact Option.some.inj (hfindG'.symm.trans hfindG)
                cases hgc
                split
                · rename_i hmethodG'
                  have hmethodG'' :
                      findGMethodInList (cls.methods.map embedMethod) attrName = none := by
                    simpa [findGMethodInList, embedClass] using hmethodG'
                  rw [hmethodG] at hmethodG''
                  cases hmethodG''
                ·
                  exact
                    SourceMethodLookupData.mk
                      (List.Mem.head rest)
                      cls
                      hfind
                      (findByName_mem hmethod)
                      hmethod

/-- Source lookup data transported through the canonical compiled method lookup
used by `embedded_static_program_elaborates`. -/
private def sourceMethodLookupData_at_compiledLookup
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (cct : CheckedClassTable)
    (classesCompiled :
      Checked.IsCompiledClassTable
        (embedClassTable p.classes) core cct)
    (source_lookup :
      findMethodInMro p.classes recvMro attrName = some sourceMethod)
    (lookup :
      RelatedHierarchyLookupData
        findCheckedClass CheckedClass.methods CheckedMethod.name
        cct recvMro attrName
        (fun definingClassName gm cm =>
          Checked.IsCompiledMethodAt
            (embedClassTable p.classes) core definingClassName gm cm)
        (embedMethod sourceMethod))
    (lookup_def :
      lookup =
        Checked.isCompiledClassTable_findMethodInMro
          classesCompiled
          (findGMethodInMro_embed source_lookup)) :
    SourceMethodLookupData
      p.classes recvMro attrName sourceMethod lookup.definingClassName := by
  rw [lookup_def]
  exact sourceMethodLookupData_canonical p core cct classesCompiled source_lookup

namespace Checked

/-- The stored method translation proof determines the compiled method. -/
private theorem IsCompiledMethodAt_unique
    (left :
      IsCompiledMethodAt gct hwfct cname gm cm₁)
    (right :
      IsCompiledMethodAt gct hwfct cname gm cm₂) :
    cm₁ = cm₂ := by
  cases cm₁ with
  | mk name₁ receiverParam₁ param₁ paramTy₁ returnTy₁ parameterObligation₁ returnObligation₁ body₁ =>
  cases cm₂ with
  | mk name₂ receiverParam₂ param₂ paramTy₂ returnTy₂ parameterObligation₂ returnObligation₂ body₂ =>
  have hname : name₁ = name₂ :=
    left.name_eq.trans right.name_eq.symm
  have hreceiver : receiverParam₁ = receiverParam₂ :=
    left.receiverParam_eq.trans right.receiverParam_eq.symm
  have hparam : param₁ = param₂ :=
    left.param_eq.trans right.param_eq.symm
  have hparamTy : paramTy₁ = paramTy₂ :=
    left.paramTy_eq.trans right.paramTy_eq.symm
  have hreturnTy : returnTy₁ = returnTy₂ :=
    left.returnTy_eq.trans right.returnTy_eq.symm
  have hparameterObligation : parameterObligation₁ = parameterObligation₂ :=
    left.parameterObligation_eq.trans right.parameterObligation_eq.symm
  have hreturnObligation : returnObligation₁ = returnObligation₂ :=
    left.returnObligation_eq.trans right.returnObligation_eq.symm
  have hbody : body₁ = body₂ := by
    calc
      body₁ =
          compileCheck left.body_hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ cname)]
            .any
            (.methodBody cname gm.name []) := left.body_eq
      _ =
          compileCheck right.body_hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ cname)]
            .any
            (.methodBody cname gm.name []) :=
          compileCheck_sourceCoherent left.body_hsrc right.body_hsrc
            [(gm.param, gm.paramTy), (gm.receiverParam, .class_ cname)]
            .any
            (.methodBody cname gm.name [])
      _ = body₂ := right.body_eq.symm
  cases hname
  cases hreceiver
  cases hparam
  cases hparamTy
  cases hreturnTy
  cases hparameterObligation
  cases hreturnObligation
  cases hbody
  rfl

end Checked

/-- Exact source-to-checked method lookup produced by embedded static
compilation for one runtime receiver MRO lookup. -/
structure ExactEmbeddedMethodLookup
    (p : Program)
    (core : WellFormedGClassTableCore (embedClassTable p.classes))
    (methodBodiesBridge : ∀ cname c m,
      findClass p.classes cname = some c →
      m ∈ c.methods →
      EmbeddedExprBridge p.classes core
        [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
        m.body
        m.returnTy)
    (cct : CheckedClassTable)
    (classesCompiled :
      Checked.IsCompiledClassTable
        (embedClassTable p.classes) core cct)
    (recvMro : List Identifier)
    (attrName : Identifier)
    (sourceMethod : Method)
    (cm : CheckedMethod) : Type where
  /-- Source lookup equality for the exact runtime receiver MRO. -/
  source_lookup :
    findMethodInMro p.classes recvMro attrName = some sourceMethod
  /-- Checked lookup equality produced by the runtime step for the same MRO. -/
  checked_lookup :
    findCheckedMethodInMro cct recvMro attrName = some cm
  /-- Transported lookup data from the compiled class table. -/
  lookup :
    RelatedHierarchyLookupData
      findCheckedClass CheckedClass.methods CheckedMethod.name
      cct recvMro attrName
      (fun definingClassName gm cm =>
        Checked.IsCompiledMethodAt
          (embedClassTable p.classes) core definingClassName gm cm)
      (embedMethod sourceMethod)
  /-- The transported lookup is the canonical compiled lookup for `source_lookup`. -/
  lookup_def :
    lookup =
      Checked.isCompiledClassTable_findMethodInMro
        classesCompiled
        (findGMethodInMro_embed source_lookup)
  /-- Source-side data for the transported defining class. -/
  source_data :
    SourceMethodLookupData
      p.classes recvMro attrName sourceMethod lookup.definingClassName
  /-- The runtime checked method is the exact embedded compiler output. -/
  compiled_method_eq :
    cm =
      compileEmbeddedMethod p core lookup.definingClassName sourceMethod
        (methodBodiesBridge lookup.definingClassName
          source_data.sourceClass
          sourceMethod
          source_data.findClass_source
          source_data.method_mem_source).hsrc

/-- Static typing, source bridges, and exact checked compiler output for one program. -/
structure EmbeddedStaticElaboration (p : Program) : Type where
  /-- The static table rules and permitted method check targets. -/
  staticClassTable : EmbeddableStaticClassTable p.classes
  /-- The static type assigned to the program main expression. -/
  mainTy : Ty
  /-- The typing and inheritance data for the translated class table. -/
  core : WellFormedGClassTableCore (embedClassTable p.classes)
  /-- The embedded gradual source bridge for the program main expression. -/
  mainBridge : EmbeddedExprBridge p.classes core [] p.main mainTy
  /-- Embedded gradual source bridges for method bodies. -/
  methodBodiesBridge : ∀ cname c m,
    findClass p.classes cname = some c →
    m ∈ c.methods →
    EmbeddedExprBridge p.classes core
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy
  /-- The gradual target requested for the checked main expression. -/
  mainTarget : GTy
  /-- The requested main target is the checked-runtime approximation of the main bridge type. -/
  mainTarget_eq :
    mainTarget = approxTarget mainBridge.srcTy
  /-- The checked program produced by compiling the embedded gradual program. -/
  cp : CheckedProgram
  /-- The class-table compilation artifact for the checked program classes. -/
  classesCompiled :
    Checked.IsCompiledClassTable
      (embedClassTable p.classes) core cp.classes
  /-- Proof that each allocated runtime method is the translation of the method selected by source lookup. -/
  methodLookupCompiled : ∀ {recvMro attrName sourceMethod cm},
    findMethodInMro p.classes recvMro attrName = some sourceMethod →
    findCheckedMethodInMro cp.classes recvMro attrName = some cm →
    ExactEmbeddedMethodLookup p core methodBodiesBridge cp.classes
      classesCompiled recvMro attrName sourceMethod cm
  /-- The data-bearing checked elaboration artifact for the embedded gradual program. -/
  compiled : Checked.ElaboratesProgramAt (embedProgram p) mainTarget cp
  /-- Relate the checked program main expression to the compiler output for the
  main bridge. -/
  main_eq :
    cp.main =
      compileCheck mainBridge.hsrc [] mainTarget (.main [])

def embedded_static_program_elaborates
    (hprog : BridgeableStaticProgram p) :
    EmbeddedStaticElaboration p := by
  let classesCompiled :
      Checked.IsCompiledClassTable
        (embedClassTable p.classes)
        hprog.core
        (compileEmbeddedProgram hprog).classes :=
    compileEmbeddedClasses_compiled
      p
      hprog.classTable
      hprog.core
      hprog.methodBodiesBridge
      p.classes
      (fun hc => hc)
  refine
    { staticClassTable := hprog.classTable
      mainTy := hprog.mainTy
      core := hprog.core
      mainBridge := hprog.mainBridge
      methodBodiesBridge := hprog.methodBodiesBridge
      mainTarget := approxTarget hprog.mainBridge.srcTy
      mainTarget_eq := rfl
      cp := compileEmbeddedProgram hprog
      classesCompiled := classesCompiled
      methodLookupCompiled := ?_
      compiled := ?_
      main_eq := rfl }
  · intro recvMro attrName sourceMethod cm source_lookup checked_lookup
    let lookup :=
      Checked.isCompiledClassTable_findMethodInMro
        classesCompiled
        (findGMethodInMro_embed source_lookup)
    let source_data :=
      sourceMethodLookupData_at_compiledLookup
        p
        hprog.core
        (compileEmbeddedProgram hprog).classes
        classesCompiled
        source_lookup
        lookup
        rfl
    have hmember : lookup.member2 = cm := by
      have hfound := lookup.found
      have checked_lookup' :
          findMemberInHierarchy findCheckedClass CheckedClass.methods CheckedMethod.name
            (compileEmbeddedProgram hprog).classes recvMro attrName = some cm := by
        simpa [findCheckedMethodInMro] using checked_lookup
      rw [checked_lookup'] at hfound
      exact (Option.some.inj hfound).symm
    have hcomponent :
        Checked.IsCompiledMethodAt
          (embedClassTable p.classes)
          hprog.core
          lookup.definingClassName
          (embedMethod sourceMethod)
          (compileEmbeddedMethod p hprog.core lookup.definingClassName sourceMethod
            (hprog.methodBodiesBridge lookup.definingClassName
              source_data.sourceClass
              sourceMethod
              source_data.findClass_source
              source_data.method_mem_source).hsrc) :=
      compileEmbeddedMethod_compiled
        p
        hprog.core
        hprog.methodBodiesBridge
        source_data.findClass_source
        source_data.method_mem_source
    have hcompiled : lookup.member2 =
        compileEmbeddedMethod p hprog.core lookup.definingClassName sourceMethod
          (hprog.methodBodiesBridge lookup.definingClassName
            source_data.sourceClass
            sourceMethod
            source_data.findClass_source
            source_data.method_mem_source).hsrc :=
      Checked.IsCompiledMethodAt_unique lookup.related hcomponent
    exact
      { source_lookup := source_lookup
        checked_lookup := checked_lookup
        lookup := lookup
        lookup_def := rfl
        source_data := source_data
        compiled_method_eq := hmember.symm.trans hcompiled }
  refine
    { hwfct := hprog.core
      classes_elab := classesCompiled
      main_srcTy := hprog.mainBridge.srcTy
      main_hsrc := hprog.mainBridge.hsrc
      main_eq := rfl
      target_checkedTarget :=
        approxTarget_checkedTarget
          (gct := embedClassTable p.classes)
          (G := hprog.mainBridge.srcTy)
      target_wf := approxTarget_wellFormed
        (gSrcInfer_sourceWellFormed (by nofun) hprog.mainBridge.hsrc) }

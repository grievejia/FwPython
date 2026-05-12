import FwPython.Static.TypeSystem
import FwPython.Gradual.Embedding
import FwPython.Gradual.Statics
import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.Soundness

/-! # Static-to-gradual embedding bridge

Packages the source-facing static fragment together with the gradual
well-formedness core needed to reuse the existing gradual elaboration and
soundness pipeline. -/

structure EmbeddableStaticClassTable (ct : ClassTable) : Type where
  hwf : WellFormedClassTable ct
  methodSigChecked : ∀ cname c m,
    findClass ct cname = some c →
    m ∈ c.methods →
    RuntimePublicAnnotation (embedClassTable ct) (embedTy m.paramTy) ∧
      RuntimePublicAnnotation (embedClassTable ct) (embedTy m.returnTy)

structure EmbeddableStaticProgram (p : Program) : Type where
  classTable : EmbeddableStaticClassTable p.classes
  mainTy : Ty
  mainTyping : HasType p.classes [] p.main mainTy
  methodBodiesTyped : ∀ cname c m,
    findClass p.classes cname = some c →
    m ∈ c.methods →
    HasType p.classes
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy

theorem wellFormedGTy_embedTy
    (h : WellFormedTy ct T) :
    WellFormedGTy (embedClassTable ct) (embedTy T) := by
  induction T with
  | class_ cname =>
      cases h with
      | class_ hfind hmro =>
          exact .class_ (findGClass_embedClassTable hfind) (computeGMro_embedClassTable hmro)
  | callable P R ihP ihR =>
      cases h with
      | callable hwfP hwfR =>
          exact .callable (ihP hwfP) (ihR hwfR)
  | union T U ihT ihU =>
      cases h with
      | union hwfT hwfU =>
          exact .union (ihT hwfT) (ihU hwfU)
  | intersection T U ihT ihU =>
      cases h with
      | intersection hwfT hwfU =>
          exact .intersection (ihT hwfT) (ihU hwfU)
  | bottom =>
      cases h with
      | bottom =>
          exact .bottom
  | negClass cname =>
      cases h with
      | negClass hfind hmro =>
          exact .negClass (findGClass_embedClassTable hfind) (computeGMro_embedClassTable hmro)

private theorem computeMro_embedClassTable_reverse {ct : ClassTable}
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

private theorem findMethodInMro_embed_reverse {ct : ClassTable}
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
  boolExists := by
    exact ⟨embedClass hemb.hwf.boolExists.cls,
      hemb.hwf.boolExists.mro,
      findGClass_embedClassTable hemb.hwf.boolExists.hfind,
      computeGMro_embedClassTable hemb.hwf.boolExists.hmro⟩
  noneExists := by
    exact ⟨embedClass hemb.hwf.noneExists.cls,
      hemb.hwf.noneExists.mro,
      findGClass_embedClassTable hemb.hwf.noneExists.hfind,
      computeGMro_embedClassTable hemb.hwf.noneExists.hmro⟩
  boundMethodExists := by
    exact ⟨embedClass hemb.hwf.boundMethodExists.cls,
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
  boolLeaf := by
    intro cname gc mro hfindG hmroG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    exact hemb.hwf.builtinsLeaf cname c mro hfind
      (computeMro_embedClassTable_reverse hfind hmroG) hmem
  noneLeaf := by
    intro cname gc mro hfindG hmroG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    exact hemb.hwf.noneLeaf cname c mro hfind
      (computeMro_embedClassTable_reverse hfind hmroG) hmem
  boundMethodLeaf := by
    intro cname gc mro hfindG hmroG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    exact hemb.hwf.boundMethodLeaf cname c mro hfind
      (computeMro_embedClassTable_reverse hfind hmroG) hmem

private theorem gradualLiskovCondition_embedClassTable
    (hemb : EmbeddableStaticClassTable ct) :
    GradualLiskovCondition (embedClassTable ct) := by
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
    exact ⟨wellFormedGTy_embedTy hwfP, wellFormedGTy_embedTy hwfR⟩
  allMethodSignaturesRuntimePublic := by
    intro cname gc gm hfindG hmem
    obtain ⟨c, hfind, hgc⟩ := findClass_embedClassTable_reverse hfindG
    subst hgc
    rcases List.mem_map.mp hmem with ⟨m, hm, rfl⟩
    exact hemb.methodSigChecked cname c m hfind hm

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

theorem embedTyEnv_lookupSource
    {Γ : TyEnv} {x : Identifier} {T : Ty}
    (h : Γ.lookup x = some T) :
    (embedTyEnv Γ).lookupSource x = some (embedTy T) := by
  simp [SBindingEnv.lookupSource, embedTyEnv_lookupBinding h]

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
        (.intersection (embedTy T) (.class_ C)) := by
  simpa [embedTy] using
    embedTyEnv_update Γ x (.intersection T (.class_ C))

theorem embedTyEnv_update_negClass
    (Γ : TyEnv) (x : Identifier) (T : Ty) (C : Identifier) :
    embedTyEnv (Γ.update x (.intersection T (.negClass C))) =
      (embedTyEnv Γ).updateSource x
        (.intersection (embedTy T) (.negClass C)) := by
  simpa [embedTy] using
    embedTyEnv_update Γ x (.intersection T (.negClass C))

theorem sourceEnvOk_embedTyEnv_update_class
    (hwfct : WellFormedClassTable ct)
    (henv : SourceEnvOk (embedClassTable ct) (embedTyEnv Γ))
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some c) :
    SourceEnvOk
      (embedClassTable ct)
      (embedTyEnv (Γ.update x (.intersection T (.class_ C)))) := by
  have hb := sourceEnvOk_lookup henv (embedTyEnv_lookupBinding hlook)
  have hmroC := (hwfct.allMrosExist _ _ hfind).hmro
  have hclassWf :
      WellFormedGTy (embedClassTable ct) (.class_ C) :=
    wellFormedGTy_embedTy (ct := ct) (T := .class_ C) (.class_ hfind hmroC)
  have hnewSrc :
      SourceCallableTy (embedClassTable ct)
        (.intersection (embedTy T) (.class_ C)) :=
    .intersection hb.1 .class_
  have hnewWf :
      WellFormedGTy (embedClassTable ct)
        (.intersection (embedTy T) (.class_ C)) :=
    .intersection hb.2 hclassWf
  have henv' :=
    sourceEnvOk_updateSource henv (embedTyEnv_lookupBinding hlook) hnewSrc hnewWf
  simpa [embedTyEnv_update_class] using henv'

theorem sourceEnvOk_embedTyEnv_update_negClass
    (hwfct : WellFormedClassTable ct)
    (henv : SourceEnvOk (embedClassTable ct) (embedTyEnv Γ))
    (hlook : Γ.lookup x = some T)
    (hfind : findClass ct C = some c) :
    SourceEnvOk
      (embedClassTable ct)
      (embedTyEnv (Γ.update x (.intersection T (.negClass C)))) := by
  have hb := sourceEnvOk_lookup henv (embedTyEnv_lookupBinding hlook)
  have hmroC := (hwfct.allMrosExist _ _ hfind).hmro
  have hnegWf :
      WellFormedGTy (embedClassTable ct) (.negClass C) :=
    wellFormedGTy_embedTy (ct := ct) (T := .negClass C) (.negClass hfind hmroC)
  have hnewSrc :
      SourceCallableTy (embedClassTable ct)
        (.intersection (embedTy T) (.negClass C)) :=
    .intersection hb.1 .negClass
  have hnewWf :
      WellFormedGTy (embedClassTable ct)
        (.intersection (embedTy T) (.negClass C)) :=
    .intersection hb.2 hnegWf
  have henv' :=
    sourceEnvOk_updateSource henv (embedTyEnv_lookupBinding hlook) hnewSrc hnewWf
  simpa [embedTyEnv_update_negClass] using henv'

theorem empty_embedTyEnv_ok :
    SourceEnvOk (embedClassTable ct) (embedTyEnv ([] : TyEnv)) := by
  intro b hb
  cases hb

theorem methodEntry_embedTyEnv_ok
    (hemb : EmbeddableStaticClassTable ct)
    (hfind : findClass ct cname = some c)
    (hm : m ∈ c.methods) :
    SourceEnvOk
      (embedClassTable ct)
      (embedTyEnv [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]) := by
  have hchecked := hemb.methodSigChecked cname c m hfind hm
  have hwfSig := hemb.hwf.allMethodSignaturesWellFormed cname c m hfind hm
  have hmroC := (hemb.hwf.allMrosExist _ _ hfind).hmro
  intro b hb
  simp [embedTyEnv] at hb
  rcases hb with rfl | rfl
  · exact ⟨runtimePublicAnnotation_to_sourceCallableTy _ hchecked.1,
      wellFormedGTy_embedTy hwfSig.1⟩
  · exact ⟨.class_, wellFormedGTy_embedTy (.class_ hfind hmroC)⟩

inductive ViewOnSrc (ct : ClassTable) : Ty → GTy → Type where
  | embed :
      ViewOnSrc ct T (embedTy T)
  | sub :
      IsSubtype ct S T →
      ViewOnSrc ct S G →
      ViewOnSrc ct T G
  | unionStruct :
      ViewOnSrc ct T G →
      ViewOnSrc ct U H →
      ViewOnSrc ct (.union T U) (.union G H)
  | join :
      ViewOnSrc ct T G →
      ViewOnSrc ct U H →
      ViewOnSrc ct (.union T U) (.union G H)
  | interIntro :
      ViewOnSrc ct T G →
      ViewOnSrc ct U G →
      ViewOnSrc ct (.intersection T U) G

inductive AttrSelection (ct : ClassTable) :
    Ty → Identifier → Ty → Type where
  | class_ :
      FindMethodType ct cname attrName paramTy returnTy →
      AttrSelection ct (.class_ cname) attrName (.callable paramTy returnTy)
  | union :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrSelection ct
        (.union (.class_ c1) (.class_ c2))
        attrName
        (.union (.callable p1 r1) (.callable p2 r2))
  | inter :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrSelection ct
        (.intersection (.class_ c1) (.class_ c2))
        attrName
        (.intersection (.callable p1 r1) (.callable p2 r2))

inductive CallSelection (ct : ClassTable) :
    Ty → Ty → Ty → Type where
  | callable :
      CallSelection ct (.callable paramTy returnTy) paramTy returnTy
  | union :
      CallSelection ct calleeTy₁ paramTy₁ returnTy₁ →
      CallSelection ct calleeTy₂ paramTy₂ returnTy₂ →
      CallSelection ct
        (.union calleeTy₁ calleeTy₂)
        (.intersection paramTy₁ paramTy₂)
        (.union returnTy₁ returnTy₂)
  | inter_left :
      CallSelection ct calleeTy₁ paramTy returnTy →
      CallSelection ct
        (.intersection calleeTy₁ calleeTy₂)
        paramTy
        returnTy
  | inter_right :
      CallSelection ct calleeTy₂ paramTy returnTy →
      CallSelection ct
        (.intersection calleeTy₁ calleeTy₂)
        paramTy
        returnTy

structure EmbeddedExprBridge
    (ct : ClassTable)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct))
    (Γ : TyEnv) (e : Expr) (T : Ty) : Type where
  srcTy : GTy
  hsrc : GSrcInfer (embedClassTable ct) hwfct (embedTyEnv Γ) (embedExpr e) srcTy
  view : ViewOnSrc ct T srcTy
  srcSource : SourceCallableTy (embedClassTable ct) srcTy
  srcWellFormed : WellFormedGTy (embedClassTable ct) srcTy

inductive ExprProvenance
    (ct : ClassTable)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct)) :
    {Γ : TyEnv} →
    {e : Expr} → {T : Ty} →
    EmbeddedExprBridge ct hwfct Γ e T → Type where
  | var
      {Γ : TyEnv}
      {x : Identifier}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.var x) T) :
      ExprProvenance ct hwfct bridge
  | constNone
      {Γ : TyEnv}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ .constNone T) :
      ExprProvenance ct hwfct bridge
  | constTrue
      {Γ : TyEnv}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ .constTrue T) :
      ExprProvenance ct hwfct bridge
  | constFalse
      {Γ : TyEnv}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ .constFalse T) :
      ExprProvenance ct hwfct bridge
  | new
      {Γ : TyEnv}
      {cname : Identifier}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.new cname) T) :
      ExprProvenance ct hwfct bridge
  | attrAccess
      {Γ : TyEnv}
      {baseExpr : Expr}
      {recvTy resultTy : Ty}
      {attrName : Identifier}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.attrAccess baseExpr attrName) resultTy)
      (base : EmbeddedExprBridge ct hwfct Γ baseExpr recvTy)
      (pbase : ExprProvenance ct hwfct base)
      (hselect : AttrSelection ct recvTy attrName resultTy)
      (hattr : attrSourceTy? (embedClassTable ct) base.srcTy attrName = some bridge.srcTy)
      (hhsrc : HEq bridge.hsrc (GSrcInfer.attrAccess base.hsrc hattr)) :
      ExprProvenance ct hwfct bridge
  | call
      {Γ : TyEnv}
      {calleeExpr argExpr : Expr}
      {calleeTy argTy paramTy returnTy : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.call calleeExpr argExpr) returnTy)
      (callee : EmbeddedExprBridge ct hwfct Γ calleeExpr calleeTy)
      (pcallee : ExprProvenance ct hwfct callee)
      (arg : EmbeddedExprBridge ct hwfct Γ argExpr argTy)
      (parg : ExprProvenance ct hwfct arg)
      (hselect : CallSelection ct calleeTy paramTy returnTy)
      (hargSub : IsSubtype ct argTy paramTy)
      (hcall :
        callSourceTy?
          (gct := embedClassTable ct)
          (s := calleeSummarySrc (embedClassTable ct) callee.srcTy)
          (argTy := arg.srcTy)
          hwfct
          (callableSummaryOk_calleeSummarySrc callee.srcSource callee.srcWellFormed)
          arg.srcWellFormed
        = some bridge.srcTy)
      (hhsrc :
        HEq bridge.hsrc
          (GSrcInfer.call
            callee.hsrc
            arg.hsrc
            callee.srcSource
            callee.srcWellFormed
            arg.srcWellFormed
            hcall)) :
      ExprProvenance ct hwfct bridge
  | cond
      {Γ : TyEnv}
      {condExpr thenExpr elseExpr : Expr}
      {testTy thenTy elseTy : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.cond condExpr thenExpr elseExpr) (.union thenTy elseTy))
      (hnotIsInstance : (embedExpr condExpr).notIsInstance)
      (condBridge : EmbeddedExprBridge ct hwfct Γ condExpr testTy)
      (pcond : ExprProvenance ct hwfct condBridge)
      (hbool :
        AssignableTo (embedClassTable ct) condBridge.srcTy (.class_ boolClass))
      (thenBridge : EmbeddedExprBridge ct hwfct Γ thenExpr thenTy)
      (pthen : ExprProvenance ct hwfct thenBridge)
      (elseBridge : EmbeddedExprBridge ct hwfct Γ elseExpr elseTy)
      (pelse : ExprProvenance ct hwfct elseBridge)
      (hhsrc :
        HEq bridge.hsrc
          (GSrcInfer.cond
            hnotIsInstance
            condBridge.hsrc
            hbool
            thenBridge.hsrc
            elseBridge.hsrc)) :
      ExprProvenance ct hwfct bridge
  | isInstance
      {Γ : TyEnv}
      {x C : Identifier}
      {T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.isInstance x C) T) :
      ExprProvenance ct hwfct bridge
  | condIsInstance
      {Γ : TyEnv}
      {x C : Identifier}
      {T : Ty}
      {thenExpr elseExpr : Expr}
      {resultTy : Ty}
      {cls : Class}
      (bridge : EmbeddedExprBridge ct hwfct Γ (.cond (.isInstance x C) thenExpr elseExpr) resultTy)
      (hlook : Γ.lookup x = some T)
      (hfind : findClass ct C = some cls)
      (thenBridge :
        EmbeddedExprBridge
          ct
          hwfct
          (Γ.update x (.intersection T (.class_ C)))
          thenExpr
          resultTy)
      (pthen :
        ExprProvenance
          ct
          hwfct
          thenBridge)
      (elseBridge :
        EmbeddedExprBridge
          ct
          hwfct
          (Γ.update x (.intersection T (.negClass C)))
          elseExpr
          resultTy)
      (pelse :
        ExprProvenance
          ct
          hwfct
          elseBridge) :
      ExprProvenance ct hwfct bridge
  | sub
      {Γ : TyEnv}
      {e : Expr}
      {S T : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ e T)
      (child : EmbeddedExprBridge ct hwfct Γ e S)
      (pchild : ExprProvenance ct hwfct child)
      (hsub : IsSubtype ct S T)
      (hhsrc : HEq bridge.hsrc child.hsrc) :
      ExprProvenance ct hwfct bridge
  | interIntro
      {Γ : TyEnv}
      {e : Expr}
      {T U : Ty}
      (bridge : EmbeddedExprBridge ct hwfct Γ e (.intersection T U))
      (left : EmbeddedExprBridge ct hwfct Γ e T)
      (pleft : ExprProvenance ct hwfct left)
      (right : EmbeddedExprBridge ct hwfct Γ e U)
      (pright : ExprProvenance ct hwfct right)
      (hhsrcLeft : HEq bridge.hsrc left.hsrc)
      (hhsrcRight : HEq bridge.hsrc right.hsrc) :
      ExprProvenance ct hwfct bridge

structure ViewWitness
    (ct : ClassTable)
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (T : Ty)
    (v : CheckedValue) : Type where
  srcTy : GTy
  view : ViewOnSrc ct T srcTy
  witness : CheckedValueWitness gct cct heap v srcTy

theorem checkedCallableView_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hview : CheckedCallableView gct cct heap v) :
    CheckedCallableView gct cct heap' v := by
  cases hview with
  | objRefBoundMethod hlook hrecv hmro =>
      exact .objRefBoundMethod (hmono _ _ hlook) (hmono _ _ hrecv) hmro

theorem checkedAnyShape_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hshape : CheckedAnyShape gct cct heap v) :
    CheckedAnyShape gct cct heap' v := by
  cases hshape with
  | objRef hlook =>
      exact .objRef (hmono _ _ hlook)

theorem checkedClassView_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hview : CheckedClassView gct cct heap v cname) :
    CheckedClassView gct cct heap' v cname := by
  cases hview with
  | objRef hlook hfind hmro hmem =>
      exact .objRef (hmono _ _ hlook) hfind hmro hmem

theorem checkedValueWitness_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (w : CheckedValueWitness gct cct heap v G) :
    CheckedValueWitness gct cct heap' v G :=
  match w with
  | .mk hwf (.any hshape) => .mk hwf (.any (checkedAnyShape_heapMono hmono hshape))
  | .mk hwf (.class_ hview) => .mk hwf (.class_ (checkedClassView_heapMono hmono hview))
  | .mk hwf (.callable hview) => .mk hwf (.callable (checkedCallableView_heapMono hmono hview))
  | .mk hwf (.unionLeft wG) => .mk hwf (.unionLeft (checkedValueWitness_heapMono hmono wG))
  | .mk hwf (.unionRight wH) => .mk hwf (.unionRight (checkedValueWitness_heapMono hmono wH))
  | .mk hwf (.intersection wG wH) =>
      .mk hwf (.intersection (checkedValueWitness_heapMono hmono wG)
        (checkedValueWitness_heapMono hmono wH))
  | .mk hwf (.negClass hshape hok) =>
      .mk hwf (.negClass (checkedAnyShape_heapMono hmono hshape)
        (fun ℓ => enforceValue_heapMono hmono (hok ℓ)))

def viewWitness_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (w : ViewWitness ct gct cct heap T v) :
    ViewWitness ct gct cct heap' T v where
  srcTy := w.srcTy
  view := w.view
  witness := checkedValueWitness_heapMono hmono w.witness

theorem checkedValueWitness_class_inv
    (w : CheckedValueWitness gct cct heap v (embedTy (.class_ cname))) :
    CheckedClassView gct cct heap v cname := by
  simpa using checkedValueWitness_class_view w

theorem checkedValueWitness_callable_inv
    (w : CheckedValueWitness gct cct heap v (embedTy (.callable P R))) :
    CheckedCallableView gct cct heap v := by
  simpa using checkedValueWitness_callable_view w

theorem checkedValueWitness_objRef_inv
    (w : CheckedValueWitness gct cct heap v G)
    (hv : v = .objRef oid) :
    ∃ obj, heap.lookup oid = some obj :=
  checkedValueWitness_objRef_lookup w hv

theorem checkedCallableView_payload
    (hview : CheckedCallableView gct cct heap (.objRef oid)) :
    ∃ recvOid recvObj cm,
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid cm⟩ ∧
      heap.lookup recvOid = some recvObj ∧
      CheckedMethodInReceiverMro gct cct recvObj.className cm := by
  cases hview with
  | objRefBoundMethod hlook hrecv hmro =>
      exact ⟨_, _, _, hlook, hrecv, hmro⟩

theorem checkedValueWitness_callable_payload
    (w : CheckedValueWitness gct cct heap (.objRef oid) (.callable P R)) :
    ∃ recvOid recvObj cm,
      heap.lookup oid = some ⟨boundMethodClass, .boundMethod recvOid cm⟩ ∧
      heap.lookup recvOid = some recvObj ∧
      CheckedMethodInReceiverMro gct cct recvObj.className cm :=
  checkedCallableView_payload (checkedValueWitness_callable_view w)

theorem checkedValueWitness_approxFormula
    (w : CheckedValueWitness gct cct heap v G) :
    CheckedValueWitness gct cct heap v (approxFormula G) :=
  match w with
  | .mk hwf (.any hshape) =>
      .mk (approxFormula_wellFormed hwf) (.any hshape)
  | .mk hwf (.class_ hview) =>
      .mk (approxFormula_wellFormed hwf) (.class_ hview)
  | .mk hwf (.callable hview) =>
      .mk (approxFormula_wellFormed hwf) (.any (checkedCallableView_toShape hview))
  | .mk hwf (.unionLeft wG) =>
      .mk (approxFormula_wellFormed hwf)
        (.unionLeft (checkedValueWitness_approxFormula wG))
  | .mk hwf (.unionRight wH) =>
      .mk (approxFormula_wellFormed hwf)
        (.unionRight (checkedValueWitness_approxFormula wH))
  | .mk hwf (.intersection wG wH) =>
      .mk (approxFormula_wellFormed hwf)
        (.intersection
          (checkedValueWitness_approxFormula wG)
          (checkedValueWitness_approxFormula wH))
  | .mk hwf (.negClass hshape hok) =>
      .mk (approxFormula_wellFormed hwf) (.negClass hshape hok)

theorem checkedValueWitness_approxTarget
    (w : CheckedValueWitness gct cct heap v G) :
    CheckedValueWitness gct cct heap v (approxTarget gct G) :=
  match w with
  | .mk hwf (.any hshape) =>
      .mk (approxTarget_wellFormed hwf) (.any hshape)
  | .mk hwf (.class_ hview) =>
      .mk (approxTarget_wellFormed hwf) (.class_ hview)
  | .mk hwf (.callable hview) =>
      .mk (approxTarget_wellFormed hwf) (.callable hview)
  | .mk hwf (.unionLeft wG) =>
      .mk (approxTarget_wellFormed hwf)
        (.unionLeft (checkedValueWitness_approxTarget wG))
  | .mk hwf (.unionRight wH) =>
      .mk (approxTarget_wellFormed hwf)
        (.unionRight (checkedValueWitness_approxTarget wH))
  | .mk hwf (.intersection wG wH) =>
      by
        simpa [approxTarget] using
          checkedValueWitness_approxFormula
            (gct := gct)
            (cct := cct)
            (heap := heap)
            (v := v)
            (.mk hwf (.intersection wG wH))
  | .mk hwf (.negClass hshape hok) =>
      .mk (approxTarget_wellFormed hwf) (.negClass hshape hok)

theorem runtime_receiver_extends_static_class
    (wRecv : CheckedValueWitness
      (embedClassTable ct)
      cct
      heap
      (.objRef oid)
      (embedTy (.class_ cname))) :
    ∃ recvObj recvCls recvMro,
      heap.lookup oid = some recvObj ∧
      findClass ct recvObj.className = some recvCls ∧
      ComputeMro ct recvCls recvMro ∧
      IsSubtype ct (.class_ recvObj.className) (.class_ cname) := by
  cases checkedValueWitness_class_inv wRecv with
  | objRef hlook hfind hmro hmem =>
      obtain ⟨recvCls, hfindRecv, hclsEq⟩ := findClass_embedClassTable_reverse hfind
      subst hclsEq
      exact ⟨_, recvCls, _,
        hlook,
        hfindRecv,
        computeMro_embedClassTable_reverse hfindRecv hmro,
        .class_ hfindRecv (computeMro_embedClassTable_reverse hfindRecv hmro) hmem⟩

theorem typed_method_exists_on_runtime_receiver_embed
    (halign : Checked.AlignedCheckedClassTable (embedClassTable ct) cct)
    {cname attrName : Identifier}
    {paramTy returnTy : Ty}
    (hfmt : FindMethodType ct cname attrName paramTy returnTy)
    {recvClass : Identifier} {recvCls : Class} {recvMro : List Identifier}
    (hsub : IsSubtype ct (.class_ recvClass) (.class_ cname))
    (hfindRecv : findClass ct recvClass = some recvCls)
    (hmroRecv : ComputeMro ct recvCls recvMro) :
    ∃ cm, findCheckedMethodInMro cct recvMro attrName = some cm := by
  obtain ⟨m, hlookupRecv⟩ :=
    typed_method_exists_on_runtime_receiver hfmt hsub hfindRecv hmroRecv
  have hname : m.name = attrName :=
    findMethodInMro_name hlookupRecv
  have hfindRecvG :
      findGClass (embedClassTable ct) recvClass = some (embedClass recvCls) :=
    findGClass_embedClassTable hfindRecv
  have hmroRecvG :
      GComputeMro (embedClassTable ct) (embedClass recvCls) recvMro :=
    computeGMro_embedClassTable hmroRecv
  have hlookupRecvG :
      findGMethodInMro (embedClassTable ct) recvMro (embedMethod m).name = some (embedMethod m) := by
    simpa [embedMethod, hname] using
      (findGMethodInMro_embed hlookupRecv)
  obtain ⟨cc, hfindCc, _, _⟩ :=
    halign.classLookupAgree recvClass (embedClass recvCls) hfindRecvG
  obtain ⟨cm, hfindCm, _, _, _, _⟩ :=
    halign.methodLookupAgree
      recvClass
      (embedClass recvCls)
      cc
      recvMro
      (embedMethod m)
      hfindRecvG
      hfindCc
      hmroRecvG
      hlookupRecvG
  exact ⟨cm, by simpa [embedMethod, hname] using hfindCm⟩

theorem typed_method_variance_on_runtime_receiver_embed
    (hliskov : LiskovCondition ct)
    {cname attrName : Identifier}
    {paramTy returnTy : Ty}
    (hfmt : FindMethodType ct cname attrName paramTy returnTy)
    {recvClass : Identifier} {recvCls : Class} {recvMro : List Identifier}
    (hsub : IsSubtype ct (.class_ recvClass) (.class_ cname))
    (hfindRecv : findClass ct recvClass = some recvCls)
    (hmroRecv : ComputeMro ct recvCls recvMro)
    {m : Method}
    (hlookupRecv : findMethodInMro ct recvMro attrName = some m) :
    AssignableTo (embedClassTable ct)
      (embedTy paramTy)
      (embedTy m.paramTy) ∧
    AssignableTo (embedClassTable ct)
      (embedTy m.returnTy)
      (embedTy returnTy) := by
  obtain ⟨hparam, hreturn⟩ :=
    typed_method_variance_on_runtime_receiver
      hliskov
      hfmt
      hsub
      hfindRecv
      hmroRecv
      hlookupRecv
  exact
    ⟨staticSubtype_to_embeddedAssignableTo hparam,
      staticSubtype_to_embeddedAssignableTo hreturn⟩

theorem attrSelection_runtime_lookup_embed
    (halign : Checked.AlignedCheckedClassTable (embedClassTable ct) cct)
    (hselect : AttrSelection ct recvTy attrName resultTy)
    (wRecv : CheckedValueWitness
      (embedClassTable ct)
      cct
      heap
      (.objRef oid)
      (embedTy recvTy)) :
    ∃ cm recvObj recvCls recvMro,
      heap.lookup oid = some recvObj ∧
      findClass ct recvObj.className = some recvCls ∧
      ComputeMro ct recvCls recvMro ∧
      findCheckedMethodInMro cct recvMro attrName = some cm := by
  have lookup :
      ∀ {cname : Identifier} {pT rT : Ty},
        FindMethodType ct cname attrName pT rT →
        CheckedValueWitness (embedClassTable ct) cct heap (.objRef oid)
          (embedTy (.class_ cname)) →
        ∃ cm recvObj recvCls recvMro,
          heap.lookup oid = some recvObj ∧
          findClass ct recvObj.className = some recvCls ∧
          ComputeMro ct recvCls recvMro ∧
          findCheckedMethodInMro cct recvMro attrName = some cm := by
    intro _ _ _ hfmt w
    rcases runtime_receiver_extends_static_class w with
      ⟨recvObj, recvCls, recvMro, hlook, hfindRecv, hmroRecv, hsub⟩
    obtain ⟨cm, hlookupCm⟩ :=
      typed_method_exists_on_runtime_receiver_embed halign hfmt hsub hfindRecv hmroRecv
    exact ⟨cm, recvObj, recvCls, recvMro, hlook, hfindRecv, hmroRecv, hlookupCm⟩
  cases hselect with
  | class_ hfmt => exact lookup hfmt wRecv
  | union hfmt1 hfmt2 =>
      cases wRecv with
      | mk _ data =>
          cases data with
          | unionLeft wLeft => exact lookup hfmt1 wLeft
          | unionRight wRight => exact lookup hfmt2 wRight
  | inter hfmt1 _ =>
      cases wRecv with
      | mk _ data =>
          cases data with
          | intersection wLeft _ => exact lookup hfmt1 wLeft

structure EmbeddedStaticElaboration (p : Program) : Type where
  mainTy : Ty
  mainTyping : HasType p.classes [] p.main mainTy
  core : WellFormedGClassTableCore (embedClassTable p.classes)
  mainBridge : EmbeddedExprBridge p.classes core [] p.main mainTy
  mainProvenance : ExprProvenance p.classes core mainBridge
  methodBodiesBridge : ∀ cname c m,
    findClass p.classes cname = some c →
    m ∈ c.methods →
    EmbeddedExprBridge p.classes core
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy
  methodBodiesProvenance : ∀ cname c m
    (hfind : findClass p.classes cname = some c)
    (hm : m ∈ c.methods),
    ExprProvenance p.classes core (methodBodiesBridge cname c m hfind hm)
  mainTarget : GTy
  mainTarget_eq :
    mainTarget = approxTarget (embedClassTable p.classes) mainBridge.srcTy
  cp : CheckedProgram
  compiled : Checked.ElaboratesProgramAt (embedProgram p) mainTarget cp
  main_eq : cp.main = (compileCheck .main mainBridge.hsrc [] mainTarget 0).1

/-- A static program together with the explicit gradual source bridges needed
    to compile it through the existing checked pipeline. This is the current
    weakest useful replacement for the too-strong theorem that every arbitrary
    `HasType` derivation embeds into principal gradual source typing. -/
structure BridgeableStaticProgram (p : Program) : Type where
  static : EmbeddableStaticProgram p
  core : WellFormedGClassTableCore (embedClassTable p.classes)
  mainBridge : EmbeddedExprBridge p.classes core [] p.main static.mainTy
  mainProvenance : ExprProvenance p.classes core mainBridge
  methodBodiesBridge : ∀ cname c m,
    findClass p.classes cname = some c →
    m ∈ c.methods →
    EmbeddedExprBridge p.classes core
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy
  methodBodiesProvenance : ∀ cname c m
    (hfind : findClass p.classes cname = some c)
    (hm : m ∈ c.methods),
    ExprProvenance p.classes core (methodBodiesBridge cname c m hfind hm)

private def compileEmbeddedMethod
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
  parameterLabels :=
    castBoundaryLabels
      (by
        have h :=
          (compileBoundaryTarget_eq_compileBoundaryRaw_interp
            (checkedTargetOfGTy (embedTy m.paramTy))).symm
        simp only [interpTarget_checkedTargetOfGTy] at h
        exact h)
      ((mkBoundaryLabels
        (.methodParameter cname m.name)
        .negative
        (compileBoundaryRaw (embedTy m.paramTy))
        0).1)
  returnLabels :=
    castBoundaryLabels
      (by
        have h :=
          (compileBoundaryTarget_eq_compileBoundaryRaw_interp
            (checkedTargetOfGTy (embedTy m.returnTy))).symm
        simp only [interpTarget_checkedTargetOfGTy] at h
        exact h)
      ((mkBoundaryLabels
        (.methodReturn cname m.name)
        .positive
        (compileBoundaryRaw (embedTy m.returnTy))
        0).1)
  body :=
    (compileCheck
      (.methodBody cname m.name)
      hsrc
      [(m.param, embedTy m.paramTy),
       (m.receiverParam, .class_ cname)]
      (embedTy m.returnTy)
      0).1

private theorem compileEmbeddedMethod_compiled
    (hprog : BridgeableStaticProgram p)
    (hfind : findClass p.classes cname = some c)
    (hm : m ∈ c.methods) :
    Checked.IsCompiledMethodAt
      (embedClassTable p.classes)
      cname
      (embedMethod m)
      (compileEmbeddedMethod p hprog.core cname m
        (hprog.methodBodiesBridge cname c m hfind hm).hsrc) where
  name_eq := rfl
  receiverParam_eq := rfl
  param_eq := rfl
  paramTy_eq := by
    simp [compileEmbeddedMethod, embedMethod]
  returnTy_eq := by
    simp [compileEmbeddedMethod, embedMethod]
  paramContract_eq := by
    change
      compileBoundaryTarget (checkedTargetOfGTy (embedTy m.paramTy)) =
        compileBoundaryRaw (interpTarget (checkedTargetOfGTy (embedTy m.paramTy)))
    exact compileBoundaryTarget_eq_compileBoundaryRaw_interp
      (checkedTargetOfGTy (embedTy m.paramTy))
  returnContract_eq := by
    change
      compileBoundaryTarget (checkedTargetOfGTy (embedTy m.returnTy)) =
        compileBoundaryRaw (interpTarget (checkedTargetOfGTy (embedTy m.returnTy)))
    exact compileBoundaryTarget_eq_compileBoundaryRaw_interp
      (checkedTargetOfGTy (embedTy m.returnTy))
  parameterLabels_eq := by
    simp [compileEmbeddedMethod, castBoundaryLabels]
  returnLabels_eq := by
    simp [compileEmbeddedMethod, castBoundaryLabels]
  body_compiled := by
    refine ⟨hprog.core, _, (hprog.methodBodiesBridge cname c m hfind hm).hsrc, ?_⟩
    change
      (compileCheck
        (.methodBody cname m.name)
        (hprog.methodBodiesBridge cname c m hfind hm).hsrc
        [(m.param, embedTy m.paramTy),
         (m.receiverParam, .class_ cname)]
        (embedTy m.returnTy)
        0).1 =
      (compileCheck
        (.methodBody cname m.name)
        (hprog.methodBodiesBridge cname c m hfind hm).hsrc
        [(m.param, embedTy m.paramTy),
         (m.receiverParam, .class_ cname)]
        (embedTy m.returnTy)
        0).1
    rfl

private def compileEmbeddedMethods
    (hprog : BridgeableStaticProgram p)
    (c : Class)
    (hfind : findClass p.classes c.name = some c) :
    (ms : List Method) →
    (∀ {m : Method}, m ∈ ms → m ∈ c.methods) →
    List CheckedMethod
  | [], _ => []
  | m :: ms, hmems =>
      compileEmbeddedMethod p hprog.core c.name m
        (hprog.methodBodiesBridge c.name c m hfind (hmems (.head _))).hsrc ::
      compileEmbeddedMethods hprog c hfind ms
        (fun hm => hmems (.tail _ hm))

private theorem compileEmbeddedMethods_compiled
    (hprog : BridgeableStaticProgram p)
    (c : Class)
    (hfind : findClass p.classes c.name = some c) :
    ∀ (ms : List Method)
      (hmems : ∀ {m : Method}, m ∈ ms → m ∈ c.methods),
      Forall₂
        (Checked.IsCompiledMethodAt (embedClassTable p.classes) c.name)
        (ms.map embedMethod)
        (compileEmbeddedMethods hprog c hfind ms hmems)
  | [], _ => .nil
  | m :: ms, hmems =>
      .cons
        (by
          simpa using
            compileEmbeddedMethod_compiled
              (p := p)
              (hprog := hprog)
              (cname := c.name)
              (c := c)
              (m := m)
              hfind
              (hmems (.head _)))
        (compileEmbeddedMethods_compiled hprog c hfind ms
          (fun hm => hmems (.tail _ hm)))

private def compileEmbeddedClass
    (hprog : BridgeableStaticProgram p)
    (c : Class)
    (hmem : c ∈ p.classes) :
    CheckedClass where
  name := c.name
  baseClasses := c.baseClasses
  methods :=
    compileEmbeddedMethods
      hprog
      c
      (findClass_of_mem hprog.static.classTable.hwf.classNamesUnique hmem)
      c.methods
      (fun hm => hm)

private theorem compileEmbeddedClass_compiled
    (hprog : BridgeableStaticProgram p)
    (c : Class)
    (hmem : c ∈ p.classes) :
    Checked.IsCompiledClass
      (embedClassTable p.classes)
      (embedClass c)
      (compileEmbeddedClass hprog c hmem) where
  name_eq := rfl
  baseClasses_eq := rfl
  methods_compiled := by
    simpa [compileEmbeddedClass] using
      compileEmbeddedMethods_compiled
        (p := p)
        hprog
        c
        (findClass_of_mem hprog.static.classTable.hwf.classNamesUnique hmem)
        c.methods
        (fun hm => hm)

private def compileEmbeddedClasses
    (hprog : BridgeableStaticProgram p) :
    (cs : List Class) →
    (∀ {c : Class}, c ∈ cs → c ∈ p.classes) →
    CheckedClassTable
  | [], _ => []
  | c :: cs, hmems =>
      compileEmbeddedClass hprog c (hmems (.head _)) ::
      compileEmbeddedClasses hprog cs
        (fun hc => hmems (.tail _ hc))

private theorem compileEmbeddedClasses_compiled
    (hprog : BridgeableStaticProgram p) :
    ∀ (cs : List Class)
      (hmems : ∀ {c : Class}, c ∈ cs → c ∈ p.classes),
      Forall₂
        (Checked.IsCompiledClass (embedClassTable p.classes))
        (cs.map embedClass)
        (compileEmbeddedClasses hprog cs hmems)
  | [], _ => .nil
  | c :: cs, hmems =>
      .cons
        (compileEmbeddedClass_compiled
          (p := p)
          hprog
          c
          (hmems (.head _)))
        (compileEmbeddedClasses_compiled hprog cs
          (fun hc => hmems (.tail _ hc)))

private def compileEmbeddedProgram
    (hprog : BridgeableStaticProgram p) :
    CheckedProgram where
  classes := compileEmbeddedClasses hprog p.classes (fun hc => hc)
  main :=
    (compileCheck
      .main
      hprog.mainBridge.hsrc
      []
      (approxTarget (embedClassTable p.classes) hprog.mainBridge.srcTy)
      0).1

def embedded_static_program_elaborates
    (hprog : BridgeableStaticProgram p) :
    EmbeddedStaticElaboration p := by
  refine
    { mainTy := hprog.static.mainTy
      mainTyping := hprog.static.mainTyping
      core := hprog.core
      mainBridge := hprog.mainBridge
      mainProvenance := hprog.mainProvenance
      methodBodiesBridge := hprog.methodBodiesBridge
      methodBodiesProvenance := hprog.methodBodiesProvenance
      mainTarget := approxTarget (embedClassTable p.classes) hprog.mainBridge.srcTy
      mainTarget_eq := rfl
      cp := compileEmbeddedProgram hprog
      compiled := ?_
      main_eq := rfl }
  refine
    { classes_elab := ?_
      hwfct := hprog.core
      main_srcTy := hprog.mainBridge.srcTy
      main_hsrc := hprog.mainBridge.hsrc
      main_eq := rfl
      target_runtimePublic := approxTarget_checkedTarget
      target_wf := approxTarget_wellFormed hprog.mainBridge.srcWellFormed }
  simpa [compileEmbeddedProgram] using
    compileEmbeddedClasses_compiled (p := p) hprog p.classes (fun hc => hc)

private theorem checkedMethod_body_static_bridge
    (hprog : BridgeableStaticProgram p)
    {cname : Identifier} {cc : CheckedClass} {cm : CheckedMethod}
    (hfc : findCheckedClass (embedded_static_program_elaborates hprog).cp.classes cname = some cc)
    (hmem : cm ∈ cc.methods) :
    ∃ c m,
      ∃ _hfind : findClass p.classes cname = some c,
      ∃ _hm : m ∈ c.methods,
        ∃ srcTy,
        ∃ hsrc : GSrcInfer
          (embedClassTable p.classes)
          hprog.core
          (embedTyEnv [(m.param, m.paramTy), (m.receiverParam, .class_ cname)])
          (embedExpr m.body)
          srcTy,
        ∃ _bridge : EmbeddedExprBridge p.classes hprog.core
          [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
          m.body
          m.returnTy,
        cm.body =
          (compileCheck
            (.methodBody cname m.name)
            hsrc
            [(m.param, embedTy m.paramTy),
             (m.receiverParam, .class_ cname)]
            (embedTy m.returnTy)
            0).1 := by
  let helab := embedded_static_program_elaborates hprog
  obtain ⟨gc, gm, hfg, hgm, hcm⟩ :=
    Checked.traceMethodToSource helab.compiled.classes_elab hfc hmem
  obtain ⟨gc', hfg', hgc⟩ :=
    Checked.checkedClass_lookup_to_source helab.compiled hfc
  have hgc' : gc = gc' := by
    exact helab.compiled.hwfct.raw.classNamesUnique _ _
      (findClass_mem hfg)
      (findClass_mem hfg')
      ((findGClass_name hfg).trans (findGClass_name hfg').symm)
  subst gc'
  obtain ⟨c, hfind, hgcEq⟩ := findClass_embedClassTable_reverse hfg
  subst gc
  rcases List.mem_map.mp hgm with ⟨m, hm, hgmEq⟩
  subst gm
  obtain ⟨cm', hcm'mem, hcm'⟩ := Checked.forall₂_mem_left hgc.methods_compiled hgm
  have hcname : c.name = cname := findClass_name hfind
  have hcm'cname :
      Checked.IsCompiledMethodAt
        (embedProgram p).classes
        cname
        (embedMethod m)
        cm' := by
    simpa [hcname] using hcm'
  have hcmEq : cm = cm' :=
    Checked.compiledMethod_named_unique helab.compiled.hwfct helab.compiled
      hfc hmem hcm'mem hcm hcm'cname rfl
  obtain ⟨hwfct', srcTy, hsrc', hbody'⟩ := hcm'cname.body_compiled
  have hcore : hwfct' = hprog.core := Subsingleton.elim _ _
  subst hcore
  refine ⟨c, m, hfind, hm, srcTy, ?_,
    hprog.methodBodiesBridge cname c m hfind hm, ?_⟩
  · simpa [embedProgram, embedMethod]
      using hsrc'
  · simpa [hcmEq, hcname, embedMethod] using hbody'

structure BindingOriginOk
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (surfaceEnv : TyEnv)
    (env : CheckedEnv)
    (Γ : CheckedTyEnv)
    (x : Identifier) : Type where
  surfaceTy : Ty
  checkedTy : GTy
  value : CheckedValue
  hsurface : surfaceEnv.lookup x = some surfaceTy
  henv : env.lookup x = some value
  hchecked : Γ.lookup x = some checkedTy
  viewWitness : ViewWitness ct (embedClassTable ct) cct heap surfaceTy value
  checkedWitness : CheckedValueWitness (embedClassTable ct) cct heap value checkedTy

structure EmbeddedEnvOk
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (surfaceEnv : TyEnv)
    (env : CheckedEnv)
    (Γ : CheckedTyEnv) : Type where
  binding : ∀ x checkedTy, Γ.lookup x = some checkedTy →
    BindingOriginOk ct cct heap surfaceEnv env Γ x

def embeddedEnvOk_nil
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    EmbeddedEnvOk ct cct heap ([] : TyEnv) [] [] where
  binding := by
    intro x checkedTy hlook
    cases hlook

def EmbeddedEnvOk.binding_lookup
    (henvOk : EmbeddedEnvOk ct cct heap surfaceEnv env Γ)
    (hlook : Γ.lookup x = some checkedTy) :
    BindingOriginOk ct cct heap surfaceEnv env Γ x :=
  henvOk.binding x checkedTy hlook

def BindingOriginOk.heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (ok : BindingOriginOk ct cct heap surfaceEnv env Γ x) :
    BindingOriginOk ct cct heap' surfaceEnv env Γ x where
  surfaceTy := ok.surfaceTy
  checkedTy := ok.checkedTy
  value := ok.value
  hsurface := ok.hsurface
  henv := ok.henv
  hchecked := ok.hchecked
  viewWitness := viewWitness_heapMono hmono ok.viewWitness
  checkedWitness := checkedValueWitness_heapMono hmono ok.checkedWitness

def EmbeddedEnvOk.heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (henvOk : EmbeddedEnvOk ct cct heap surfaceEnv env Γ) :
    EmbeddedEnvOk ct cct heap' surfaceEnv env Γ where
  binding := by
    intro x checkedTy hlook
    exact (henvOk.binding x checkedTy hlook).heapMono hmono

structure EnforceFrameOk
    (gct : GClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (v : CheckedValue) : Type where
  target : GTy
  runtimePublic : RuntimePublicAnnotation gct target
  witness : CheckedValueWitness gct cct heap v target

theorem enforceFrameOk_ok_witness
    (ok : EnforceFrameOk gct cct heap v)
    {c : BoundaryContract}
    (hcb : c = compileBoundaryRaw ok.target)
    (labels : BoundaryLabels c)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : Checked.AlignedCheckedClassTable gct cct) :
    ∃ v',
      EnforceValue gct heap v c labels (.ok v') ∧
      CheckedValueWitness gct cct heap v' ok.target :=
  by
    subst hcb
    exact
      (Checked.checkedValueWitness_same_contract
        ok.witness
        ok.runtimePublic
        hheap
        hwfct
        halign
        (ℓ := labels)).1

theorem enforceFrameOk_noBlame
    (ok : EnforceFrameOk gct cct heap v)
    {c : BoundaryContract}
    (hcb : c = compileBoundaryRaw ok.target)
    (labels : BoundaryLabels c)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (halign : Checked.AlignedCheckedClassTable gct cct)
    (henf :
      EnforceValue gct heap v c labels (.blame labels.direct)) :
    False := by
  subst hcb
  exact
    (Checked.checkedValueWitness_same_contract
      ok.witness
      ok.runtimePublic
      hheap
      hwfct
      halign
      (ℓ := labels)).2 henf

structure DynAttrAccessFrameOk
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (oid : Nat)
    (attrName : Identifier) : Type where
  recvTy : Ty
  resultTy : Ty
  attrSelection : AttrSelection ct recvTy attrName resultTy
  recvWitness :
    CheckedValueWitness
      (embedClassTable ct)
      cct
      heap
      (.objRef oid)
      (embedTy recvTy)

theorem dynAttrAccessFrameOk_notFound_impossible
    (halign : Checked.AlignedCheckedClassTable (embedClassTable ct) cct)
    (ok : DynAttrAccessFrameOk ct cct heap oid attrName)
    {obj : CheckedHeapObject}
    {gc : GClass}
    {mro : List Identifier}
    (hlookObj : heap.lookup oid = some obj)
    (hfindCls : findGClass (embedClassTable ct) obj.className = some gc)
    (hMro : GComputeMro (embedClassTable ct) gc mro)
    (hnotfound : findCheckedMethodInMro cct mro attrName = none) :
    False := by
  obtain ⟨cm, recvObj, recvCls, recvMro, hlookRecv, hfindRecv, hmroRecv, hlookup⟩ :=
    attrSelection_runtime_lookup_embed halign ok.attrSelection ok.recvWitness
  rw [hlookObj] at hlookRecv
  cases hlookRecv
  obtain ⟨objCls, hfindObjCls, hgcEq⟩ := findClass_embedClassTable_reverse hfindCls
  subst hgcEq
  have hfindRecv' : findClass ct obj.className = some recvCls := hfindRecv
  rw [hfindObjCls] at hfindRecv'
  cases hfindRecv'
  have hmroObj : ComputeMro ct recvCls mro := by
    simpa using computeMro_embedClassTable_reverse hfindObjCls hMro
  have hmroEq : recvMro = mro :=
    determinism hmroRecv hmroObj
  rw [hmroEq] at hlookup
  simp [hnotfound] at hlookup

structure AwaitArgumentFrameOk
    (ct : ClassTable)
    (cct : CheckedClassTable)
    (heap : CheckedHeap)
    (argVal : CheckedValue)
    (recvOid : Nat)
    (cm : CheckedMethod) : Type where
  recvObj : CheckedHeapObject
  hrecvLookup : heap.lookup recvOid = some recvObj
  resolvedMethod :
    CheckedMethodInReceiverMro
      (embedClassTable ct)
      cct
      recvObj.className
      cm
  argWitness :
    CheckedValueWitness
      (embedClassTable ct)
      cct
      heap
      argVal
      cm.paramTy

theorem awaitArgumentFrameOk_ok_witness
    (halign : Checked.AlignedCheckedClassTable (embedClassTable ct) cct)
    (ok : AwaitArgumentFrameOk ct cct heap argVal recvOid cm)
    (hheap : CheckedHeapWellFormed (embedClassTable ct) cct heap)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct)) :
    ∃ argVal',
      EnforceValue
        (embedClassTable ct)
        heap
        argVal
        cm.parameterContract
        cm.parameterLabels
        (.ok argVal') ∧
      CheckedValueWitness
        (embedClassTable ct)
        cct
        heap
        argVal'
        cm.paramTy := by
  have hcontracts := Checked.checkedMethodInReceiverMro_contracts halign ok.resolvedMethod
  have htargets := Checked.checkedMethodInReceiverMro_runtimePublic halign ok.resolvedMethod
  obtain ⟨argVal', henf, hwit⟩ :=
    enforceFrameOk_ok_witness
      { target := cm.paramTy
        runtimePublic := runtimePublicAnnotation_mk htargets.1.2
        witness := ok.argWitness }
      hcontracts.1
      cm.parameterLabels
      hheap
      hwfct
      halign
  exact ⟨argVal', henf, hwit⟩

theorem awaitArgumentFrameOk_noBlame
    (halign : Checked.AlignedCheckedClassTable (embedClassTable ct) cct)
    (ok : AwaitArgumentFrameOk ct cct heap argVal recvOid cm)
    (hheap : CheckedHeapWellFormed (embedClassTable ct) cct heap)
    (hwfct : WellFormedGClassTableCore (embedClassTable ct))
    (henf :
      EnforceValue
        (embedClassTable ct)
        heap
        argVal
        cm.parameterContract
        cm.parameterLabels
        (.blame cm.parameterLabels.direct)) :
    False := by
  have hcontracts := Checked.checkedMethodInReceiverMro_contracts halign ok.resolvedMethod
  have htargets := Checked.checkedMethodInReceiverMro_runtimePublic halign ok.resolvedMethod
  exact
    enforceFrameOk_noBlame
      { target := cm.paramTy
        runtimePublic := runtimePublicAnnotation_mk htargets.1.2
        witness := ok.argWitness }
      hcontracts.1
      cm.parameterLabels
      hheap
      hwfct
      halign
      henf

inductive StateOriginOk
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap)
    (env : CheckedEnv)
    (ctrl : Checked.Control)
    (cont : Checked.Continuation) : Type where
  | main :
      ctrl = Checked.Control.expr helab.cp.main →
      env = [] →
      cont = ([] : Checked.Continuation) →
      StateOriginOk p helab heap env ctrl cont

structure StaticCheckedStateSafe
    (p : Program)
    (helab : EmbeddedStaticElaboration p)
    (heap : CheckedHeap)
    (env : CheckedEnv)
    (ctrl : Checked.Control)
    (cont : Checked.Continuation)
    (expectedType : GTy) : Type where
  Γ : CheckedTyEnv
  outΓ : CheckedTyEnv
  G : GTy
  heapwf : CheckedHeapWellFormed (embedClassTable p.classes) helab.cp.classes heap
  hwfct : WellFormedGClassTableCore (embedClassTable p.classes)
  halign : Checked.AlignedCheckedClassTable (embedClassTable p.classes) helab.cp.classes
  henv : CheckedEnvHasType (embedClassTable p.classes) helab.cp.classes heap env Γ
  hctrl : Checked.CheckedControlHasType (embedClassTable p.classes) helab.cp.classes heap Γ ctrl G
  hcont :
    Checked.CheckedContinuationHasType
      (embedClassTable p.classes)
      helab.cp.classes
      heap
      Γ
      G
      outΓ
      expectedType
      cont
  surfaceEnv : TyEnv
  envOk : EmbeddedEnvOk p.classes helab.cp.classes heap surfaceEnv env Γ
  originOk : StateOriginOk p helab heap env ctrl cont

def StaticCheckedStateSafe.toCheckedStateSafe
    (hsafe : StaticCheckedStateSafe p helab heap env ctrl cont expectedType) :
    Checked.CheckedStateSafe
      (embedClassTable p.classes)
      helab.cp.classes
      heap
      env
      ctrl
      cont
      expectedType :=
  ⟨hsafe.Γ, hsafe.outΓ, hsafe.G, hsafe.hwfct, hsafe.heapwf,
    hsafe.halign, hsafe.henv, hsafe.hctrl, hsafe.hcont⟩

def embedded_static_initial_safe
    (helab : EmbeddedStaticElaboration p) :
    StaticCheckedStateSafe
      p
      helab
      (Checked.initialState helab.cp).heap
      (Checked.initialState helab.cp).env
      (Checked.initialState helab.cp).control
      (Checked.initialState helab.cp).continuation
      (runtimePublicTy helab.mainTarget) := by
  have htargetChecked :
      RuntimePublicAnnotation (embedClassTable p.classes) helab.mainTarget := by
    rw [helab.mainTarget_eq]
    exact approxTarget_checkedTarget
  have htargetWf :
      WellFormedGTy (embedClassTable p.classes) helab.mainTarget := by
    rw [helab.mainTarget_eq]
    exact approxTarget_wellFormed helab.mainBridge.srcWellFormed
  refine
    { Γ := []
      outΓ := []
      G := runtimePublicTy helab.mainTarget
      heapwf := Checked.checkedHeapInitial_wellFormed helab.core.raw
      hwfct := helab.core
      halign := Checked.alignedCheckedClassTable_of_compiled helab.compiled.hwfct helab.compiled.classes_elab
      henv := ?_
      hctrl := ?_
      hcont := .nil
      surfaceEnv := []
      envOk := ?_
      originOk := ?_ }
  · intro x G hlook
    cases hlook
  · refine .expr ?_
    simpa [helab.main_eq] using
      (compileCheck_checked
        .main
        (henv := empty_embedTyEnv_ok)
        (helab := .nil)
        helab.core
        htargetChecked
        htargetWf
        helab.mainBridge.hsrc)
  · simpa [Checked.initialState, Checked.expressionState] using
      embeddedEnvOk_nil p.classes helab.cp.classes CheckedHeap.initial
  · simpa [Checked.initialState, Checked.expressionState] using
      (StateOriginOk.main (p := p) (helab := helab) rfl rfl rfl)

theorem stateOriginOk_not_blame
    (horig : StateOriginOk p helab heap env ctrl cont) :
    ctrl ≠ Checked.Control.blame ℓ := by
  intro hblame
  cases horig with
  | main hctrl _ _ =>
      rw [hblame] at hctrl
      cases hctrl

structure StaticStepClosedElaboration
    (p : Program)
    (helab : EmbeddedStaticElaboration p) : Type where
  stepClosed :
    ∀ {heap env ctrl cont expectedType s'},
      StaticCheckedStateSafe p helab heap env ctrl cont expectedType →
      Checked.Step
        (embedClassTable p.classes)
        helab.cp.classes
        { heap, env, control := ctrl, continuation := cont }
        s' →
      StaticCheckedStateSafe
        p
        helab
        s'.heap
        s'.env
        s'.control
        s'.continuation
        expectedType

theorem static_checked_preservation_multi
    (hclosed : StaticStepClosedElaboration p helab)
    (hsafe : StaticCheckedStateSafe
      p
      helab
      s.heap
      s.env
      s.control
      s.continuation
      expectedType)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      s
      finalState) :
    Nonempty
      (StaticCheckedStateSafe
        p
        helab
        finalState.heap
        finalState.env
        finalState.control
        finalState.continuation
        expectedType) := by
  induction hsteps generalizing expectedType with
  | refl =>
      exact ⟨hsafe⟩
  | step hstep hrest ih =>
      rcases ih (hclosed.stepClosed hsafe hstep) with ⟨hsafe'⟩
      exact ⟨hsafe'⟩

theorem finalResult_blame_control
    (hfinal : Checked.finalResult? s = some (heap', CheckedResult.blame ℓ)) :
    s.control = Checked.Control.blame ℓ ∧ s.continuation = [] := by
  cases s with
  | mk heap env control continuation =>
      cases control with
      | expr e =>
          cases continuation <;> simp [Checked.finalResult?] at hfinal
      | val v =>
          cases continuation <;> simp [Checked.finalResult?] at hfinal
      | blame lbl =>
          cases continuation with
          | nil =>
              simp [Checked.finalResult?] at hfinal
              rcases hfinal with ⟨_, hℓ⟩
              cases hℓ
              exact ⟨rfl, rfl⟩
          | cons hd tl =>
              simp [Checked.finalResult?] at hfinal
      | runtimeError err =>
          cases continuation <;> simp [Checked.finalResult?] at hfinal

theorem embedded_static_program_success_or_blame
    (helab : EmbeddedStaticElaboration p)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', result)) :
    (∃ v, result = CheckedResult.success v ∧
      CheckedValueWitness
        (embedClassTable p.classes)
        helab.cp.classes
        heap'
        v
        (runtimePublicTy helab.mainTarget)) ∨
    (∃ ℓ, result = CheckedResult.blame ℓ) := by
  exact Checked.gradual_soundness_at helab.compiled hsteps hfinal

theorem embedded_static_program_success_of_no_blame
    (helab : EmbeddedStaticElaboration p)
    (hnoblame :
      ∀ {finalState heap' ℓ},
        Checked.Steps
          (embedClassTable p.classes)
          helab.cp.classes
          (Checked.initialState helab.cp)
          finalState →
        Checked.finalResult? finalState = some (heap', CheckedResult.blame ℓ) →
        False)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', result)) :
    ∃ v, result = CheckedResult.success v := by
  cases embedded_static_program_success_or_blame helab hsteps hfinal with
  | inl hsuccess =>
      rcases hsuccess with ⟨v, hresult, _⟩
      exact ⟨v, hresult⟩
  | inr hblame =>
      rcases hblame with ⟨ℓ, hresult⟩
      exact False.elim (hnoblame hsteps (hresult ▸ hfinal))

theorem embedded_static_no_blame
    (helab : EmbeddedStaticElaboration p)
    (hclosed : StaticStepClosedElaboration p helab)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', CheckedResult.blame ℓ)) :
    False := by
  have hsafe :=
    static_checked_preservation_multi
      (p := p)
      (helab := helab)
      hclosed
      (embedded_static_initial_safe helab)
      hsteps
  rcases hsafe with ⟨hsafeFinal⟩
  have hnotBlame : finalState.control ≠ Checked.Control.blame ℓ :=
    stateOriginOk_not_blame hsafeFinal.originOk
  obtain ⟨hctrl, _⟩ := finalResult_blame_control hfinal
  exact hnotBlame hctrl

theorem embedded_static_success
    (helab : EmbeddedStaticElaboration p)
    (hclosed : StaticStepClosedElaboration p helab)
    (hsteps : Checked.Steps
      (embedClassTable p.classes)
      helab.cp.classes
      (Checked.initialState helab.cp)
      finalState)
    (hfinal : Checked.finalResult? finalState = some (heap', result)) :
    ∃ v, result = CheckedResult.success v :=
  embedded_static_program_success_of_no_blame helab
    (fun hsteps' hfinal' => embedded_static_no_blame helab hclosed hsteps' hfinal')
    hsteps hfinal

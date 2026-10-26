import FwPython.Static.Semantics.StateTyping
import FwPython.Static.Semantics.MultiStep
import FwPython.Static.Semantics.HeapPreservation
import FwPython.Static.TypeSystem.TypingLemmas
import FwPython.Static.TypeSystem.WellFormedness
import FwPython.Static.Semantics.Heap
import FwPython.Static.Subtyping.Inversion

open FwPython.Static.Subtyping

/-! # Preservation for Safe States

One-step preservation: stepping from a safe state produces a safe state. -/

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

namespace SmallStep

/-! ## Monotonicity of frame and continuation typing under heap extension -/

/-- Frame typing is preserved when every object lookup in the first heap holds in the second. -/
private def frameHasType_mono
    (hf : FrameHasType structural h inΓ inTy outΓ outTy f)
    (hmono : ∀ {oid obj}, h.lookup oid = some obj → h'.lookup oid = some obj) :
    FrameHasType structural h' inΓ inTy outΓ outTy f :=
  match hf with
  | .attrAccess hfmt hsub => .attrAccess hfmt hsub
  | .attrAccessUnion hfmt1 hfmt2 hsub => .attrAccessUnion hfmt1 hfmt2 hsub
  | .callCallee harg hsub => .callCallee harg hsub
  | .awaitArgument hlook hprov hsub => .awaitArgument (hmono hlook) hprov hsub
  | .cond hthen helse hsub => .cond hthen helse hsub
  | .returnTo henv => .returnTo (env_has_type_mono henv hmono)
  | .interIntro hf1 hf2 hwfIn1 hwfIn2 =>
    .interIntro (frameHasType_mono hf1 hmono) (frameHasType_mono hf2 hmono) hwfIn1 hwfIn2
  | .sub hf' hsub => .sub (frameHasType_mono hf' hmono) hsub

private theorem continuationHasType_mono
    (hk : ContinuationHasType structural h inΓ inTy outΓ outTy k)
    (hmono : ∀ {oid obj}, h.lookup oid = some obj → h'.lookup oid = some obj) :
    ContinuationHasType structural h' inΓ inTy outΓ outTy k := by
  induction hk with
  | nil => exact .nil
  | cons hf _ ih => exact .cons (frameHasType_mono hf hmono) ih

/-! ## Focus rule helpers: construct `FrameHasType` directly from typing -/

/-- A typed attribute access supplies its receiver type and a frame that produces the result. -/
private theorem attrAccess_frame_of_type
    (hwf : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hty : HasType hwf.toWellFormedClassHierarchy Γ (.attrAccess base attrName) T) :
    ∃ Tbase,
      HasType hwf.toWellFormedClassHierarchy Γ base Tbase ∧
      FrameHasType hwf.toWellFormedClassHierarchy h Γ Tbase Γ T (.attrAccess attrName) := by
  generalize he : Expr.attrAccess base attrName = e at hty
  induction hty with
  | sub _ hsub ih =>
    obtain ⟨Tbase, hbase, hframe⟩ := ih hΓwf he
    exact ⟨Tbase, hbase, .sub hframe hsub⟩
  | attrAccess hbase hfmt =>
    cases he
    exact ⟨_, hbase, .attrAccess hfmt (.refl (findMethodType_wellFormed hwf hfmt))⟩
  | attrAccessUnion hbase hfmt1 hfmt2 =>
    cases he
    exact ⟨_, hbase, .attrAccessUnion hfmt1 hfmt2 (.refl
      (.union (findMethodType_wellFormed hwf hfmt1)
        (findMethodType_wellFormed hwf hfmt2)))⟩
  | interIntro _ _ ih1 ih2 =>
    obtain ⟨Tbase₁, hbase₁, hframe₁⟩ := ih1 hΓwf he
    obtain ⟨Tbase₂, hbase₂, hframe₂⟩ := ih2 hΓwf he
    exact ⟨.intersection Tbase₁ Tbase₂,
      .interIntro hbase₁ hbase₂,
      .interIntro hframe₁ hframe₂
        (hasType_wellFormed hwf hΓwf hbase₁)
        (hasType_wellFormed hwf hΓwf hbase₂)⟩
  | _ => exact Expr.noConfusion he

/-- A typed call supplies its callee type and a frame that evaluates the argument next. -/
private theorem call_frame_of_type
    (hwf : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hty : HasType hwf.toWellFormedClassHierarchy Γ (.call callee arg) T) :
    ∃ calleeTy,
      HasType hwf.toWellFormedClassHierarchy Γ callee calleeTy ∧
      FrameHasType hwf.toWellFormedClassHierarchy h Γ calleeTy Γ T (.callCallee arg) := by
  generalize he : Expr.call callee arg = e at hty
  induction hty with
  | sub _ hsub ih =>
    obtain ⟨calleeTy, hcallee, hframe⟩ := ih hΓwf he
    exact ⟨calleeTy, hcallee, .sub hframe hsub⟩
  | call hcallee harg hsubArg =>
    cases he
    have hwfReturn := (hasType_wellFormed hwf hΓwf hcallee).callable_return
    have hargParam := HasType.sub harg hsubArg
    exact ⟨_, hcallee, .callCallee hargParam (.refl hwfReturn)⟩
  | interIntro _ _ ih1 ih2 =>
    obtain ⟨calleeTy₁, hcallee₁, hframe₁⟩ := ih1 hΓwf he
    obtain ⟨calleeTy₂, hcallee₂, hframe₂⟩ := ih2 hΓwf he
    exact ⟨.intersection calleeTy₁ calleeTy₂,
      .interIntro hcallee₁ hcallee₂,
      .interIntro hframe₁ hframe₂
        (hasType_wellFormed hwf hΓwf hcallee₁)
        (hasType_wellFormed hwf hΓwf hcallee₂)⟩
  | _ => exact Expr.noConfusion he

/-- A typed conditional supplies its test type and a frame that selects a typed branch. -/
private theorem cond_frame_of_type
    (hwf : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hty : HasType hwf.toWellFormedClassHierarchy Γ (.cond condExpr thenBr elseBr) T)
    (hne : ∀ x C, condExpr ≠ .isInstance x C) :
    ∃ Tcond,
      HasType hwf.toWellFormedClassHierarchy Γ condExpr Tcond ∧
      FrameHasType hwf.toWellFormedClassHierarchy h Γ Tcond Γ T (.cond thenBr elseBr) := by
  generalize he : Expr.cond condExpr thenBr elseBr = e at hty
  induction hty generalizing condExpr thenBr elseBr with
  | sub _ hsub ih =>
    obtain ⟨Tcond, hcondExpr, hframe⟩ := ih hΓwf hne he
    exact ⟨Tcond, hcondExpr, .sub hframe hsub⟩
  | cond hcond hbool hthen helse =>
    cases he
    have hcondBool := HasType.sub hcond hbool
    have hwfUnion : WellFormedTy _ (.union _ _) :=
      .union (hasType_wellFormed hwf hΓwf hthen) (hasType_wellFormed hwf hΓwf helse)
    exact ⟨_, hcondBool,
      .cond
        (.sub hthen (.unionLeft (.refl hwfUnion.union_left) hwfUnion.union_right))
        (.sub helse (.unionRight (.refl hwfUnion.union_right) hwfUnion.union_left))
        (.refl hwfUnion)⟩
  | condIsInstance _ _ _ _ =>
    cases he
    exact (hne _ _ rfl).elim
  | interIntro _ _ ih1 ih2 =>
    obtain ⟨Tcond₁, hcond₁, hframe₁⟩ := ih1 hΓwf hne he
    obtain ⟨Tcond₂, hcond₂, hframe₂⟩ := ih2 hΓwf hne he
    exact ⟨.intersection Tcond₁ Tcond₂,
      .interIntro hcond₁ hcond₂,
      .interIntro hframe₁ hframe₂
        (hasType_wellFormed hwf hΓwf hcond₁)
        (hasType_wellFormed hwf hΓwf hcond₂)⟩
  | _ => exact Expr.noConfusion he

/-! ## `condIsInstance` typing helpers -/

/-- Type the then-branch at the narrowed environment, by induction on the
    original conditional typing. -/
private theorem condIsInstanceTrue_typing
    (hwf : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hty : HasType hwf.toWellFormedClassHierarchy Γ (.cond (.isInstance x C) thenBr elseBr) T)
    (hlookΓ : Γ.lookup x = some S)
    (hfindCls : findClass ct C = some cls) :
    HasType hwf.toWellFormedClassHierarchy (Γ.update x (.intersection S (.class_ C))) thenBr T := by
  generalize he : Expr.cond (.isInstance x C) thenBr elseBr = e at hty
  induction hty generalizing x C S cls thenBr elseBr with
  | cond _ _ hthen helse =>
    cases he
    exact .sub
      (hasType_strengthen_var hthen hlookΓ (.interLeft (.refl (hΓwf _ _ hlookΓ)) (WellFormedTy.class_of_lookup hfindCls)))
      (.unionLeft (.refl (hasType_wellFormed hwf hΓwf hthen)) (hasType_wellFormed hwf hΓwf helse))
  | condIsInstance hlookΓ' _ hthen helse =>
    cases he
    have heq := Option.some.inj (hlookΓ'.symm.trans hlookΓ)
    subst heq
    have hΓThen := wellFormedTyEnv_update_class hΓwf hlookΓ hfindCls
    have hΓElse := wellFormedTyEnv_update_negClass hΓwf hlookΓ hfindCls
    exact .sub hthen
      (.unionLeft (.refl (hasType_wellFormed hwf hΓThen hthen)) (hasType_wellFormed hwf hΓElse helse))
  | sub _ hsub ih =>
    exact .sub (ih hΓwf hlookΓ hfindCls he) hsub
  | interIntro _ _ ih1 ih2 =>
    exact .interIntro (ih1 hΓwf hlookΓ hfindCls he)
      (ih2 hΓwf hlookΓ hfindCls he)
  | _ => exact Expr.noConfusion he

/-- Type the else-branch at the narrowed environment, by induction on the
    original conditional typing. -/
private theorem condIsInstanceFalse_typing
    (hwf : WellTypedClassHierarchy ct)
    (hΓwf : WellFormedTyEnv ct Γ)
    (hty : HasType hwf.toWellFormedClassHierarchy Γ (.cond (.isInstance x C) thenBr elseBr) T)
    (hlookΓ : Γ.lookup x = some S)
    (hfindCls : findClass ct C = some cls) :
    HasType hwf.toWellFormedClassHierarchy (Γ.update x (.intersection S (.negClass C))) elseBr T := by
  generalize he : Expr.cond (.isInstance x C) thenBr elseBr = e at hty
  induction hty generalizing x C S cls thenBr elseBr with
  | cond _ _ hthen helse =>
    cases he
    exact .sub
      (hasType_strengthen_var helse hlookΓ (.interLeft (.refl (hΓwf _ _ hlookΓ)) (WellFormedTy.negClass_of_lookup hfindCls)))
      (.unionRight (.refl (hasType_wellFormed hwf hΓwf helse)) (hasType_wellFormed hwf hΓwf hthen))
  | condIsInstance hlookΓ' _ hthen helse =>
    cases he
    have heq := Option.some.inj (hlookΓ'.symm.trans hlookΓ)
    subst heq
    have hΓThen := wellFormedTyEnv_update_class hΓwf hlookΓ hfindCls
    have hΓElse := wellFormedTyEnv_update_negClass hΓwf hlookΓ hfindCls
    exact .sub helse
      (.unionRight (.refl (hasType_wellFormed hwf hΓElse helse)) (hasType_wellFormed hwf hΓThen hthen))
  | sub _ hsub ih =>
    exact .sub (ih hΓwf hlookΓ hfindCls he) hsub
  | interIntro _ _ ih1 ih2 =>
    exact .interIntro (ih1 hΓwf hlookΓ hfindCls he)
      (ih2 hΓwf hlookΓ hfindCls he)
  | _ => exact Expr.noConfusion he

/-! ## Frame/continuation environment strengthening -/

/-- For non-returnTo frames, the output env equals the input env. -/
private theorem frame_preserves_env
    (hf : FrameHasType structural h inΓ inTy outΓ outTy f)
    (hne : ∀ e, f ≠ .returnTo e) :
    outΓ = inΓ := by
  induction hf with
  | returnTo _ => exact absurd rfl (hne _)
  | interIntro _ _ _ _ ih1 _ => exact ih1 hne
  | sub _ _ ih => exact ih hne
  | _ => rfl

/-- A returnTo frame's input env can be freely replaced (it appears only as
    an index, not in any premise). -/
private theorem frameHasType_returnTo_reindex
    (hf : FrameHasType structural h inΓ inTy outΓ outTy (Frame.returnTo callerEnv)) :
    FrameHasType structural h inΓ' inTy outΓ outTy (Frame.returnTo callerEnv) := by
  generalize hfeq : Frame.returnTo callerEnv = f at hf
  induction hf generalizing inΓ' with
  | returnTo henvR => cases hfeq; exact .returnTo henvR
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    exact .interIntro (ih1 hfeq) (ih2 hfeq) hwfIn1 hwfIn2
  | sub _ hsub ih => exact .sub (ih hfeq) hsub
  | _ => exact Frame.noConfusion hfeq

/-- Strengthen a non-returnTo frame's input environment at a variable.
    Since non-returnTo frames have outΓ = inΓ, both envs are strengthened. -/
private theorem frameHasType_strengthen_var
    {inΓ outΓ : TyEnv}
    (hf : FrameHasType structural h inΓ inTy outΓ outTy f)
    (hout : outΓ = inΓ)
    (hne : ∀ e, f ≠ Frame.returnTo e)
    (hlook : inΓ.lookup z = some oldTy)
    (hsub : IsSubtype structural newTy oldTy) :
    FrameHasType structural h (inΓ.update z newTy) inTy (inΓ.update z newTy) outTy f := by
  induction hf with
  | attrAccess hfmt hsub' =>
    cases hout; exact FrameHasType.attrAccess hfmt hsub'
  | attrAccessUnion hfmt1 hfmt2 hsub' =>
    cases hout; exact FrameHasType.attrAccessUnion hfmt1 hfmt2 hsub'
  | callCallee harg hsub' =>
    cases hout
    exact FrameHasType.callCallee
      (hasType_strengthen_var harg hlook hsub)
      hsub'
  | awaitArgument hlookH hprov hsub' =>
    cases hout; exact FrameHasType.awaitArgument hlookH hprov hsub'
  | cond hthen helse hsub' =>
    cases hout
    exact FrameHasType.cond
      (hasType_strengthen_var hthen hlook hsub)
      (hasType_strengthen_var helse hlook hsub)
      hsub'
  | returnTo _ => exact absurd rfl (hne _)
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    cases hout
    exact FrameHasType.interIntro (ih1 rfl hne hlook)
      (ih2 rfl hne hlook) hwfIn1 hwfIn2
  | sub _ hsub' ih =>
    exact FrameHasType.sub (ih hout hne hlook) hsub'

/-- Strengthen a continuation's input environment at a variable. -/
private theorem continuationHasType_strengthen_var
    (hk : ContinuationHasType structural h inΓ inTy outΓ outTy k)
    (hlook : inΓ.lookup z = some oldTy)
    (hsub : IsSubtype structural newTy oldTy) :
    ∃ outΓ', ContinuationHasType structural h (inΓ.update z newTy) inTy outΓ' outTy k := by
  induction hk generalizing z oldTy newTy with
  | nil => exact ⟨_, ContinuationHasType.nil⟩
  | cons hf hrest ih =>
    rename_i _ _ _ _ f _ _ _
    cases f with
    | returnTo =>
      exact ⟨_, ContinuationHasType.cons (frameHasType_returnTo_reindex hf) hrest⟩
    | attrAccess | callCallee | awaitArgument | cond =>
      have heq := frame_preserves_env hf (by intro _ heq; exact Frame.noConfusion heq)
      subst heq
      have hfStrong := frameHasType_strengthen_var hf rfl
        (by intro _ heq; exact Frame.noConfusion heq) hlook hsub
      obtain ⟨outΓ', hrest'⟩ := ih hlook hsub
      exact ⟨outΓ', ContinuationHasType.cons hfStrong hrest'⟩

/-! ## Return-rule helpers

Each return rule needs to handle `interIntro`/`sub` wrapping in the
frame typing. These helpers do induction on `FrameHasType` for each
frame type. -/

/-- returnFromBody: value passes through, env restored from returnTo frame. -/
private theorem returnFromBody_helper
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.returnTo callerEnv))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap v T) :
    ValueHasType hwf.toWellFormedClassHierarchy heap v midTy ∧ EnvHasType hwf.toWellFormedClassHierarchy heap callerEnv midΓ := by
  generalize hfeq : Frame.returnTo callerEnv = f at hframe
  induction hframe with
  | returnTo henvR => cases hfeq; exact ⟨hval, henvR⟩
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨hval1, henv1⟩ := ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) hfeq
    obtain ⟨hval2, _⟩ := ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1)) hfeq
    exact ⟨.interIntro hval1 hval2
      (.intersection (valueHasType_wellFormed hwf hheap hval1)
        (valueHasType_wellFormed hwf hheap hval2)), henv1⟩
  | sub _ hsub ih =>
    obtain ⟨hval', henv'⟩ := ih hval hfeq
    exact ⟨.sub hval' hsub, henv'⟩
  | _ => exact Frame.noConfusion hfeq

/-- returnCondTrue: select then branch from cond frame. -/
private theorem returnCondTrue_helper
    (hframe : FrameHasType structural heap Γ T midΓ midTy (Frame.cond thenBr elseBr))
    (hval : ValueHasType structural heap (Value.objRef trueOid) T)
    (henv : EnvHasType structural heap env Γ) :
    HasType structural midΓ thenBr midTy ∧ EnvHasType structural heap env midΓ := by
  generalize hfeq : Frame.cond thenBr elseBr = f at hframe
  induction hframe with
  | cond hthen _ hsubR => cases hfeq; exact ⟨.sub hthen hsubR, henv⟩
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨h1, henv1⟩ := ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) henv hfeq
    obtain ⟨h2, _⟩ := ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1)) henv hfeq
    exact ⟨.interIntro h1 h2, henv1⟩
  | sub _ hsub ih =>
    obtain ⟨h, henv'⟩ := ih hval henv hfeq
    exact ⟨.sub h hsub, henv'⟩
  | _ => exact Frame.noConfusion hfeq

/-- returnCondFalse: select else branch from cond frame. -/
private theorem returnCondFalse_helper
    (hframe : FrameHasType structural heap Γ T midΓ midTy (Frame.cond thenBr elseBr))
    (hval : ValueHasType structural heap (Value.objRef falseOid) T)
    (henv : EnvHasType structural heap env Γ) :
    HasType structural midΓ elseBr midTy ∧ EnvHasType structural heap env midΓ := by
  generalize hfeq : Frame.cond thenBr elseBr = f at hframe
  induction hframe with
  | cond _ helse hsubR => cases hfeq; exact ⟨.sub helse hsubR, henv⟩
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨h1, henv1⟩ := ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) henv hfeq
    obtain ⟨h2, _⟩ := ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1)) henv hfeq
    exact ⟨.interIntro h1 h2, henv1⟩
  | sub _ hsub ih =>
    obtain ⟨h, henv'⟩ := ih hval henv hfeq
    exact ⟨.sub h hsub, henv'⟩
  | _ => exact Frame.noConfusion hfeq

/-- returnCondNotBool: contradiction — the cond value must be true or false. -/
private theorem returnCondNotBool_helper
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.cond thenBr elseBr))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap (Value.objRef condOid) T)
    (hneTrue : condOid ≠ trueOid)
    (hneFalse : condOid ≠ falseOid) : False := by
  generalize hfeq : Frame.cond thenBr elseBr = f at hframe
  induction hframe with
  | cond _ _ _ =>
    cases hfeq
    -- T = .class_ boolClass, so condOid must be trueOid or falseOid
    obtain ⟨_, hlookActual⟩ := objRef_has_heap_entry hval
    obtain ⟨_, _, hfind_c, hmro_c⟩ := hheap.classesExist _ _ hlookActual
    have hsubClass := objRef_class_subtype hwf hheap hval hlookActual hfind_c hmro_c
    have hbool := bool_subtype_is_bool hwf hsubClass hfind_c hmro_c
    rcases hheap.boolExhaustive _ _ hlookActual hbool with rfl | rfl
    · exact hneTrue rfl
    · exact hneFalse rfl
  | interIntro _ _ hwfIn1 hwfIn2 ih1 _ =>
    exact ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) hfeq
  | sub _ _ ih => exact ih hval hfeq
  | _ => exact Frame.noConfusion hfeq

/-- returnAttrAccess: allocate bound method and produce the typed result. -/
private theorem returnAttrAccess_helper
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.attrAccess attrName))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap (Value.objRef objOid) T)
    (hlookObj : heap.lookup objOid = some obj)
    (hfindClass : findClass ct obj.className = some c)
    (hmroEval : ComputeMro ct c mro)
    (hmethodEval : findMethodInMro ct mro attrName = some m)
    (halloc : heap.alloc ⟨boundMethodClass, ObjectPayload.boundMethod objOid m⟩ = (bmOid, heap'))
    (henv : EnvHasType hwf.toWellFormedClassHierarchy heap env Γ) :
    ValueHasType hwf.toWellFormedClassHierarchy heap' (Value.objRef bmOid) midTy ∧
    EnvHasType hwf.toWellFormedClassHierarchy heap' env midΓ ∧
    HeapWellFormed ct heap' := by
  have hmono : ∀ {oid' obj'}, heap.lookup oid' = some obj' → heap'.lookup oid' = some obj' :=
    fun hlk => heap_alloc_preserves_old hheap.idsBounded halloc hlk
  have hlookBM := heap_alloc_lookup_new halloc
  generalize hfeq : Frame.attrAccess attrName = f at hframe
  induction hframe generalizing hlookObj hfindClass hmroEval hmethodEval halloc with
  | attrAccess hfmt hsub =>
    cases hfeq
    have hsubClass := objRef_class_subtype hwf hheap hval hlookObj hfindClass hmroEval
    have ⟨hpvar, hrvar⟩ := typed_method_variance_on_runtime_receiver hwf
      hfmt hsubClass hfindClass hmroEval hmethodEval
    have hheap' := step_preserves_heapWellFormed
      (s := { heap, env := [], control := Control.val (Value.objRef objOid),
              continuation := [Frame.attrAccess attrName] })
      (Step.returnAttrAccess hlookObj hfindClass hmroEval hmethodEval halloc) hheap hwf
    exact ⟨ValueHasType.sub (ValueHasType.sub (ValueHasType.objRefCallable hlookBM)
      (IsSubtype.callable hpvar hrvar)) hsub,
      env_has_type_mono henv hmono, hheap'⟩
  | attrAccessUnion hfmt1 hfmt2 hsub =>
    cases hfeq
    have hbm := ValueHasType.objRefCallable (structural := hwf.toWellFormedClassHierarchy) hlookBM
    have hheap' := step_preserves_heapWellFormed
      (s := { heap, env := [], control := Control.val (Value.objRef objOid),
              continuation := [Frame.attrAccess attrName] })
      (Step.returnAttrAccess hlookObj hfindClass hmroEval hmethodEval halloc) hheap hwf
    rcases objRef_union_class_decompose hwf hheap hval hlookObj hfindClass hmroEval with hsub1 | hsub2
    · have ⟨hpvar, hrvar⟩ := typed_method_variance_on_runtime_receiver hwf
        hfmt1 hsub1 hfindClass hmroEval hmethodEval
      exact ⟨ValueHasType.sub (ValueHasType.sub hbm (IsSubtype.callable hpvar hrvar))
        (subtype_union_iff.mp hsub).1,
        env_has_type_mono henv hmono, hheap'⟩
    · have ⟨hpvar, hrvar⟩ := typed_method_variance_on_runtime_receiver hwf
        hfmt2 hsub2 hfindClass hmroEval hmethodEval
      exact ⟨ValueHasType.sub (ValueHasType.sub hbm (IsSubtype.callable hpvar hrvar))
        (subtype_union_iff.mp hsub).2,
        env_has_type_mono henv hmono, hheap'⟩
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨hval1, henv1, hheap1⟩ := ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2))
      hlookObj hfindClass hmroEval hmethodEval halloc henv hfeq
    obtain ⟨hval2, _, _⟩ := ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1))
      hlookObj hfindClass hmroEval hmethodEval halloc henv hfeq
    exact ⟨.interIntro hval1 hval2
      (.intersection (valueHasType_wellFormed hwf hheap1 hval1)
        (valueHasType_wellFormed hwf hheap1 hval2)), henv1, hheap1⟩
  | sub _ hsub ih =>
    obtain ⟨hval', henv', hheap'⟩ := ih hval hlookObj hfindClass hmroEval hmethodEval halloc henv hfeq
    exact ⟨.sub hval' hsub, henv', hheap'⟩
  | _ => exact Frame.noConfusion hfeq

/-- returnAttrAccessNotFound: contradiction — typed method must exist. -/
private theorem returnAttrAccessNotFound_helper
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.attrAccess attrName))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap (Value.objRef objOid) T)
    (hlookObj : heap.lookup objOid = some obj)
    (hfindClass : findClass ct obj.className = some c)
    (hmroEval : ComputeMro ct c mro)
    (hmethodNotFound : findMethodInMro ct mro attrName = none) : False := by
  generalize hfeq : Frame.attrAccess attrName = f at hframe
  induction hframe generalizing hlookObj hfindClass hmroEval hmethodNotFound with
  | attrAccess hfmt _ =>
    cases hfeq
    have hsubClass := objRef_class_subtype hwf hheap hval hlookObj hfindClass hmroEval
    obtain ⟨_, hm⟩ := typed_method_exists_on_runtime_receiver hwf hfmt hsubClass hfindClass hmroEval
    simp [hmethodNotFound] at hm
  | attrAccessUnion hfmt1 hfmt2 _ =>
    cases hfeq
    rcases objRef_union_class_decompose hwf hheap hval hlookObj hfindClass hmroEval with hsub1 | hsub2
    · obtain ⟨_, hm⟩ := typed_method_exists_on_runtime_receiver hwf hfmt1 hsub1 hfindClass hmroEval
      simp [hmethodNotFound] at hm
    · obtain ⟨_, hm⟩ := typed_method_exists_on_runtime_receiver hwf hfmt2 hsub2 hfindClass hmroEval
      simp [hmethodNotFound] at hm
  | interIntro _ _ hwfIn1 hwfIn2 ih1 _ =>
    exact ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) hlookObj hfindClass hmroEval hmethodNotFound hfeq
  | sub _ _ ih => exact ih hval hlookObj hfindClass hmroEval hmethodNotFound hfeq
  | _ => exact Frame.noConfusion hfeq

/-- Preserve the required input and declared function-type evidence while the argument evaluates. -/
private theorem returnCallCallee_helper
    (hwf : WellTypedClassHierarchy ct) (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.callCallee arg))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap (Value.objRef calleeOid) T)
    (hlookCallee : heap.lookup calleeOid = some ⟨calleeClassName, .boundMethod recvOid m⟩)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy heap env Γ) :
    ∃ requiredInput, HasType hwf.toWellFormedClassHierarchy midΓ arg requiredInput ∧
      FrameHasType hwf.toWellFormedClassHierarchy heap midΓ requiredInput midΓ midTy (.awaitArgument recvOid m) ∧
      EnvHasType hwf.toWellFormedClassHierarchy heap env midΓ := by
  generalize hfeq : Frame.callCallee arg = f at hframe
  induction hframe generalizing hlookCallee with
  | callCallee harg hsub =>
    cases hfeq
    obtain ⟨_, _, _, hlookBM, hlookRecv, hprov, hsubCallable⟩ :=
      objRef_callable_provenance hwf hheap hval
    obtain ⟨_, hrec, hmethod⟩ := unify_payload hlookBM hlookCallee
    subst hrec; subst hmethod
    have hwfInput := hasType_wellFormed hwf (envHasType_wellFormedTyEnv hwf hheap henv) harg
    exact ⟨_, harg, .awaitArgument hlookRecv hprov
      (.trans hsubCallable (.callable (.refl hwfInput) hsub)), henv⟩
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨Q1, harg1, pending1, henv1⟩ := ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) hlookCallee henv hfeq
    obtain ⟨Q2, harg2, pending2, _⟩ := ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1)) hlookCallee henv hfeq
    exact ⟨.intersection Q1 Q2, .interIntro harg1 harg2,
      .interIntro pending1 pending2
        (hasType_wellFormed hwf (envHasType_wellFormedTyEnv hwf hheap henv1) harg1)
        (hasType_wellFormed hwf (envHasType_wellFormedTyEnv hwf hheap henv1) harg2), henv1⟩
  | sub _ hsub ih =>
    obtain ⟨Q, harg, pending, henv⟩ := ih hval hlookCallee henv hfeq
    exact ⟨Q, harg, .sub pending hsub, henv⟩
  | _ => exact Frame.noConfusion hfeq

/-- returnCallNotInvokable: contradiction — callable must be bound method. -/
private theorem returnCallNotInvokable_helper
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.callCallee arg))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap (Value.objRef calleeOid) T)
    (hlookCallee : heap.lookup calleeOid = some ⟨calleeClassName, ObjectPayload.ordinary⟩) : False := by
  generalize hfeq : Frame.callCallee arg = f at hframe
  induction hframe generalizing hlookCallee with
  | callCallee _ _ =>
    cases hfeq
    obtain ⟨_, _, _, _, heq, hlookBM, _, _⟩ := canonical_callable hwf hheap hval
    simp at heq; subst heq
    exact payload_absurd hlookBM hlookCallee
  | interIntro _ _ hwfIn1 hwfIn2 ih1 _ =>
    exact ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) hlookCallee hfeq
  | sub _ _ ih => exact ih hval hlookCallee hfeq
  | _ => exact Frame.noConfusion hfeq

/-- returnAwaitArgument: construct body env and typing, push returnTo frame. -/
private theorem returnAwaitArgument_helper
    (hwf : WellTypedClassHierarchy ct) (hheap : HeapWellFormed ct heap)
    (hframe : FrameHasType hwf.toWellFormedClassHierarchy heap Γ T midΓ midTy (Frame.awaitArgument recvOid m))
    (hval : ValueHasType hwf.toWellFormedClassHierarchy heap argVal T)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy heap env Γ) :
    (∃ bodyΓ,
      EnvHasType hwf.toWellFormedClassHierarchy heap [(m.param, argVal), (m.receiverParam, Value.objRef recvOid)] bodyΓ ∧
      HasType hwf.toWellFormedClassHierarchy bodyΓ m.body m.returnTy) ∧
    IsSubtype hwf.toWellFormedClassHierarchy m.returnTy midTy ∧
    EnvHasType hwf.toWellFormedClassHierarchy heap env midΓ := by
  generalize hfeq : Frame.awaitArgument recvOid m = f at hframe
  induction hframe with
  | awaitArgument hlookRecv hprov hsub =>
    cases hfeq
    obtain ⟨_, _, hfindRecv, hmroRecv, hmethodRecv⟩ := hprov
    obtain ⟨dname, d, hdmem, hfindd, hmethods⟩ := findMethodInMro_provenance hmethodRecv
    have hbodyType := hwf.allMethodsWellTyped dname d m hfindd hmethods
    have hsubParam := callable_domain_subtype hsub
    have hvalParam := ValueHasType.sub hval hsubParam
    refine ⟨⟨_, ?_, hbodyType⟩,
      callable_return_subtype hsub (valueHasType_nonempty hwf hheap hval), henv⟩
    intro y Ty hlookBody
    by_cases hyParam : y = m.param
    · subst hyParam
      simp [NamedEnv.lookup] at hlookBody
      cases hlookBody
      exact ⟨_, by simp [NamedEnv.lookup], hvalParam⟩
    · have hparamy : m.param ≠ y := by
        intro hEq
        exact hyParam hEq.symm
      by_cases hyRecv : y = m.receiverParam
      · subst hyRecv
        have hlookRecvBody : NamedEnv.lookup [(m.receiverParam, _root_.Ty.class_ dname)]
            m.receiverParam = some Ty := by
          simpa [NamedEnv.lookup, hparamy] using hlookBody
        simp [NamedEnv.lookup] at hlookRecvBody
        cases hlookRecvBody
        refine ⟨_, ?_, .objRef hlookRecv (.class_ hfindRecv hmroRecv hdmem)⟩
        simp [NamedEnv.lookup, hparamy]
      · have hrecvy : m.receiverParam ≠ y := by
          intro hEq
          exact hyRecv hEq.symm
        have : False := by
          simp [NamedEnv.lookup, hparamy, hrecvy] at hlookBody
        exact False.elim this
  | interIntro _ _ hwfIn1 hwfIn2 ih1 ih2 =>
    obtain ⟨⟨bodyΓ1, henvBody1, hbody1⟩, hsub1, henvMid1⟩ :=
      ih1 (.sub hval (.interLeft (.refl hwfIn1) hwfIn2)) henv hfeq
    obtain ⟨_, hsub2, _⟩ :=
      ih2 (.sub hval (.interRight (.refl hwfIn2) hwfIn1)) henv hfeq
    exact ⟨⟨bodyΓ1, henvBody1, hbody1⟩, .interIntro hsub1 hsub2, henvMid1⟩
  | sub _ hsub ih =>
    obtain ⟨hbody, hsub', henvMid⟩ := ih hval henv hfeq
    exact ⟨hbody, .trans hsub' hsub, henvMid⟩
  | _ => exact Frame.noConfusion hfeq

/-! ## One-step preservation -/

/-- One-step preservation: if a safe state takes a step, the result is safe. -/
theorem preservation
    (hwf : WellTypedClassHierarchy ct)
    (hsafe : StateSafe hwf.toWellFormedClassHierarchy heap env ctrl cont expectedType)
    (hstep : Step ct { heap, env, control := ctrl, continuation := cont }
                     { heap := heap', env := env', control := ctrl', continuation := cont' }) :
    StateSafe hwf.toWellFormedClassHierarchy heap' env' ctrl' cont' expectedType := by
  obtain ⟨Γ, outΓ, T, hheap, henv, hctrl, hcont⟩ := hsafe
  cases hstep with
  -- Focus rules: push a frame, control becomes a subexpression
  | focusAttrAccess =>
    cases hctrl with
    | expr hty =>
      have hΓwf := envHasType_wellFormedTyEnv hwf hheap henv
      obtain ⟨Tbase, hbase, hframe⟩ := attrAccess_frame_of_type hwf hΓwf hty
      exact ⟨Γ, outΓ, Tbase, hheap, henv, .expr hbase, .cons hframe hcont⟩
  | focusCall =>
    cases hctrl with
    | expr hty =>
      have hΓwf := envHasType_wellFormedTyEnv hwf hheap henv
      obtain ⟨calleeTy, hcallee, hframe⟩ := call_frame_of_type hwf hΓwf hty
      exact ⟨Γ, outΓ, calleeTy, hheap, henv, ControlHasType.expr hcallee, ContinuationHasType.cons hframe hcont⟩
  | focusCond hne =>
    cases hctrl with
    | expr hty =>
      have hΓwf := envHasType_wellFormedTyEnv hwf hheap henv
      obtain ⟨Tcond, hcondExpr, hframe⟩ := cond_frame_of_type hwf hΓwf hty hne
      exact ⟨Γ, outΓ, Tcond, hheap, henv, .expr hcondExpr, .cons hframe hcont⟩
  -- Direct condIsInstance steps
  | condIsInstanceTrue henvLook hlookObj hfindClass hmroEval hmem =>
    cases hctrl with
    | expr hty =>
      have hΓwf := envHasType_wellFormedTyEnv hwf hheap henv
      obtain ⟨_, _, hlookΓ, hfindCls⟩ := has_type_cond_isInstance_inv hty
      have hwfS := hΓwf _ _ hlookΓ
      have hwfC := WellFormedTy.class_of_lookup hfindCls
      -- Type thenBr at narrowed env
      have hthen := condIsInstanceTrue_typing hwf hΓwf hty hlookΓ hfindCls
      -- Narrow the runtime env
      have henv' := env_has_type_narrow henv hlookΓ (fun v hv => by
        have := Option.some.inj (hv.symm.trans henvLook); subst this
        obtain ⟨_, hv', hvt⟩ := henv _ _ hlookΓ
        have := Option.some.inj (hv'.symm.trans henvLook); subst this
        exact .interIntro hvt
          (.objRef hlookObj (.class_ hfindClass hmroEval hmem)) (.intersection hwfS hwfC))
      -- Strengthen the continuation
      obtain ⟨outΓ', hcont'⟩ := continuationHasType_strengthen_var hcont
        hlookΓ (.interLeft (.refl hwfS) hwfC)
      exact ⟨_, outΓ', T, hheap, henv', .expr hthen, hcont'⟩
  | condIsInstanceFalse henvLook hlookObj hfindClass hmroEval hnotmem =>
    cases hctrl with
    | expr hty =>
      have hΓwf := envHasType_wellFormedTyEnv hwf hheap henv
      obtain ⟨_, _, hlookΓ, hfindCls⟩ := has_type_cond_isInstance_inv hty
      have hwfS := hΓwf _ _ hlookΓ
      have hwfNegC := WellFormedTy.negClass_of_lookup hfindCls
      -- Type elseBr at narrowed env
      have helse := condIsInstanceFalse_typing hwf hΓwf hty hlookΓ hfindCls
      -- Narrow the runtime env
      have henv' := env_has_type_narrow henv hlookΓ (fun v hv => by
        have := Option.some.inj (hv.symm.trans henvLook); subst this
        obtain ⟨_, hv', hvt⟩ := henv _ _ hlookΓ
        have := Option.some.inj (hv'.symm.trans henvLook); subst this
        exact .interIntro hvt
          (.objRefNegClass hlookObj hwfNegC hfindClass hmroEval hnotmem) (.intersection hwfS hwfNegC))
      -- Strengthen the continuation
      obtain ⟨outΓ', hcont'⟩ := continuationHasType_strengthen_var hcont
        hlookΓ (.interLeft (.refl hwfS) hwfNegC)
      exact ⟨_, outΓ', T, hheap, henv', .expr helse, hcont'⟩
  | condIsInstanceVarNotFound henvLook =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, _, hlookΓ, _⟩ := has_type_cond_isInstance_inv hty
      obtain ⟨_, henvLookV, _⟩ := henv _ _ hlookΓ
      exact absurd (henvLook.symm.trans henvLookV) (by simp)
  -- Variable lookup
  | varSuccess hlook =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, hlookΓ, hsub⟩ := has_type_var_inv hty (envHasType_wellFormedTyEnv hwf hheap henv)
      obtain ⟨_, henvLook, hval⟩ := henv _ _ hlookΓ
      have := Option.some.inj (henvLook.symm.trans hlook); subst this
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub hval hsub),
        hcont⟩
  | varError hlook =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, hlookΓ, _⟩ := has_type_var_inv hty (envHasType_wellFormedTyEnv hwf hheap henv)
      obtain ⟨_, henvLook, _⟩ := henv _ _ hlookΓ
      exact absurd (hlook.symm.trans henvLook) (by simp)
  -- New object
  | newSuccess hfind hne1 hne2 hne3 halloc =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, _, _, _, _, hsub⟩ := has_type_new_inv hty
      have hmono : ∀ {oid obj}, heap.lookup oid = some obj → heap'.lookup oid = some obj :=
        fun hlk => heap_alloc_preserves_old hheap.idsBounded halloc hlk
      have hheap' : HeapWellFormed ct heap' :=
        step_preserves_heapWellFormed
          (s := { heap, env, control := .expr (.new _), continuation := cont })
          (Step.newSuccess hfind hne1 hne2 hne3 halloc) hheap hwf
      have hlookNew := heap_alloc_lookup_new halloc
      exact ⟨Γ, outΓ, T, hheap',
        env_has_type_mono henv hmono,
        .val (.sub (.objRef hlookNew (.refl hsub.sourceWellFormed)) hsub),
        continuationHasType_mono hcont hmono⟩
  | newClassNotFound hfind =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, hfind', _, _, _, _⟩ := has_type_new_inv hty
      exact absurd (hfind.symm.trans hfind') (by simp)
  | newBuiltinError _ hbuiltin =>
    cases hctrl with
    | expr hty =>
      obtain ⟨_, _, hne1, hne2, hne3, _⟩ := has_type_new_inv hty
      rcases hbuiltin with rfl | rfl | rfl
      · exact absurd rfl hne1
      · exact absurd rfl hne2
      · exact absurd rfl hne3
  -- Constants
  | constNone =>
    cases hctrl with
    | expr hty =>
      have hsub := has_type_constNone_inv hty
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub (.objRef hheap.initialNone (.refl (WellFormedTy.none hwf.toWellFormedClassHierarchy))) hsub),
        hcont⟩
  | constTrue =>
    cases hctrl with
    | expr hty =>
      have hsub := has_type_constTrue_inv hty
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub (.objRef hheap.initialTrue (.refl (WellFormedTy.bool hwf.toWellFormedClassHierarchy))) hsub),
        hcont⟩
  | constFalse =>
    cases hctrl with
    | expr hty =>
      have hsub := has_type_constFalse_inv hty
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub (.objRef hheap.initialFalse (.refl (WellFormedTy.bool hwf.toWellFormedClassHierarchy))) hsub),
        hcont⟩
  -- isInstance
  | isInstanceTrue =>
    cases hctrl with
    | expr hty =>
      have hsub := (has_type_isInstance_inv hty).2.2
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub (.objRef hheap.initialTrue (.refl (WellFormedTy.bool hwf.toWellFormedClassHierarchy))) hsub),
        hcont⟩
  | isInstanceFalse =>
    cases hctrl with
    | expr hty =>
      have hsub := (has_type_isInstance_inv hty).2.2
      exact ⟨Γ, outΓ, T, hheap, henv,
        .val (.sub (.objRef hheap.initialFalse (.refl (WellFormedTy.bool hwf.toWellFormedClassHierarchy))) hsub),
        hcont⟩
  | isInstanceVarNotFound henvLook =>
    cases hctrl with
    | expr hty =>
      obtain ⟨⟨_, hlookΓ⟩, _, _⟩ := has_type_isInstance_inv hty
      obtain ⟨_, henvLookV, _⟩ := henv _ _ hlookΓ
      exact absurd (henvLook.symm.trans henvLookV) (by simp)
  -- Return rules
  | returnAttrAccess hlookObj hfindClass hmroEval hmethodEval halloc =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨hval', henv', hheap'⟩ := returnAttrAccess_helper hwf hheap hframe hval
          hlookObj hfindClass hmroEval hmethodEval halloc henv
        exact ⟨_, _, _, hheap', henv', .val hval',
          continuationHasType_mono hrest
            (fun hlk => heap_alloc_preserves_old hheap.idsBounded halloc hlk)⟩
  | returnAttrAccessNotFound hlookObj hfindClass hmroEval hmethodNotFound =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        exact absurd (returnAttrAccessNotFound_helper hwf hheap hframe hval
          hlookObj hfindClass hmroEval hmethodNotFound) id
  | returnCallCallee hlookCallee =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨_, harg, pending, henvMid⟩ :=
          returnCallCallee_helper hwf hheap hframe hval hlookCallee henv
        exact ⟨_, _, _, hheap, henvMid, .expr harg,
          .cons pending hrest⟩
  | returnCallNotInvokable hlookCallee =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        exact absurd (returnCallNotInvokable_helper hwf hheap hframe hval hlookCallee) id
  | returnAwaitArgument =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨⟨bodyΓ, henvBody, hbodyType⟩, hsubRet, henvMid⟩ :=
          returnAwaitArgument_helper hwf hheap hframe hval henv
        exact ⟨bodyΓ, _, _, hheap, henvBody, .expr hbodyType,
          .cons (.sub (.returnTo henvMid) hsubRet) hrest⟩
  | returnCondTrue =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨hthen, henvMid⟩ := returnCondTrue_helper hframe hval henv
        exact ⟨_, _, _, hheap, henvMid, .expr hthen, hrest⟩
  | returnCondFalse =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨helse, henvMid⟩ := returnCondFalse_helper hframe hval henv
        exact ⟨_, _, _, hheap, henvMid, .expr helse, hrest⟩
  | returnCondNotBool hneTrue hneFalse =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        exact absurd (returnCondNotBool_helper hwf hheap hframe hval hneTrue hneFalse) id
  | returnFromBody =>
    cases hctrl with
    | val hval =>
      cases hcont with
      | cons hframe hrest =>
        obtain ⟨hval', henvCaller⟩ := returnFromBody_helper hwf hheap hframe hval
        exact ⟨_, _, _, hheap, henvCaller, .val hval', hrest⟩
  -- Error unwind rules: ctrl is .error, which has no ControlHasType constructor
  | errorUnwindAttrAccess =>
    cases hctrl
  | errorUnwindCallCallee =>
    cases hctrl
  | errorUnwindAwaitArgument =>
    cases hctrl
  | errorUnwindCond =>
    cases hctrl
  | errorUnwindReturnTo =>
    cases hctrl

private theorem preservation_steps
    (hwf : WellTypedClassHierarchy ct)
    (hsafe : StateSafe hwf.toWellFormedClassHierarchy s.heap s.env s.control s.continuation expectedType)
    (hsteps : Steps ct s s') :
    StateSafe hwf.toWellFormedClassHierarchy s'.heap s'.env s'.control s'.continuation expectedType := by
  induction hsteps with
  | refl => exact hsafe
  | step hs _ ih => exact ih (preservation hwf hsafe hs)

/-- Multi-step preservation. -/
theorem preservation_multi
    (hwf : WellTypedClassHierarchy ct)
    (hsafe : StateSafe hwf.toWellFormedClassHierarchy heap env ctrl cont expectedType)
    (hsteps : Steps ct { heap, env, control := ctrl, continuation := cont }
                       { heap := heap', env := env', control := ctrl', continuation := cont' }) :
    StateSafe hwf.toWellFormedClassHierarchy heap' env' ctrl' cont' expectedType :=
  preservation_steps hwf hsafe hsteps

end SmallStep

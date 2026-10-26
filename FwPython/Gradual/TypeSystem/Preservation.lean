import FwPython.Gradual.TypeSystem.Safety
import FwPython.Gradual.TypeSystem.EnforcementClassification
import FwPython.Gradual.TypeSystem.IsInstanceRefinement
import FwPython.Gradual.Checked.Enforce
import FwPython.Gradual.Checked.HeapPreservation

/-! ## Preservation for checked safe states

One-step and multi-step preservation: stepping from a safe checked state
produces a safe checked state. Blame is a valid safe control (it
propagates through frames without issue). Runtime errors have no
`CheckedControlHasType` constructor and are ruled out by contradiction. -/

variable {gct : GClassTable} {structural : WellFormedClassHierarchy (eraseClassTable gct)}

namespace Checked

/-! ### Heap monotonicity for typing judgments

When the heap is extended by allocation, existing typing judgments are
preserved because existing heap lookups remain valid. -/

/-- Heap monotonicity for `CheckedCallableView`. -/
theorem checkedCallableView_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hview : CheckedCallableView gct cct heap v) :
    CheckedCallableView gct cct heap' v :=
  match hview with
  | .objRefBoundMethod hlook hrecv hmro => .objRefBoundMethod (hmono _ _ hlook) (hmono _ _ hrecv) hmro

/-- Heap monotonicity for CheckedAnyShape. -/
theorem checkedAnyShape_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hshape : CheckedAnyShape gct cct heap v) :
    CheckedAnyShape gct cct heap' v :=
  match hshape with
  | .objRef hlook => .objRef (hmono _ _ hlook)

/-- Heap monotonicity for CheckedClassView. -/
theorem checkedClassView_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hview : CheckedClassView gct cct heap v cname) :
    CheckedClassView gct cct heap' v cname :=
  match hview with
  | .objRef hlook hfind hmro hmem => .objRef (hmono _ _ hlook) hfind hmro hmem

/-- Witness heap monotonicity. -/
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
  | .mk hwf (.negClass hshape hblame) =>
    .mk hwf (.negClass (checkedAnyShape_heapMono hmono hshape)
      (enforceValue_heapMono hmono hblame))

/-! ### Frame environment preservation lemmas

For frames that do not switch environments (all frames except `returnTo`),
the output type-environment equals the input
type-environment.

For `returnTo`, the output type-environment carries the stored caller
environment typing.

We prove these by case analysis on the derivation. -/

/-- Helper: for frames whose base constructors always have `midΓ = inΓ`,
    prove `Γ' = Γ` by case analysis. -/
private theorem frameHasType_env_eq_attrAccess
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a, f = .attrAccess a) : Γ' = Γ := by
  induction hf with
  | attrAccess _ | attrAccessUnion _ _ => rfl
  | _ => obtain ⟨_, h⟩ := hframe; cases h

private theorem frameHasType_env_eq_callCallee
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a p r obligation, f = .callCallee a p r obligation) : Γ' = Γ := by
  induction hf with
  | callCallee _ _ _ _ _ _ => rfl
  | _ => obtain ⟨_, _, _, _, h⟩ := hframe; cases h

private theorem frameHasType_env_eq_awaitArgument
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a b r obligation, f = .awaitArgument a b r obligation) : Γ' = Γ := by
  induction hf with
  | awaitArgument _ _ _ _ _ _ _ _ => rfl
  | _ => obtain ⟨_, _, _, _, h⟩ := hframe; cases h

private theorem frameHasType_env_eq_cond
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a b, f = .cond a b) : Γ' = Γ := by
  induction hf with
  | cond _ _ => rfl
  | _ => obtain ⟨_, _, h⟩ := hframe; cases h

private theorem frameHasType_env_eq_enforce
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a b, f = .enforce a b) : Γ' = Γ := by
  induction hf with
  | enforce _ _ => rfl
  | _ => obtain ⟨_, _, h⟩ := hframe; cases h

private theorem frameHasType_env_eq_dynAttrAccess
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : ∃ a b, f = .dynAttrAccess a b) : Γ' = Γ := by
  induction hf with
  | dynAttrAccess => rfl
  | _ => obtain ⟨_, _, h⟩ := hframe; cases h

/-- Extract caller-env typing from a `returnTo` frame. -/
private theorem frameHasType_returnTo_callerEnv
    (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : f = .returnTo callerEnv) :
    CheckedEnvHasType gct cct heap callerEnv Γ' := by
  induction hf with
  | returnTo henvCaller => exact Frame.returnTo.inj hframe ▸ henvCaller
  | _ => exact absurd hframe nofun

/-! ### Expression-to-value typing transfer

When an atomic expression evaluates to a value, we transfer the expression
typing derivation to a value witness derivation. -/

/-- If `.constNone` has type `G`, the noneOid object reference has value witness `G`. -/
private theorem constNone_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .constNone)
    (hheap : CheckedHeapWellFormed gct cct heap) :
    CheckedValueWitness gct cct heap (.objRef noneOid) G := by
  cases hty with
  | constNone =>
    obtain ⟨c, mro, hfc, hmro⟩ := hheap.classesExist _ _ hheap.initialNone
    have : findGClass gct noneClass = some c := hfc
    exact .mk (.class_ this hmro)
      (.class_ (.objRef hheap.initialNone this hmro
        (by simpa [findGClass_name this] using mro_self_mem hmro)))
  | _ => exact absurd he nofun

/-- If `.constTrue` has type `G`, the trueOid object reference has value witness `G`. -/
private theorem constTrue_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .constTrue)
    (hheap : CheckedHeapWellFormed gct cct heap) :
    CheckedValueWitness gct cct heap (.objRef trueOid) G := by
  cases hty with
  | constTrue =>
    obtain ⟨c, mro, hfc, hmro⟩ := hheap.classesExist _ _ hheap.initialTrue
    have : findGClass gct boolClass = some c := hfc
    exact .mk (.class_ this hmro)
      (.class_ (.objRef hheap.initialTrue this hmro
        (by simpa [findGClass_name this] using mro_self_mem hmro)))
  | _ => exact absurd he nofun

/-- If `.constFalse` has type `G`, the falseOid object reference has value witness `G`. -/
private theorem constFalse_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .constFalse)
    (hheap : CheckedHeapWellFormed gct cct heap) :
    CheckedValueWitness gct cct heap (.objRef falseOid) G := by
  cases hty with
  | constFalse =>
    obtain ⟨c, mro, hfc, hmro⟩ := hheap.classesExist _ _ hheap.initialFalse
    have : findGClass gct boolClass = some c := hfc
    exact .mk (.class_ this hmro)
      (.class_ (.objRef hheap.initialFalse this hmro
        (by simpa [findGClass_name this] using mro_self_mem hmro)))
  | _ => exact absurd he nofun

/-- If `.var x` has type `G` and `env.lookup x = some v`, then `v` has value witness `G`. -/
private theorem var_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .var x)
    (henv : CheckedEnvHasType gct cct heap env Γ)
    (hlookup : env.lookup x = some v) :
    CheckedValueWitness gct cct heap v G := by
  cases hty with
  | var hlook =>
    obtain rfl := CheckedExpr.var.inj he
    obtain ⟨v', hv', hvty⟩ := henv _ _ hlook
    cases hlookup.symm.trans hv'
    exact hvty
  | _ => exact absurd he nofun

/-- If `.new cname` has type `G` and the allocation produces `(oid, heap')`,
    then `objRef oid` has value witness `G` in the extended heap. -/
private theorem new_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .new cname)
    {heap : CheckedHeap}
    (hwfct : WellFormedGClassTableCore gct)
    (halloc : heap.alloc ⟨cname, .ordinary⟩ = (oid, heap')) :
    CheckedValueWitness gct cct heap' (.objRef oid) G := by
  cases hty with
  | new hfind _ _ _ =>
    obtain rfl := CheckedExpr.new.inj he
    have hlook := checkedHeap_alloc_lookup_new halloc
    let hmro := (hwfct.raw.allMrosExist _ _ hfind).hmro
    exact .mk (.class_ hfind hmro)
      (.class_ (.objRef hlook hfind hmro
        (by simpa [findGClass_name hfind] using mro_self_mem hmro)))
  | _ => exact absurd he nofun

/-- If `.isInstance x C` has type `G`, then the boolean result value has witness `G`. -/
private theorem isInstance_val_of_expr
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .isInstance x C)
    (hheap : CheckedHeapWellFormed gct cct heap)
    (result : CheckedValue) (hresult : result = .objRef trueOid ∨ result = .objRef falseOid) :
    CheckedValueWitness gct cct heap result G := by
  cases hty with
  | isInstance _ _ =>
    cases hresult with
    | inl hr =>
      subst hr
      obtain ⟨c, mro, hfc, hmro⟩ := hheap.classesExist _ _ hheap.initialTrue
      have : findGClass gct boolClass = some c := hfc
      exact .mk (.class_ this hmro)
        (.class_ (.objRef hheap.initialTrue this hmro
          (by simpa [findGClass_name this] using mro_self_mem hmro)))
    | inr hr =>
      subst hr
      obtain ⟨c, mro, hfc, hmro⟩ := hheap.classesExist _ _ hheap.initialFalse
      have : findGClass gct boolClass = some c := hfc
      exact .mk (.class_ this hmro)
        (.class_ (.objRef hheap.initialFalse this hmro
          (by simpa [findGClass_name this] using mro_self_mem hmro)))
  | _ => exact absurd he nofun

/-! ### Expression typing contradiction lemmas

When a well-typed expression would produce a runtime error at
evaluation time, the evaluation condition is contradictory. -/

/-- A well-typed variable lookup implies the variable is in the runtime env. -/
private theorem var_lookup_ne_none
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .var x)
    (henv : CheckedEnvHasType gct cct heap env Γ) :
    env.lookup x ≠ none := by
  induction hty with
  | var hlook =>
    obtain rfl := CheckedExpr.var.inj he
    obtain ⟨v, hv, _⟩ := henv _ _ hlook
    simp [hv]
  | _ => exact absurd he nofun

/-- A well-typed `new` expression implies the class exists. -/
private theorem new_class_exists
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .new cname) :
    ∃ c, findGClass gct cname = some c := by
  induction hty with
  | new hfind _ _ _ => exact ⟨_, CheckedExpr.new.inj he ▸ hfind⟩
  | _ => exact absurd he nofun

/-- A well-typed `new` expression implies the class is not a builtin. -/
private theorem new_not_builtin
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .new cname) :
    cname ≠ boolClass ∧ cname ≠ noneClass ∧ cname ≠ boundMethodClass := by
  induction hty with
  | new _ hne_bool hne_none hne_bm => exact CheckedExpr.new.inj he ▸ ⟨hne_bool, hne_none, hne_bm⟩
  | _ => exact absurd he nofun

/-- A well-typed `isInstance` implies the variable is in the type env. -/
private theorem isInstance_var_exists
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G) (he : e = .isInstance x C)
    (henv : CheckedEnvHasType gct cct heap env Γ) :
    env.lookup x ≠ none := by
  induction hty with
  | isInstance hlook _ =>
    obtain ⟨rfl, _⟩ := CheckedExpr.isInstance.inj he
    obtain ⟨v, hv, _⟩ := henv _ _ hlook
    simp [hv]
  | _ => exact absurd he nofun

/-- A well-typed `cond (isInstance x C)` implies the variable is in the runtime env. -/
private theorem condIsInstance_var_exists
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .cond (.isInstance x C) thenBr elseBr)
    (henv : CheckedEnvHasType gct cct heap env Γ) :
    env.lookup x ≠ none := by
  induction hty with
  | condIsInstance hlook _ _ _ _ _ _ _ _ =>
    obtain ⟨v, hv, _⟩ := henv _ _ ((CheckedExpr.isInstance.inj (CheckedExpr.cond.inj he).1).1 ▸ hlook)
    simp [hv]
  | cond hty_cond _ _ _ _ _ =>
    exact isInstance_var_exists hty_cond (CheckedExpr.cond.inj he).1 henv
  | _ => exact absurd he nofun

/-! ### Focus decomposition lemmas

Decompose an expression typing `CheckedHasType gct structural Γ (compound subexpr ...) G`
into a subexpression typing + a frame typing. -/

/-- Decompose `.attrAccess base attrName` into base typing + attrAccess frame. -/
private theorem focus_attrAccess
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .attrAccess base attrName) (cct : CheckedClassTable) (heap : CheckedHeap) :
    ∃ G₁, CheckedHasType gct structural Γ base G₁ ∧
      CheckedFrameHasType gct structural cct heap Γ G₁ Γ G (.attrAccess attrName) := by
  cases hty with
  | attrAccess hbase hfind =>
    obtain ⟨rfl, rfl⟩ := CheckedExpr.attrAccess.inj he
    exact ⟨_, hbase, .attrAccess hfind⟩
  | attrAccessUnion hbase hfind1 hfind2 =>
    obtain ⟨rfl, rfl⟩ := CheckedExpr.attrAccess.inj he
    exact ⟨_, hbase, .attrAccessUnion hfind1 hfind2⟩
  | _ => exact absurd he nofun

/-- Decompose `.call callee arg paramTy returnTy returnObligation` into callee typing + callCallee frame. -/
private theorem focus_call
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .call callee arg paramTy returnTy returnObligation)
    (cct : CheckedClassTable) (heap : CheckedHeap) :
    ∃ G₁, CheckedHasType gct structural Γ callee G₁ ∧
      CheckedFrameHasType gct structural cct heap Γ G₁ Γ G
        (.callCallee arg paramTy returnTy returnObligation) := by
  cases hty with
  | call hcallee harg hassign htP htR hwfP hwfR =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := CheckedExpr.call.inj he
    exact ⟨_, hcallee, .callCallee harg hassign htP htR hwfP hwfR⟩
  | _ => exact absurd he nofun

/-- Decompose `.cond condExpr thenBr elseBr` (non-isInstance) into condExpr typing + cond frame. -/
private theorem focus_cond
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .cond condExpr thenBr elseBr)
    (hne : ∀ x C, condExpr ≠ .isInstance x C) (cct : CheckedClassTable) (heap : CheckedHeap) :
    ∃ G₁, CheckedHasType gct structural Γ condExpr G₁ ∧
      CheckedFrameHasType gct structural cct heap Γ G₁ Γ G (.cond thenBr elseBr) := by
  cases hty with
  | cond hcond hthen helse _htgt =>
    obtain ⟨rfl, rfl, rfl⟩ := CheckedExpr.cond.inj he
    exact ⟨_, hcond, .cond hthen helse⟩
  | condIsInstance hlook hfind _ _ _ _ _ =>
    obtain ⟨hcond_eq, _, _⟩ := CheckedExpr.cond.inj he
    exact absurd hcond_eq.symm (hne _ _)
  | _ => exact absurd he nofun

/-- Decompose `.enforce e c ℓ` into inner typing + enforce frame. -/
private theorem focus_enforce
    {e' : CheckedExpr} (hty : CheckedHasType gct structural Γ e' G)
    (he : e' = .enforce e c ℓ) (cct : CheckedClassTable) (heap : CheckedHeap) :
    ∃ G₁, CheckedHasType gct structural Γ e G₁ ∧
      CheckedFrameHasType gct structural cct heap Γ G₁ Γ G (.enforce c ℓ) := by
  cases hty with
  | enforce hinner hwf htgt =>
    obtain ⟨rfl, rfl, rfl⟩ := CheckedExpr.enforce.inj he
    exact ⟨_, hinner, .enforce hwf htgt⟩
  | _ => exact absurd he nofun

/-- Decompose `.dynAttrAccess base attrName ℓ` into base typing + dynAttrAccess frame. -/
private theorem focus_dynAttrAccess
    {e : CheckedExpr} (hty : CheckedHasType gct structural Γ e G)
    (he : e = .dynAttrAccess base attrName ℓ) (cct : CheckedClassTable) (heap : CheckedHeap) :
    ∃ G₁, CheckedHasType gct structural Γ base G₁ ∧
      CheckedFrameHasType gct structural cct heap Γ G₁ Γ G (.dynAttrAccess attrName ℓ) := by
  cases hty with
  | dynAttrAccess hbase =>
    obtain ⟨rfl, rfl, rfl⟩ := CheckedExpr.dynAttrAccess.inj he
    exact ⟨_, hbase, .dynAttrAccess⟩
  | _ => exact absurd he nofun

/-! ### Frame value transfer lemmas -/

/-- For a returnTo frame, transfer a value at `inTy` to a value at
    the frame's output type in the caller environment. -/
private theorem returnTo_value_transfer
    (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : f = .returnTo callerEnv)
    (w : CheckedValueWitness gct cct heap v inTy) :
    CheckedEnvHasType gct cct heap callerEnv Γ' ∧
    CheckedValueWitness gct cct heap v outTy := by
  induction hf with
  | returnTo henvCaller =>
    obtain rfl := Frame.returnTo.inj hframe
    exact ⟨henvCaller, w⟩
  | _ => exact absurd hframe nofun

/-- Heap monotonicity for environment typing. -/
private theorem checkedEnvHasType_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (henv : CheckedEnvHasType gct cct heap env Γ) :
    CheckedEnvHasType gct cct heap' env Γ := by
  intro x Gx hlookup
  obtain ⟨v, hv, hvty⟩ := henv x Gx hlookup
  exact ⟨v, hv, checkedValueWitness_heapMono hmono hvty⟩

/-- Updated environment typing with a new witness at a variable. -/
private theorem checkedEnvHasType_updateWitness
    (henv : CheckedEnvHasType gct cct heap env Γ)
    (hlook : Γ.lookup x = some oldG)
    (hlookV : env.lookup x = some v)
    (wNew : CheckedValueWitness gct cct heap v newG) :
    CheckedEnvHasType gct cct heap env (Γ.update x newG) := by
  intro y Gy hlookΓ'
  by_cases hyx : y = x
  · subst hyx
    rw [gTyEnv_update_lookup_eq newG ⟨oldG, hlook⟩] at hlookΓ'
    exact ⟨v, hlookV, Option.some.inj hlookΓ'.symm ▸ wNew⟩
  · rw [gTyEnv_update_lookup_ne newG hyx] at hlookΓ'
    exact henv y Gy hlookΓ'

/-- Frame typing is monotone in the heap. -/
private theorem checkedFrameHasType_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f) :
    CheckedFrameHasType gct structural cct heap' Γ inTy Γ' outTy f := by
  induction hf with
  | attrAccess hfind => exact .attrAccess hfind
  | attrAccessUnion hf1 hf2 => exact .attrAccessUnion hf1 hf2
  | dynAttrAccess => exact .dynAttrAccess
  | callCallee harg hassign htP htR hwfP hwfR =>
    exact .callCallee harg hassign htP htR hwfP hwfR
  | awaitArgument hlook hmro htP htR htReturn hwfP hwfR hwfReturn =>
    exact .awaitArgument (hmono _ _ hlook) hmro htP htR htReturn hwfP hwfR hwfReturn
  | cond hthen helse => exact .cond hthen helse
  | returnTo henvCaller =>
    exact .returnTo (checkedEnvHasType_heapMono hmono henvCaller)
  | enforce hwf htgt => exact .enforce hwf htgt

/-- Continuation typing is monotone in the heap. -/
private theorem checkedContinuationHasType_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (hcont : CheckedContinuationHasType gct structural cct heap Γ G outΓ outTy k) :
    CheckedContinuationHasType gct structural cct heap' Γ G outΓ outTy k := by
  induction hcont with
  | nil => exact .nil
  | cons hf _ ih =>
    exact .cons (checkedFrameHasType_heapMono hmono hf) ih

/-! ### Cond frame inversion

Extract branch typings from a cond frame. -/

/-- From a cond frame, produce a control typing for the then branch. -/
private theorem cond_frame_then_branch
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : f = .cond thenBr elseBr) :
    Γ' = Γ ∧ CheckedControlHasType gct structural cct heap Γ (.expr thenBr) outTy := by
  induction hf with
  | cond hthen _ =>
    obtain ⟨rfl, rfl⟩ := Frame.cond.inj hframe
    exact ⟨rfl, .expr hthen⟩
  | _ => exact absurd hframe nofun

/-- From a cond frame, produce a control typing for the else branch. -/
private theorem cond_frame_else_branch
    {f : Frame} (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : f = .cond thenBr elseBr) :
    Γ' = Γ ∧ CheckedControlHasType gct structural cct heap Γ (.expr elseBr) outTy := by
  induction hf with
  | cond _ helse =>
    obtain ⟨rfl, rfl⟩ := Frame.cond.inj hframe
    exact ⟨rfl, .expr helse⟩
  | _ => exact absurd hframe nofun

/-- From an exact class witness at `class_ boolClass` on an objRef,
    the oid is trueOid or falseOid. -/
private theorem boolClass_objRef_is_true_or_false
    (w : CheckedValueWitness gct cct heap (.objRef oid) (.class_ boolClass))
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct) :
    oid = trueOid ∨ oid = falseOid := by
  cases checkedValueWitness_class_view w with
  | objRef hlook hfind hmro hmem =>
    exact hheap.boolExhaustive oid _ hlook (hwfct.raw.sealedLeaf boolClass (by simp [sealedClasses]) _ _ _ hfind hmro hmem)
/-! ### Frame value transfer functions -/

/-- For an enforce frame, extract environment equality and the enforce target's
    contract, well-formedness, and admissibility. Successful enforcement
    constructs the output witness from the post-enforcement value, so the frame
    exposes exactly the facts needed by that preservation case. -/
private theorem enforce_frame_info
    (hf : CheckedFrameHasType gct structural cct heap Γ inTy Γ' outTy f)
    (hframe : f = .enforce c ℓ) :
    Γ' = Γ ∧ CompilesBoundary outTy (compileBoundaryTarget c) ∧ WellFormedGTy gct outTy ∧
    CheckedTargetTy gct outTy := by
  induction hf with
  | enforce hwf htgt =>
    obtain ⟨rfl, rfl⟩ := Frame.enforce.inj hframe
    exact ⟨rfl, compileBoundaryTarget_eq_compileBoundaryRaw_interp _, hwf, htgt⟩
  | _ => exact absurd hframe nofun

/-! ### Fresh bound-method allocation helpers (Step 6) -/

/-- A freshly allocated bound-method has a class witness at `boundMethodClass`. -/
private theorem allocated_boundMethod_class_witness
    {heap : CheckedHeap} {heap' : CheckedHeap}
    (halloc : heap.alloc ⟨boundMethodClass, .boundMethod recvOid cm⟩ = (bmOid, heap'))
    (hwfct : WellFormedGClassTableCore gct) :
    CheckedValueWitness gct cct heap' (.objRef bmOid) (.class_ boundMethodClass) := by
  have hlook := checkedHeap_alloc_lookup_new halloc
  exact .mk (.class_ hwfct.raw.boundMethodExists.hfind hwfct.raw.boundMethodExists.hmro)
    (.class_ (.objRef hlook hwfct.raw.boundMethodExists.hfind hwfct.raw.boundMethodExists.hmro
      (by simpa [findGClass_name hwfct.raw.boundMethodExists.hfind] using
        mro_self_mem hwfct.raw.boundMethodExists.hmro)))

/-- A freshly allocated objRef has an `any` witness. -/
private theorem allocated_objRef_any_witness
    {heap : CheckedHeap} {heap' : CheckedHeap} {obj : CheckedHeapObject}
    (halloc : heap.alloc obj = (oid, heap')) :
    CheckedValueWitness gct cct heap' (.objRef oid) .any := by
  have hlook := checkedHeap_alloc_lookup_new halloc
  exact .mk .any (.any (.objRef hlook))

/-! ### condIsInstance inversion -/

private theorem checkedValueWitness_isInstanceRefinementBase
    (w : CheckedValueWitness gct cct heap v T)
    (hfacet : isInstanceRefinementBase? T = some U) :
    CheckedValueWitness gct cct heap v U := by
  induction T generalizing U v with
  | any => simp [isInstanceRefinementBase?] at hfacet
  | class_ _ | callable _ _ | bottom | negClass _ =>
      simp [isInstanceRefinementBase?] at hfacet
      cases hfacet; exact w
  | union L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hfacet
      have hbase : isInstanceRefinementBase? (.union L R) = some (.union L' R') := by
        simp [isInstanceRefinementBase?, hL, hR]
      cases hfacet
      cases w with | mk hwf data => cases data with
        | unionLeft wL =>
            exact .mk (wellFormedGTy_isInstanceRefinementBase? hbase hwf)
              (.unionLeft (ihL wL hL))
        | unionRight wR =>
            exact .mk (wellFormedGTy_isInstanceRefinementBase? hbase hwf)
              (.unionRight (ihR wR hR))
  | intersection L R ihL ihR =>
      rcases hL : isInstanceRefinementBase? L with _ | L' <;>
        rcases hR : isInstanceRefinementBase? R with _ | R' <;>
        simp [isInstanceRefinementBase?, hL, hR] at hfacet
      · cases hfacet
        cases w with | mk _ data => cases data with
          | intersection wL wR => exact ihR wR hR
      · cases hfacet
        cases w with | mk _ data => cases data with
          | intersection wL wR => exact ihL wL hL
      · have hbase :
            isInstanceRefinementBase? (.intersection L R) = some (.intersection L' R') := by
          simp [isInstanceRefinementBase?, hL, hR]
        cases hfacet
        cases w with | mk hwf data => cases data with
          | intersection wL wR =>
              exact .mk (wellFormedGTy_isInstanceRefinementBase? hbase hwf)
                (.intersection (ihL wL hL) (ihR wR hR))

private theorem checkedValueWitness_isInstanceRefinementWith
    (w : CheckedValueWitness gct cct heap v T)
    (wExtra : CheckedValueWitness gct cct heap v extra) :
    CheckedValueWitness gct cct heap v (isInstanceRefinementWith T extra) := by
  unfold isInstanceRefinementWith
  cases hfacet : isInstanceRefinementBase? T with
  | none => simpa [hfacet] using wExtra
  | some U =>
      let wBase := checkedValueWitness_isInstanceRefinementBase w hfacet
      exact .mk (.intersection wBase.wf wExtra.wf) (.intersection wBase wExtra)

private theorem checkedValueWitness_isInstanceThenRefinement
    (w : CheckedValueWitness gct cct heap v T)
    (wClass : CheckedValueWitness gct cct heap v (.class_ C)) :
    CheckedValueWitness gct cct heap v (isInstanceThenRefinement T C) :=
  checkedValueWitness_isInstanceRefinementWith w wClass

private theorem checkedValueWitness_isInstanceElseRefinement
    (w : CheckedValueWitness gct cct heap v T)
    (wNeg : CheckedValueWitness gct cct heap v (.negClass C)) :
    CheckedValueWitness gct cct heap v (isInstanceElseRefinement T C) :=
  checkedValueWitness_isInstanceRefinementWith w wNeg

/-- Inversion for cond with isInstance scrutinee: extract branch typings.
    Without sub/interIntro, only `cond` and `condIsInstance` match. -/
private theorem checked_has_type_cond_isInstance_inv
    (hty : CheckedHasType gct structural Γ (.cond (.isInstance x C) thenBr elseBr) G) :
    -- Case 1: ordinary cond — both branches typed under Γ
    (∃ testTy, CheckedHasType gct structural Γ (.isInstance x C) testTy ∧
      CheckedHasType gct structural Γ thenBr G ∧ CheckedHasType gct structural Γ elseBr G) ∨
    -- Case 2: condIsInstance — branches typed under narrowed envs
    (∃ T cls,
      Γ.lookup x = some T ∧
      findGClass gct C = some cls ∧
      CheckedHasType gct structural (Γ.update x (isInstanceThenRefinement T C)) thenBr G ∧
      CheckedHasType gct structural (Γ.update x (isInstanceElseRefinement T C)) elseBr G) := by
  cases hty with
  | cond htest hthen helse _ =>
    exact .inl ⟨_, htest, hthen, helse⟩
  | condIsInstance hlook hfind _ _ _ hthen helse =>
    exact .inr ⟨_, _, hlook, hfind, hthen, helse⟩

/-! ### Main preservation theorem -/

/-- One-step preservation: if a safe checked state takes a step, the
    result is a safe checked state. -/
theorem checked_preservation
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hstep : Step gct cct { heap, env, control := ctrl, continuation := cont }
                      { heap := heap', env := env', control := ctrl', continuation := cont' }) :
    CheckedStateSafe gct cct heap' env' ctrl' cont' expectedType := by
  obtain ⟨Γ, outΓ, G, hwfct, hheap, halign, henv, hctrl, hcont⟩ := hsafe
  -- Heap well-formedness is preserved by all steps
  have hheap' : CheckedHeapWellFormed gct cct heap' :=
    step_preserves_checkedHeapWellFormed hstep hheap hwfct.raw
  -- Heap monotonicity for non-allocating and allocating steps
  have hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj :=
    fun oid obj hlook => step_preserves_heapMonotonicity hstep hheap.idsBounded hlook
  cases hstep with
  -- ═══════════════════════════════════════════════════════════
  -- BLAME UNWIND CASES: blame propagates through any frame
  -- ═══════════════════════════════════════════════════════════
  | blameUnwindAttrAccess =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_attrAccess hf ⟨_, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  | blameUnwindCallCallee =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_callCallee hf ⟨_, _, _, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  | blameUnwindAwaitArgument =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_awaitArgument hf ⟨_, _, _, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  | blameUnwindCond =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_cond hf ⟨_, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  | blameUnwindReturnTo =>
    cases hcont with | cons hf hk =>
    exact ⟨_, _, _, hwfct, hheap', halign,
      frameHasType_returnTo_callerEnv hf rfl, .blame, hk⟩
  | blameUnwindEnforce =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_enforce hf ⟨_, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  | blameUnwindDynAttrAccess =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_dynAttrAccess hf ⟨_, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  -- ═══════════════════════════════════════════════════════════
  -- ERROR UNWIND CASES: contradiction (no CheckedControlHasType for runtimeError)
  -- ═══════════════════════════════════════════════════════════
  | errorUnwindAttrAccess | errorUnwindCallCallee | errorUnwindAwaitArgument
  | errorUnwindCond | errorUnwindReturnTo
  | errorUnwindEnforce | errorUnwindDynAttrAccess => cases hctrl
  -- ═══════════════════════════════════════════════════════════
  -- FOCUS CASES: decompose compound expression, push frame
  -- ═══════════════════════════════════════════════════════════
  | focusAttrAccess =>
    cases hctrl with | expr hty =>
    obtain ⟨G₁, hbase, hframe⟩ := focus_attrAccess hty rfl cct heap
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hbase, .cons hframe hcont⟩
  | focusCall =>
    cases hctrl with | expr hty =>
    obtain ⟨G₁, hcallee, hframe⟩ := focus_call hty rfl cct heap
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hcallee, .cons hframe hcont⟩
  | focusCond hne =>
    cases hctrl with | expr hty =>
    obtain ⟨G₁, hcond, hframe⟩ := focus_cond hty rfl hne cct heap
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hcond, .cons hframe hcont⟩
  | focusEnforce =>
    cases hctrl with | expr hty =>
    obtain ⟨G₁, hinner, hframe⟩ := focus_enforce hty rfl cct heap
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hinner, .cons hframe hcont⟩
  | focusDynAttrAccess =>
    cases hctrl with | expr hty =>
    obtain ⟨G₁, hbase, hframe⟩ := focus_dynAttrAccess hty rfl cct heap
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hbase, .cons hframe hcont⟩
  -- ═══════════════════════════════════════════════════════════
  -- ATOMIC VALUE CASES
  -- ═══════════════════════════════════════════════════════════
  | constNone =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (constNone_val_of_expr hty rfl hheap), hcont⟩
  | constTrue =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (constTrue_val_of_expr hty rfl hheap), hcont⟩
  | constFalse =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (constFalse_val_of_expr hty rfl hheap), hcont⟩
  | varSuccess hlookup =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (var_val_of_expr hty rfl henv hlookup), hcont⟩
  | varError hlookup =>
    cases hctrl with | expr hty => exact absurd hlookup (var_lookup_ne_none hty rfl henv)
  | newSuccess hfind hne_bool hne_none hne_bm halloc =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign,
      checkedEnvHasType_heapMono hmono henv,
      .val (new_val_of_expr hty rfl hwfct halloc),
      checkedContinuationHasType_heapMono hmono hcont⟩
  | newClassNotFound hnotfound =>
    cases hctrl with | expr hty =>
    obtain ⟨c, hfind⟩ := new_class_exists hty rfl
    simp [hnotfound] at hfind
  | newBuiltinError hfind hbuiltin =>
    cases hctrl with | expr hty =>
    have ⟨hne_bool, hne_none, hne_bm⟩ := new_not_builtin hty rfl
    rcases hbuiltin with rfl | rfl | rfl
    · exact absurd rfl hne_bool
    · exact absurd rfl hne_none
    · exact absurd rfl hne_bm
  -- isInstance cases
  | isInstanceTrue hlookup hlookObj hfindCls hMro hmem =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (isInstance_val_of_expr hty rfl hheap _ (.inl rfl)), hcont⟩
  | isInstanceFalse hlookup hlookObj hfindCls hMro hnotmem =>
    cases hctrl with | expr hty =>
    exact ⟨_, _, _, hwfct, hheap', halign, henv,
      .val (isInstance_val_of_expr hty rfl hheap _ (.inr rfl)), hcont⟩
  | isInstanceVarNotFound hlookup =>
    cases hctrl with | expr hty => exact absurd hlookup (isInstance_var_exists hty rfl henv)
  -- ═══════════════════════════════════════════════════════════
  -- condIsInstance CASES
  -- ═══════════════════════════════════════════════════════════
  | condIsInstanceTrue henvlook hlookObj hfindCls hMro hmem =>
    cases hctrl with | expr hty =>
    rcases checked_has_type_cond_isInstance_inv hty with
      ⟨_, _, hthen, _⟩ | ⟨_, _, hlookΓ, hfindG, hthen, _⟩
    · exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr hthen,
        .cons (.returnTo henv) hcont⟩
    · obtain ⟨_, hv, hvty⟩ := henv _ _ hlookΓ
      rw [hv] at henvlook
      cases Option.some.inj henvlook
      obtain ⟨_, _, hfindC, hmroC⟩ := hheap.classesExist _ _ hlookObj
      cases Option.some.inj (hfindC.symm.trans hfindCls)
      cases gComputeMro_determinism hmroC hMro
      let hmroCfull := (hwfct.raw.allMrosExist _ _ hfindG).hmro
      have wC : CheckedValueWitness gct cct heap _ (.class_ _) :=
        .mk (.class_ hfindG hmroCfull) (.class_ (.objRef hlookObj hfindCls hMro hmem))
      have wRef := checkedValueWitness_isInstanceThenRefinement hvty wC
      exact ⟨_, _, _, hwfct, hheap', halign,
        checkedEnvHasType_updateWitness henv hlookΓ hv wRef, .expr hthen,
        .cons (.returnTo henv) hcont⟩
  | condIsInstanceFalse henvlook hlookObj hfindCls hMro hnotmem =>
    cases hctrl with | expr hty =>
    rcases checked_has_type_cond_isInstance_inv hty with
      ⟨_, _, _, helse⟩ | ⟨_, _, hlookΓ, hfindG, _, helse⟩
    · exact ⟨_, _, _, hwfct, hheap', halign, henv, .expr helse,
        .cons (.returnTo henv) hcont⟩
    · obtain ⟨_, hv, hvty⟩ := henv _ _ hlookΓ
      rw [hv] at henvlook
      cases Option.some.inj henvlook
      let hmroC := (hwfct.raw.allMrosExist _ _ hfindG).hmro
      have wNeg : CheckedValueWitness gct cct heap _ (.negClass _) :=
        .mk (.negClass hfindG hmroC) (.negClass (.objRef hlookObj)
          (.negClassObjRefOk hlookObj hfindCls hMro hnotmem))
      have wRef := checkedValueWitness_isInstanceElseRefinement hvty wNeg
      exact ⟨_, _, _, hwfct, hheap', halign,
        checkedEnvHasType_updateWitness henv hlookΓ hv wRef, .expr helse,
        .cons (.returnTo henv) hcont⟩
  | condIsInstanceVarNotFound henvlook =>
    cases hctrl with | expr hty => exact absurd henvlook (condIsInstance_var_exists hty rfl henv)
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: cond
  -- ═══════════════════════════════════════════════════════════
  | returnCondTrue =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    have ⟨rfl, hthen_ctrl⟩ := cond_frame_then_branch hf rfl
    exact ⟨_, _, _, hwfct, hheap', halign, henv, hthen_ctrl, hk⟩
  | returnCondFalse =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    have ⟨rfl, helse_ctrl⟩ := cond_frame_else_branch hf rfl
    exact ⟨_, _, _, hwfct, hheap', halign, henv, helse_ctrl, hk⟩
  | returnCondNotBool hne_true hne_false =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with | cond _ _ =>
    rcases boolClass_objRef_is_true_or_false w hheap hwfct with rfl | rfl
    · exact absurd rfl hne_true
    · exact absurd rfl hne_false
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: returnFromBody, enforce
  -- ═══════════════════════════════════════════════════════════
  | returnFromBody =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    have ⟨hcallerEnv, w'⟩ := returnTo_value_transfer hf rfl w
    exact ⟨_, _, _, hwfct, hheap', halign, hcallerEnv, .val w', hk⟩
  | returnEnforceOk henf =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    have ⟨rfl, hcb, hwfG, htgt⟩ := enforce_frame_info hf rfl
    have w' := enforce_ok_has_witness henf (checkedValueWitness_toShape w)
      hheap hwfct halign _ hcb htgt hwfG
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .val w', hk⟩
  | returnEnforceBlame henf =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_enforce hf ⟨_, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: attribute access
  -- ═══════════════════════════════════════════════════════════
  | returnAttrAccess hlookObj hfindCls hMro hfindMethod halloc =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with
    | attrAccess _ | attrAccessUnion _ _ =>
      exact ⟨_, _, _, hwfct, hheap', halign,
        checkedEnvHasType_heapMono hmono henv,
        .val (allocated_boundMethod_class_witness halloc hwfct),
        checkedContinuationHasType_heapMono hmono hk⟩
  | returnAttrAccessNotFound hlookObj hfindCls hMro hnotfound =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with
    | attrAccess hfind =>
      exact (attrAccess_method_exists_contradiction hfind w hlookObj hfindCls hMro hnotfound halign).elim
    | attrAccessUnion hfind1 hfind2 =>
      cases w.data with
      | unionLeft wL =>
        exact (attrAccess_method_exists_contradiction hfind1
          (.mk wL.wf wL.data) hlookObj hfindCls hMro hnotfound halign).elim
      | unionRight wR =>
        exact (attrAccess_method_exists_contradiction hfind2
          (.mk wR.wf wR.data) hlookObj hfindCls hMro hnotfound halign).elim
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: dynamic attribute access
  -- ═══════════════════════════════════════════════════════════
  | returnDynAttrAccess hlookObj hfindCls hMro hfindMethod halloc =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with | dynAttrAccess =>
    exact ⟨_, _, _, hwfct, hheap', halign,
      checkedEnvHasType_heapMono hmono henv,
      .val (allocated_objRef_any_witness halloc),
      checkedContinuationHasType_heapMono hmono hk⟩
  | returnDynAttrAccessNotFound hlookObj hfindCls hMro hnotfound =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_dynAttrAccess hf ⟨_, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: call callee
  -- ═══════════════════════════════════════════════════════════
  | returnCallCalleeBound hlookup =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with | callCallee harg hassign _ htReturn _ hwfReturn =>
    cases checkedValueWitness_callable_view w with
    | objRefBoundMethod hlook' hrecv hmro_method =>
      rw [hlookup] at hlook'; cases Option.some.inj hlook'
      have hmethodTarget := checkedMethodInReceiverMro_checkedTarget halign hmro_method
      have hmethodWf := checkedMethodInReceiverMro_wellFormed halign hmro_method
      exact ⟨_, _, _, hwfct, hheap', halign, henv,
        .expr harg,
        .cons (.awaitArgument hrecv hmro_method
          hmethodTarget.1 hmethodTarget.2 htReturn
          hmethodWf.1 hmethodWf.2 hwfReturn) hk⟩
  | returnCallCalleeNotCallable hlookup =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with | callCallee _ _ _ _ _ _ =>
    cases checkedValueWitness_callable_view w with
    | objRefBoundMethod hlook' _ _ =>
      rw [hlookup] at hlook'
      exact absurd (Option.some.inj hlook') nofun
  -- ═══════════════════════════════════════════════════════════
  -- RETURN CASES: await argument (bare bound method)
  -- ═══════════════════════════════════════════════════════════
  | returnAwaitArgumentOk henf =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases hf with
    | awaitArgument hrecv hmro_method htParam htMethodReturn htCallReturn hwfParam hwfMethodReturn hwfCallReturn =>
    have wArgEnforced := enforce_ok_has_witness henf (checkedValueWitness_toShape w)
        hheap hwfct halign _ (compileBoundaryTarget_eq_compileBoundaryRaw_interp _)
        htParam
        hwfParam
    obtain ⟨recvCls, recvMro, hfindRecv, hMroRecv, hfindCm⟩ := hmro_method
    obtain ⟨dname, dc, hdname_mem, hdc, hcm_in_dc⟩ := findCheckedMethodInMro_provenance hfindCm
    have hbody := halign.methodBodiesTyped dname dc _ hdc hcm_in_dc
    obtain ⟨dcls, dmro, hfdc, hdmro⟩ :=
      mro_member_wellFormedClass (fun cname c hfind => (hwfct.raw.allMrosExist cname c hfind).exists)
        (findGClass_self hfindRecv) hMroRecv hdname_mem
    have wRecv : CheckedValueWitness gct cct heap _ (.class_ dname) :=
      .mk (.class_ hfdc hdmro) (.class_ (.objRef hrecv hfindRecv hMroRecv hdname_mem))
    refine ⟨_, _, _, hwfct, hheap', halign, ?_, .expr hbody,
      .cons (.enforce hwfMethodReturn htMethodReturn)
        (.cons (.enforce hwfCallReturn htCallReturn)
          (.cons (.returnTo henv) hk))⟩
    intro x Gx hlook
    simp only [NamedEnv.lookup] at hlook
    split at hlook
    · have hGx := Option.some.inj hlook
      exact ⟨_, by simp [NamedEnv.lookup, *], hGx ▸ wArgEnforced⟩
    · split at hlook
      · have hGx := Option.some.inj hlook
        exact ⟨_, by simp [NamedEnv.lookup, *], hGx ▸ wRecv⟩
      · cases hlook
  | returnAwaitArgumentBlame henf =>
    cases hctrl with | val w =>
    cases hcont with | cons hf hk =>
    cases frameHasType_env_eq_awaitArgument hf ⟨_, _, _, _, rfl⟩
    exact ⟨_, _, _, hwfct, hheap', halign, henv, .blame, hk⟩

/-! ### Multi-step preservation -/

private theorem checked_preservation_steps
    (hsafe : CheckedStateSafe gct cct s.heap s.env s.control s.continuation expectedType)
    (hsteps : Steps gct cct s s') :
    CheckedStateSafe gct cct s'.heap s'.env s'.control s'.continuation expectedType := by
  induction hsteps with
  | refl => exact hsafe
  | step hs _ ih => exact ih (checked_preservation hsafe hs)

/-- Multi-step preservation. -/
theorem checked_preservation_multi
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hsteps : Steps gct cct { heap, env, control := ctrl, continuation := cont }
                        { heap := heap', env := env', control := ctrl', continuation := cont' }) :
    CheckedStateSafe gct cct heap' env' ctrl' cont' expectedType :=
  checked_preservation_steps hsafe hsteps

end Checked

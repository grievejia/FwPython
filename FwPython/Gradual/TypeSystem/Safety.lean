import FwPython.Gradual.TypeSystem.Method.Lookup
import FwPython.Gradual.TypeSystem.ValueTyping
import FwPython.Gradual.Checked.Invariants

/-! ## Typed continuations and safe states for the checked machine

Proof-only judgments for typed checked machine states. Blame is a valid
final outcome (enforcement boundaries inserted by elaboration can fail),
so the safety theorem guarantees no raw `runtimeError`, not no blame. -/

namespace Checked

/-! ### Control typing -/

/-- A checked control has type `G` under the given context. Expressions
    and values get typing constructors; blame is universally typed (it
    can replace any expected result); runtime errors have no constructor
    and are ruled out by preservation. -/
inductive CheckedControlHasType (gct : GClassTable) (cct : CheckedClassTable) (heap : CheckedHeap)
    (Γ : CheckedTyEnv) : Control → GTy → Prop where
  | expr :
      CheckedHasType gct Γ e G →
      CheckedControlHasType gct cct heap Γ (.expr e) G
  | val :
      CheckedValueWitness gct cct heap v G →
      CheckedControlHasType gct cct heap Γ (.val v) G
  | blame :
      CheckedControlHasType gct cct heap Γ (.blame ℓ) G

theorem CheckedControlHasType.not_runtimeError
    (hctrl : CheckedControlHasType gct cct heap Γ ctrl G) :
    ∀ err, ctrl ≠ .runtimeError err := by
  intro err hEq
  cases hctrl <;> cases hEq

/-! ### Frame typing -/

/-- A checked frame has compatible input and output types and environments. -/
inductive CheckedFrameHasType (gct : GClassTable) (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    CheckedTyEnv → GTy → CheckedTyEnv → GTy → Frame → Prop where

  /-- Attribute access frame: consumes a class-typed value, produces
      exactly `class_ boundMethodClass`. -/
  | attrAccess :
      FindGMethodType gct cname attrName paramTy returnTy →
      CheckedFrameHasType gct cct heap Γ (.class_ cname) Γ (.class_ boundMethodClass)
        (.attrAccess attrName)

  /-- Attribute access on union receiver yields exactly `class_ boundMethodClass`. -/
  | attrAccessUnion :
      FindGMethodType gct c1 attrName p1 r1 →
      FindGMethodType gct c2 attrName p2 r2 →
      CheckedFrameHasType gct cct heap Γ (.union (.class_ c1) (.class_ c2))
        Γ (.class_ boundMethodClass) (.attrAccess attrName)

  /-- Dynamic attribute access frame: preserves the environment and
      produces exactly `any` from any checked input type. -/
  | dynAttrAccess :
      CheckedFrameHasType gct cct heap Γ inTy Γ .any (.dynAttrAccess attrName ℓ)

  /-- Call-callee frame: consumes a callable value, produces exactly `returnTy`. -/
  | callCallee :
      CheckedHasType gct Γ arg argTy →
      AssignableTo gct argTy (interpTarget paramTy) →
      RuntimePublicCheckedTarget gct paramTy →
      RuntimePublicCheckedTarget gct returnTy →
      WellFormedGTy gct (interpTarget paramTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedFrameHasType gct cct heap Γ
        (.callable (interpTarget paramTy) (interpTarget returnTy))
        Γ
        (interpTarget returnTy)
        (.callCallee arg paramTy returnTy returnLabels)

  /-- Call-value frame: consumes a callable callee, produces exactly `returnTy`. -/
  | callValue :
      CheckedValueWitness gct cct heap argVal argTy →
      RuntimePublicCheckedTarget gct paramTy →
      RuntimePublicCheckedTarget gct returnTy →
      WellFormedGTy gct (interpTarget paramTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedFrameHasType gct cct heap Γ
        (.callable (interpTarget paramTy) (interpTarget returnTy))
        Γ
        (interpTarget returnTy)
        (.callValue argVal paramTy returnTy returnLabels)

  /-- Await-argument frame: produces exactly the call-site `returnTy`. -/
  | awaitArgument :
      heap.lookup recvOid = some recvObj →
      CheckedMethodInReceiverMro gct cct recvObj.className cm →
      RuntimePublicCheckedTarget gct cm.paramTy →
      RuntimePublicCheckedTarget gct cm.returnTy →
      RuntimePublicCheckedTarget gct returnTy →
      WellFormedGTy gct (interpTarget cm.paramTy) →
      WellFormedGTy gct (interpTarget cm.returnTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedFrameHasType gct cct heap Γ inTy Γ (interpTarget returnTy)
        (.awaitArgument recvOid cm returnTy returnLabels)

  /-- Conditional frame: consumes an exact `class_ boolClass` value,
      produces exactly `R`. -/
  | cond :
      CheckedHasType gct Γ thenBr R →
      CheckedHasType gct Γ elseBr R →
      CheckedFrameHasType gct cct heap Γ (.class_ boolClass) Γ R (.cond thenBr elseBr)

  /-- Return-to frame: restores the caller environment. -/
  | returnTo :
      CheckedEnvHasType gct cct heap callerEnv callerΓ →
      CheckedFrameHasType gct cct heap bodyΓ G callerΓ G (.returnTo callerEnv)

  /-- Enforce frame: enforces the compiled contract image of `target`.
      Stores admissibility for downstream preservation use. -/
  | enforce :
      WellFormedGTy gct (interpTarget target) →
      RuntimePublicCheckedTarget gct target →
      CheckedFrameHasType gct cct heap Γ inTy Γ (interpTarget target) (.enforce target ℓ)


/-! ### Continuation typing -/

/-- A checked continuation is well-typed when frames thread types from
    top to bottom. -/
inductive CheckedContinuationHasType (gct : GClassTable) (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    CheckedTyEnv → GTy → CheckedTyEnv → GTy → Continuation → Prop where
  | nil :
      CheckedContinuationHasType gct cct heap Γ G Γ G []
  | cons :
      CheckedFrameHasType gct cct heap inΓ inTy midΓ midTy f →
      CheckedContinuationHasType gct cct heap midΓ midTy outΓ outTy k →
      CheckedContinuationHasType gct cct heap inΓ inTy outΓ outTy (f :: k)

/-! ### Checked class table alignment -/

/-- A checked class table is aligned with a gradual class table when:
    - same class names and base class lists
    - method lookup along any MRO agrees (if gradual has method m at name n,
      checked has a method at name n with matching types and compiled contracts)
    - every checked method body is well-typed under its declared signature
    - every checked method has well-formed gradual type annotations -/
structure AlignedCheckedClassTable (gct : GClassTable) (cct : CheckedClassTable) : Prop where
  classLookupAgree : ∀ cname gc,
    findGClass gct cname = some gc →
    ∃ cc, findCheckedClass cct cname = some cc ∧
      cc.name = gc.name ∧ cc.baseClasses = gc.baseClasses
  methodLookupAgree : ∀ cname gc cc mro gm,
    findGClass gct cname = some gc →
    findCheckedClass cct cname = some cc →
    GComputeMro gct gc mro →
    findGMethodInMro gct mro gm.name = some gm →
    ∃ cm, findCheckedMethodInMro cct mro gm.name = some cm ∧
      cm.paramTy = gm.paramTy ∧
      cm.returnTy = gm.returnTy ∧
      cm.parameterContract = compileBoundaryRaw cm.paramTy ∧
      cm.returnContract = compileBoundaryRaw cm.returnTy
  methodSignaturesWellFormed : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    WellFormedGTy gct cm.paramTy ∧ WellFormedGTy gct cm.returnTy
  methodBodiesTyped : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    CheckedHasType gct [(cm.param, cm.paramTy), (cm.receiverParam, .class_ cname)] cm.body cm.returnTy
  methodContractsCompiled : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    cm.parameterContract = compileBoundaryRaw cm.paramTy ∧ cm.returnContract = compileBoundaryRaw cm.returnTy
  methodSignaturesRuntimePublic : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    RuntimePublicCheckedTarget gct cm.paramTy ∧ RuntimePublicCheckedTarget gct cm.returnTy

/-- Typed attribute access guarantees the checked method lookup succeeds. -/
theorem attrAccess_method_exists_contradiction
    (hfind : FindGMethodType gct cname attrName paramTy returnTy)
    (w : CheckedValueWitness gct cct heap (.objRef objOid) (.class_ cname))
    (hlookObj : heap.lookup objOid = some obj)
    (hfindCls : findGClass gct obj.className = some c)
    (hMro : GComputeMro gct c mro)
    (hnotfound : findCheckedMethodInMro cct mro attrName = none)
    (halign : AlignedCheckedClassTable gct cct) :
    False := by
  cases checkedValueWitness_class_view w with
  | objRef hlook hfindG hmroG hmemG =>
      rw [hlookObj] at hlook
      cases Option.some.inj hlook
      rw [hfindCls] at hfindG
      cases Option.some.inj hfindG
      cases gComputeMro_determinism hMro hmroG
      obtain ⟨cCls, cMro, gm, hfcC, hmroC, hfgm, _, _⟩ := hfind
      obtain ⟨ccC, hfccC, _, _⟩ := halign.classLookupAgree _ _ hfcC
      have hgmname := findGMethodInMro_name hfgm
      have hfgm_name : findGMethodInMro gct cMro gm.name = some gm := by
        simpa [hgmname] using hfgm
      obtain ⟨cm, hfcm, _, _, _, _⟩ :=
        halign.methodLookupAgree _ _ _ _ _ hfcC hfccC hmroC hfgm_name
      obtain ⟨dname, dc, hdmem, hdc, hcm_in⟩ := findCheckedMethodInMro_provenance hfcm
      have hdname_in_mro : dname ∈ mro :=
        mro_mem_trans gct c cCls mro cMro dname (findGClass_self hfindCls) hMro
          (findGClass_self hfcC) hmroC (by simpa [findGClass_name hfcC] using hmemG) hdmem
      obtain ⟨m', hm'⟩ :=
        findCheckedMethodInMro_exists_of_mem hdname_in_mro hdc hcm_in
          ((findCheckedMethodInMro_name hfcm).trans hgmname)
      simp [hnotfound] at hm'

/-! ### Safe states -/

/-- A checked machine state is safe when the heap is well-formed, the
    environment is well-typed, the control has a type, and the continuation
    threads that type to the expected result. The checked class table must
    be aligned with the gradual class table. -/
def CheckedStateSafe (gct : GClassTable) (cct : CheckedClassTable)
    (heap : CheckedHeap) (env : CheckedEnv)
    (ctrl : Control) (cont : Continuation) (expectedType : GTy) : Prop :=
  ∃ (Γ outΓ : CheckedTyEnv) (G : GTy) (_hwfct : WellFormedGClassTableCore gct),
    CheckedHeapWellFormed gct cct heap ∧
    AlignedCheckedClassTable gct cct ∧
    CheckedEnvHasType gct cct heap env Γ ∧
    CheckedControlHasType gct cct heap Γ ctrl G ∧
    CheckedContinuationHasType gct cct heap Γ G outΓ expectedType cont

theorem CheckedStateSafe.not_runtimeError
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType) :
    ∀ err, ctrl ≠ .runtimeError err := by
  rcases hsafe with ⟨Γ, outΓ, G, hwfct, hheap, halign, henv, hctrl, hcont⟩
  exact hctrl.not_runtimeError

end Checked

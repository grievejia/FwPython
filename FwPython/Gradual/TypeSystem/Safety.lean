import FwPython.Gradual.TypeSystem.Method.Lookup
import FwPython.Gradual.TypeSystem.ValueTyping
import FwPython.Gradual.Checked.Invariants

/-! ## Typed continuations and safe states for the checked machine

Proof judgments for typed checked machine states. Enforcement boundaries
inserted by elaboration can fail with blame. The safety theorem excludes
raw `runtimeError` outcomes and permits blame.

The judgments carry one hierarchy for the erased source declarations.
Expression typing, call comparisons, and checked method-body typing use that
same table. Runtime value and environment witnesses certify heap storage and
successful runtime checks using the raw declarations. -/

namespace Checked

/-! ### Control typing -/

/-- A checked control has type `G` under the supplied table, heap, and variable types. Expressions
    and values get typing constructors; blame is universally typed (it
    can replace any expected result); runtime errors have no constructor
    and are ruled out by preservation. -/
inductive CheckedControlHasType (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (cct : CheckedClassTable) (heap : CheckedHeap)
    (Γ : CheckedTyEnv) : Control → GTy → Prop where
  | expr :
      CheckedHasType gct structural Γ e G →
      CheckedControlHasType gct structural cct heap Γ (.expr e) G
  | val :
      CheckedValueWitness gct cct heap v G →
      CheckedControlHasType gct structural cct heap Γ (.val v) G
  | blame :
      CheckedControlHasType gct structural cct heap Γ (.blame info) G

theorem CheckedControlHasType.not_runtimeError
    (hctrl : CheckedControlHasType gct structural cct heap Γ ctrl G) :
    ∀ err, ctrl ≠ .runtimeError err := by
  intro err hEq
  cases hctrl <;> cases hEq

/-! ### Frame typing -/

/-- A checked frame has compatible input and output types and environments. -/
inductive CheckedFrameHasType (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    CheckedTyEnv → GTy → CheckedTyEnv → GTy → Frame → Prop where

  /-- Attribute access frame: consumes a class-typed value, produces
      exactly `class_ boundMethodClass`. -/
  | attrAccess :
      FindGMethodType gct cname attrName paramTy returnTy →
      CheckedFrameHasType gct structural cct heap Γ (.class_ cname) Γ (.class_ boundMethodClass)
        (.attrAccess attrName)

  /-- Attribute access on union receiver yields exactly `class_ boundMethodClass`. -/
  | attrAccessUnion :
      FindGMethodType gct c1 attrName p1 r1 →
      FindGMethodType gct c2 attrName p2 r2 →
      CheckedFrameHasType gct structural cct heap Γ (.union (.class_ c1) (.class_ c2))
        Γ (.class_ boundMethodClass) (.attrAccess attrName)

  /-- Dynamic attribute access frame: preserves the environment and
      produces exactly `any` from any checked input type. -/
  | dynAttrAccess :
      CheckedFrameHasType gct structural cct heap Γ inTy Γ .any (.dynAttrAccess attrName obligation)

  /-- Call-callee frame: consumes a callable value, produces exactly `returnTy`. -/
  | callCallee :
      CheckedHasType gct structural Γ arg argTy →
      AssignableTo gct structural argTy (interpTarget paramTy) →
      CheckedTargetTy gct (interpTarget paramTy) →
      CheckedTargetTy gct (interpTarget returnTy) →
      WellFormedGTy gct (interpTarget paramTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedFrameHasType gct structural cct heap Γ
        (.callable (interpTarget paramTy) (interpTarget returnTy))
        Γ
        (interpTarget returnTy)
        (.callCallee arg paramTy returnTy returnObligation)

  /-- Await-argument frame: produces exactly the call-site `returnTy`. -/
  | awaitArgument :
      heap.lookup recvOid = some recvObj →
      CheckedMethodInReceiverMro gct cct recvObj.className cm →
      CheckedTargetTy gct (interpTarget cm.paramTy) →
      CheckedTargetTy gct (interpTarget cm.returnTy) →
      CheckedTargetTy gct (interpTarget returnTy) →
      WellFormedGTy gct (interpTarget cm.paramTy) →
      WellFormedGTy gct (interpTarget cm.returnTy) →
      WellFormedGTy gct (interpTarget returnTy) →
      CheckedFrameHasType gct structural cct heap Γ inTy Γ (interpTarget returnTy)
        (.awaitArgument recvOid cm returnTy returnObligation)

  /-- Conditional frame: consumes an exact `class_ boolClass` value,
      produces exactly `R`. -/
  | cond :
      CheckedHasType gct structural Γ thenBr R →
      CheckedHasType gct structural Γ elseBr R →
      CheckedFrameHasType gct structural cct heap Γ (.class_ boolClass) Γ R (.cond thenBr elseBr)

  /-- Return-to frame: restores the caller environment. -/
  | returnTo :
      CheckedEnvHasType gct cct heap callerEnv callerΓ →
      CheckedFrameHasType gct structural cct heap bodyΓ G callerΓ G (.returnTo callerEnv)

  /-- Enforce frame: enforces the compiled contract image of `target`.
      Stores admissibility for downstream preservation use. -/
  | enforce :
      WellFormedGTy gct (interpTarget target) →
      CheckedTargetTy gct (interpTarget target) →
      CheckedFrameHasType gct structural cct heap Γ inTy Γ (interpTarget target) (.enforce target obligation)


/-! ### Continuation typing -/

/-- A checked continuation is well-typed when frames thread types from
    top to bottom. -/
inductive CheckedContinuationHasType (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (cct : CheckedClassTable)
    (heap : CheckedHeap) :
    CheckedTyEnv → GTy → CheckedTyEnv → GTy → Continuation → Prop where
  | nil :
      CheckedContinuationHasType gct structural cct heap Γ G Γ G []
  | cons :
      CheckedFrameHasType gct structural cct heap inΓ inTy midΓ midTy f →
      CheckedContinuationHasType gct structural cct heap midΓ midTy outΓ outTy k →
      CheckedContinuationHasType gct structural cct heap inΓ inTy outΓ outTy (f :: k)

/-! ### Checked class table alignment -/

/-- A checked class table is aligned with a gradual class table when checked
class lookup preserves source classes, checked method lookup mirrors source MRO
lookup, checked method targets compile to their runtime contracts, and checked method bodies
typecheck under their checked runtime signatures. -/
structure AlignedCheckedClassTable (gct : GClassTable)
    (structural : WellFormedClassHierarchy (eraseClassTable gct)) (cct : CheckedClassTable) : Prop where
  /-- Checked class lookup preserves source class names and declared base classes. -/
  classLookupAgree : ∀ cname gc,
    findGClass gct cname = some gc →
    ∃ cc, findCheckedClass cct cname = some cc ∧
      cc.name = gc.name ∧ cc.baseClasses = gc.baseClasses
  /-- Source MRO method lookup is mirrored by checked MRO lookup with matching
  interpreted targets. -/
  methodLookupAgree : ∀ cname gc cc mro gm,
    findGClass gct cname = some gc →
    findCheckedClass cct cname = some cc →
    GComputeMro gct gc mro →
    findGMethodInMro gct mro gm.name = some gm →
    ∃ cm, findCheckedMethodInMro cct mro gm.name = some cm ∧
      interpTarget cm.paramTy = gm.paramTy ∧
      interpTarget cm.returnTy = gm.returnTy
  /-- Every checked method's interpreted parameter and return targets are
  well-formed gradual types. -/
  methodSignaturesWellFormed : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    WellFormedGTy gct cm.paramTy ∧ WellFormedGTy gct cm.returnTy
  /-- Every checked method body typechecks under its checked parameter and
  receiver environment at the neutral method-body type. The machine-pushed
  method-return frame owns the declared return boundary. -/
  methodBodiesTyped : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    CheckedHasType gct structural [(cm.param, cm.paramTy), (cm.receiverParam, .class_ cname)] cm.body .any
  /-- Every checked method's stored targets are valid checked targets for the
  gradual class table. -/
  methodSignaturesCheckedTarget : ∀ cname cc cm,
    findCheckedClass cct cname = some cc →
    cm ∈ cc.methods →
    CheckedTargetTy gct (interpTarget cm.paramTy) ∧ CheckedTargetTy gct (interpTarget cm.returnTy)

variable {structural : WellFormedClassHierarchy (eraseClassTable gct)}

/-- Typed attribute access guarantees the checked method lookup succeeds. -/
theorem attrAccess_method_exists_contradiction
    (hfind : FindGMethodType gct cname attrName paramTy returnTy)
    (w : CheckedValueWitness gct cct heap (.objRef objOid) (.class_ cname))
    (hlookObj : heap.lookup objOid = some obj)
    (hfindCls : findGClass gct obj.className = some c)
    (hMro : GComputeMro gct c mro)
    (hnotfound : findCheckedMethodInMro cct mro attrName = none)
    (halign : AlignedCheckedClassTable gct structural cct) :
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
      obtain ⟨cm, hfcm, _, _⟩ :=
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
  ∃ (Γ outΓ : CheckedTyEnv) (G : GTy) (hwfct : WellFormedGClassTableCore gct),
    CheckedHeapWellFormed gct cct heap ∧
    AlignedCheckedClassTable gct hwfct.toWellFormedClassHierarchy cct ∧
    CheckedEnvHasType gct cct heap env Γ ∧
    CheckedControlHasType gct hwfct.toWellFormedClassHierarchy cct heap Γ ctrl G ∧
    CheckedContinuationHasType gct hwfct.toWellFormedClassHierarchy cct heap Γ G outΓ expectedType cont

/-- A safely typed state's control is not a runtime error. -/
theorem CheckedStateSafe.not_runtimeError
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType) :
    ∀ err, ctrl ≠ .runtimeError err := by
  rcases hsafe with ⟨_, _, _, _, _, _, _, hctrl, _⟩
  exact hctrl.not_runtimeError

end Checked

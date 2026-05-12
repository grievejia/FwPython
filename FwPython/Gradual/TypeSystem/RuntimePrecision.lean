import FwPython.Gradual.TypeSystem.StaticGG
import FwPython.Gradual.TypeSystem.ValueSemantics
import FwPython.Gradual.TypeSystem.Soundness
import FwPython.Gradual.TypeSystem.Blame.Provenance
import FwPython.Gradual.Checked.Heap

/-! ## Runtime precision for the checked machine -/

namespace Checked

inductive CheckedHeapObjectPrecision
    (gct₁ : GClassTable) (_cct₁ _cct₂ : CheckedClassTable) (_oid : Nat) :
    CheckedHeapObject → CheckedHeapObject → Prop where
  | ordinary :
      CheckedHeapObjectPrecision gct₁ _cct₁ _cct₂ _oid
        ⟨className, .ordinary⟩
        ⟨className, .ordinary⟩
  | boundMethod :
      CheckedMethodPrecision gct₁ m₁ m₂ →
      CheckedHeapObjectPrecision gct₁ _cct₁ _cct₂ _oid
        ⟨boundMethodClass, .boundMethod recvOid m₁⟩
        ⟨boundMethodClass, .boundMethod recvOid m₂⟩

structure CheckedHeapPrecision
    (gct₁ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) : Prop where
  counter_eq : heap₁.heapCounter = heap₂.heapCounter
  lookup_prec_left :
    ∀ oid obj₁, heap₁.lookup oid = some obj₁ →
      ∃ obj₂, heap₂.lookup oid = some obj₂ ∧
        CheckedHeapObjectPrecision gct₁ cct₁ cct₂ oid obj₁ obj₂
  lookup_prec_right :
    ∀ oid obj₂, heap₂.lookup oid = some obj₂ →
      ∃ obj₁, heap₁.lookup oid = some obj₁ ∧
        CheckedHeapObjectPrecision gct₁ cct₁ cct₂ oid obj₁ obj₂

abbrev CheckedExprPrecision (gct₁ : GClassTable) (e₁ e₂ : CheckedExpr) : Prop :=
  ShapeExprPrecision gct₁ (eraseLabelsExpr e₁) (eraseLabelsExpr e₂)

inductive CheckedValuePrecision
    (gct₁ _gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) :
    CheckedValue → CheckedValue → Prop where
  | objRef :
      CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁ heap₂ →
      heap₁.lookup oid = some obj₁ →
      CheckedValuePrecision gct₁ _gct₂ cct₁ cct₂ heap₁ heap₂
        (.objRef oid)
        (.objRef oid)

inductive CheckedEnvPrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) :
    CheckedEnv → CheckedEnv → Prop where
  | nil :
      CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ [] []
  | cons :
      CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂ →
      CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ env₁ env₂ →
      CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        ((name, v₁) :: env₁)
        ((name, v₂) :: env₂)

inductive CheckedControlPrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) :
    Control → Control → Prop where
  | expr :
      CheckedExprPrecision gct₁ e₁ e₂ →
      CheckedControlPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ (.expr e₁) (.expr e₂)
  | val :
      CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂ →
      CheckedControlPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ (.val v₁) (.val v₂)
  | blame :
      CheckedControlPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ (.blame ℓ₁) (.blame ℓ₂)
  | runtimeError :
      CheckedControlPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.runtimeError err₁) (.runtimeError err₂)

inductive CheckedFramePrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) :
    Frame → Frame → Prop where
  | attrAccess :
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.attrAccess attrName)
        (.attrAccess attrName)
  | callCallee :
      CheckedExprPrecision gct₁ arg₁ arg₂ →
      CompileTargetPrecision paramTy₁ paramTy₂ →
      CompileTargetPrecision returnTy₁ returnTy₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁)
        (.callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂)
  | callValue :
      CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ argVal₁ argVal₂ →
      CompileTargetPrecision paramTy₁ paramTy₂ →
      CompileTargetPrecision returnTy₁ returnTy₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.callValue argVal₁ paramTy₁ returnTy₁ returnLabels₁)
        (.callValue argVal₂ paramTy₂ returnTy₂ returnLabels₂)
  | awaitArgument :
      CheckedMethodPrecision gct₁ m₁ m₂ →
      CompileTargetPrecision returnTy₁ returnTy₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.awaitArgument recvOid m₁ returnTy₁ returnLabels₁)
        (.awaitArgument recvOid m₂ returnTy₂ returnLabels₂)
  | cond :
      CheckedExprPrecision gct₁ thenBr₁ thenBr₂ →
      CheckedExprPrecision gct₁ elseBr₁ elseBr₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.cond thenBr₁ elseBr₁)
        (.cond thenBr₂ elseBr₂)
  | returnTo :
      CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ callerEnv₁ callerEnv₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.returnTo callerEnv₁)
        (.returnTo callerEnv₂)
  | enforce :
      CompileTargetPrecision c₁ c₂ →
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.enforce c₁ labels₁)
        (.enforce c₂ labels₂)
  | dynAttrAccess :
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
        (.dynAttrAccess attrName ℓ₁)
        (.dynAttrAccess attrName ℓ₂)

inductive CheckedContinuationPrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (heap₁ heap₂ : CheckedHeap) :
    Continuation → Continuation → Prop where
  | nil :
      CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ [] []
  | cons :
      CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ f₁ f₂ →
      CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ k₁ k₂ →
      CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ (f₁ :: k₁) (f₂ :: k₂)

structure CheckedStatePrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable)
    (s₁ s₂ : State) : Prop where
  heap_prec :
    CheckedHeapPrecision gct₁ cct₁ cct₂ s₁.heap s₂.heap
  env_prec :
    CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ s₁.heap s₂.heap s₁.env s₂.env
  control_prec :
    CheckedControlPrecision gct₁ gct₂ cct₁ cct₂ s₁.heap s₂.heap s₁.control s₂.control
  continuation_prec :
    CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂
      s₁.heap
      s₂.heap
      s₁.continuation
      s₂.continuation

/-- Minimal DGG-only state invariant: the hybrid runtime relation plus the
per-side provenance registration needed to keep simulation inductive. -/
abbrev WellElaboratedState
    (hcompiled : ElaboratesProgramAt gp P cp)
    (s : State) : Prop :=
  StateLabelsRegistered hcompiled s

structure ElaboratedStatePrecision
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (s₁ s₂ : State) : Prop where
  state_prec :
    CheckedStatePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes s₁ s₂
  left_wellElaborated :
    WellElaboratedState helab₁ s₁
  right_wellElaborated :
    WellElaboratedState helab₂ s₂

inductive CheckedOutcomePrecision
    (gct₁ gct₂ : GClassTable) (cct₁ cct₂ : CheckedClassTable) :
    (CheckedHeap × CheckedResult) → (CheckedHeap × CheckedResult) → Prop where
  | success_success :
      CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁ heap₂ →
      CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂ →
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂
        (heap₁, .success v₁)
        (heap₂, .success v₂)
  | blame_success :
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂
        (heap₁, .blame ℓ)
        (heap₂, .success v)
  | blame_blame :
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂
        (heap₁, .blame ℓ₁)
        (heap₂, .blame ℓ₂)
  | runtimeError_runtimeError :
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂
        (heap₁, .runtimeError err₁)
        (heap₂, .runtimeError err₂)

theorem checkedStatePrecision_final_right
    (hprec : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁ s₂)
    (hfinal₁ : finalResult? s₁ = some out₁) :
    ∃ out₂,
      finalResult? s₂ = some out₂ ∧
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂ out₁ out₂ := by
  cases s₁ with
  | mk heap₁ env₁ ctrl₁ cont₁ =>
      cases s₂ with
      | mk heap₂ env₂ ctrl₂ cont₂ =>
          rcases hprec with ⟨hheap, henv, hctrl, hcont⟩
          cases hctrl with
          | expr _ =>
              simp [finalResult?] at hfinal₁
          | val hval =>
              rename_i v₁ v₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₁
                  cases hfinal₁
                  exact ⟨(heap₂, .success v₂), by simp [finalResult?], .success_success hheap hval⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₁
          | blame =>
              rename_i ℓ₁ ℓ₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₁
                  cases hfinal₁
                  exact ⟨(heap₂, .blame ℓ₂), by simp [finalResult?], .blame_blame⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₁
          | runtimeError =>
              rename_i err₁ err₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₁
                  cases hfinal₁
                  exact ⟨(heap₂, .runtimeError err₂), by simp [finalResult?],
                    .runtimeError_runtimeError⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₁

theorem checkedStatePrecision_final_left
    (hprec : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁ s₂)
    (hfinal₂ : finalResult? s₂ = some out₂) :
    ∃ out₁,
      finalResult? s₁ = some out₁ ∧
      CheckedOutcomePrecision gct₁ gct₂ cct₁ cct₂ out₁ out₂ := by
  cases s₁ with
  | mk heap₁ env₁ ctrl₁ cont₁ =>
      cases s₂ with
      | mk heap₂ env₂ ctrl₂ cont₂ =>
          rcases hprec with ⟨hheap, henv, hctrl, hcont⟩
          cases hctrl with
          | expr _ =>
              simp [finalResult?] at hfinal₂
          | val hval =>
              rename_i v₁ v₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₂
                  cases hfinal₂
                  exact ⟨(heap₁, .success v₁), by simp [finalResult?], .success_success hheap hval⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₂
          | blame =>
              rename_i ℓ₁ ℓ₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₂
                  cases hfinal₂
                  exact ⟨(heap₁, .blame ℓ₁), by simp [finalResult?], .blame_blame⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₂
          | runtimeError =>
              rename_i err₁ err₂
              cases hcont with
              | nil =>
                  simp [finalResult?] at hfinal₂
                  cases hfinal₂
                  exact ⟨(heap₁, .runtimeError err₁), by simp [finalResult?],
                    .runtimeError_runtimeError⟩
              | cons _ _ =>
                  simp [finalResult?] at hfinal₂

theorem checkedStatePrecision_finality_agreement
    (hprec : CheckedStatePrecision gct₁ gct₂ cct₁ cct₂ s₁ s₂) :
    finalResult? s₁ = none ↔ finalResult? s₂ = none := by
  constructor
  · intro hnotFinal₁
    cases hfinal₂ : finalResult? s₂ with
    | none =>
        rfl
    | some out₂ =>
        rcases checkedStatePrecision_final_left hprec hfinal₂ with
          ⟨out₁, hfinal₁, _⟩
        rw [hfinal₁] at hnotFinal₁
        cases hnotFinal₁
  · intro hnotFinal₂
    cases hfinal₁ : finalResult? s₁ with
    | none =>
        rfl
    | some out₁ =>
        rcases checkedStatePrecision_final_right hprec hfinal₁ with
          ⟨out₂, hfinal₂, _⟩
        rw [hfinal₂] at hnotFinal₂
        cases hnotFinal₂

theorem ElaboratedStatePrecision.final_right
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    {helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁}
    {helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂}
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂)
    (hfinal₁ : finalResult? s₁ = some out₁) :
    ∃ out₂,
      finalResult? s₂ = some out₂ ∧
      CheckedOutcomePrecision
        gp₁.classes gp₂.classes cp₁.classes cp₂.classes out₁ out₂ :=
  checkedStatePrecision_final_right hprec.state_prec hfinal₁

theorem ElaboratedStatePrecision.finality_agreement
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂) :
    finalResult? s₁ = none ↔ finalResult? s₂ = none :=
  checkedStatePrecision_finality_agreement hprec.state_prec

theorem ElaboratedStatePrecision.not_final_of_left_can_step
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    {helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁}
    {helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂}
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂)
    (hleft : Checked.Step gp₁.classes cp₁.classes s₁ s₁') :
    finalResult? s₂ = none := by
  have hnotFinal₁ : finalResult? s₁ = none := by
    cases hfinal₁ : finalResult? s₁ with
    | none =>
        rfl
    | some _ =>
        exact (final_states_do_not_step hfinal₁ hleft).elim
  exact hprec.finality_agreement.mp hnotFinal₁

theorem ElaboratedStatePrecision.of_steps
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    {helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁}
    {helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂}
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂)
    (hsteps₁ : Checked.Steps gp₁.classes cp₁.classes s₁ s₁')
    (hsteps₂ : Checked.Steps gp₂.classes cp₂.classes s₂ s₂')
    (hstate : CheckedStatePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes s₁' s₂') :
    ElaboratedStatePrecision helab₁ helab₂ s₁' s₂' := by
  refine ⟨hstate, ?_, ?_⟩
  · exact steps_preserve_registered helab₁ hprec.left_wellElaborated hsteps₁
  · exact steps_preserve_registered helab₂ hprec.right_wellElaborated hsteps₂

theorem ElaboratedStatePrecision.of_step_steps
    {gp₁ gp₂ : GProgram}
    {P₁ P₂ : GTy}
    {cp₁ cp₂ : CheckedProgram}
    {helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁}
    {helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂}
    (hprec : ElaboratedStatePrecision helab₁ helab₂ s₁ s₂)
    (hstep₁ : Checked.Step gp₁.classes cp₁.classes s₁ s₁')
    (hsteps₂ : Checked.Steps gp₂.classes cp₂.classes s₂ s₂')
    (hstate : CheckedStatePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes s₁' s₂') :
    ElaboratedStatePrecision helab₁ helab₂ s₁' s₂' :=
  hprec.of_steps (.single hstep₁) hsteps₂ hstate

theorem checkedMethodPrecision_paramTarget_precision
    (h : CheckedMethodPrecision gct m₁ m₂) :
    CheckedTargetPrecision
      m₁.paramTy
      m₂.paramTy :=
  h.paramTy_prec

theorem checkedMethodPrecision_returnTarget_precision
    (h : CheckedMethodPrecision gct m₁ m₂) :
    CheckedTargetPrecision
      m₁.returnTy
      m₂.returnTy :=
  h.returnTy_prec

theorem checkedMethodPrecision_parameterContract_compiledBoundaryPrecision
    (h : CheckedMethodPrecision gct m₁ m₂) :
    CompiledBoundaryPrecision gct m₁.parameterContract m₂.parameterContract :=
  shapeMethodPrecision_parameterContract_prec h

theorem checkedMethodPrecision_returnContract_compiledBoundaryPrecision
    (h : CheckedMethodPrecision gct m₁ m₂) :
    CompiledBoundaryPrecision gct m₁.returnContract m₂.returnContract :=
  shapeMethodPrecision_returnContract_prec h

theorem checkedFramePrecision_callCallee_paramTarget_precision
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
      (.callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁)
      (.callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂)) :
    CompileTargetPrecision
      paramTy₁
      paramTy₂ := by
  cases hframe with
  | callCallee _ hparam _ =>
      exact hparam

theorem checkedFramePrecision_callCallee_returnTarget_precision
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
      (.callCallee arg₁ paramTy₁ returnTy₁ returnLabels₁)
      (.callCallee arg₂ paramTy₂ returnTy₂ returnLabels₂)) :
    CompileTargetPrecision
      returnTy₁
      returnTy₂ := by
  cases hframe with
  | callCallee _ _ hret =>
      exact hret

theorem checkedFramePrecision_callValue_paramTarget_precision
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
      (.callValue argVal₁ paramTy₁ returnTy₁ returnLabels₁)
      (.callValue argVal₂ paramTy₂ returnTy₂ returnLabels₂)) :
    CompileTargetPrecision
      paramTy₁
      paramTy₂ := by
  cases hframe with
  | callValue _ hparam _ =>
      exact hparam

theorem checkedFramePrecision_callValue_returnTarget_precision
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
      (.callValue argVal₁ paramTy₁ returnTy₁ returnLabels₁)
      (.callValue argVal₂ paramTy₂ returnTy₂ returnLabels₂)) :
    CompileTargetPrecision
      returnTy₁
      returnTy₂ := by
  cases hframe with
  | callValue _ _ hret =>
      exact hret

theorem checkedFramePrecision_awaitArgument_returnTarget_precision
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂
      (.awaitArgument recvOid m₁ returnTy₁ returnLabels₁)
      (.awaitArgument recvOid m₂ returnTy₂ returnLabels₂)) :
    CompileTargetPrecision
      returnTy₁
      returnTy₂ := by
  cases hframe with
  | awaitArgument _ hret =>
      exact hret

private theorem checkedHeapInitial_precision
    (gct : GClassTable) :
    CheckedHeapPrecision gct cct₁ cct₂ CheckedHeap.initial CheckedHeap.initial := by
  have hlookup_cases :
      ∀ {oid obj},
        CheckedHeap.initial.lookup oid = some obj →
        obj = ⟨noneClass, .ordinary⟩ ∨ obj = ⟨boolClass, .ordinary⟩ := by
    intro oid obj hlook
    unfold CheckedHeap.initial at hlook
    unfold CheckedHeap.lookup at hlook
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList, noneOid, trueOid, falseOid] at hlook
    split at hlook
    · exact .inl (Option.some.inj hlook).symm
    · split at hlook
      · exact .inr (Option.some.inj hlook).symm
      · split at hlook
        · exact .inr (Option.some.inj hlook).symm
        · cases hlook
  refine ⟨rfl, ?_, ?_⟩ <;>
    · rintro oid ⟨className, payload⟩ hlook
      cases payload with
      | ordinary => exact ⟨⟨className, .ordinary⟩, hlook, .ordinary⟩
      | boundMethod recvOid m =>
          rcases hlookup_cases hlook with hnone | hbool
          · cases hnone
          · cases hbool

private theorem checkedAnyShape_transport
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (hshape : CheckedAnyShape gct₁ cct₁ heap₁ v₁) :
    CheckedAnyShape gct₂ cct₂ heap₂ v₂ := by
  cases hval with
  | objRef hheap _ =>
      cases hshape with
      | objRef hlook =>
          obtain ⟨_, hlook₂, _⟩ := hheap.lookup_prec_left _ _ hlook
          exact .objRef hlook₂

private theorem checkedClassView_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (hview : CheckedClassView gct₁ cct₁ heap₁ v₁ cname) :
    CheckedClassView gct₂ cct₂ heap₂ v₂ cname := by
  cases hval with
  | objRef hheap _ =>
      cases hview with
      | objRef hlook hfind hmro hmem =>
          rcases hheap.lookup_prec_left _ _ hlook with ⟨_, hlook₂, hobjprec⟩
          obtain ⟨_, hfind₂, hclsPrec⟩ := findGClass_precision hct hfind
          have hmro₂ :=
            gComputeMro_transport hct hclsPrec hmro
          cases hobjprec <;> exact .objRef hlook₂ hfind₂ hmro₂ hmem

private theorem checkedNegClass_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (hwf₁ : WellFormedGTy gct₁ (.negClass cname))
    (hshape : CheckedAnyShape gct₁ cct₁ heap₁ v₁)
    (hok : ∀ ℓ, EnforceValue gct₁ heap₁ v₁ (compileBoundaryRaw (.negClass cname)) ℓ (.ok v₁)) :
    CheckedValueWitness gct₂ cct₂ heap₂ v₂ (.negClass cname) := by
  let hshape₂ := checkedAnyShape_transport hval hshape
  have hok₂ :
      ∀ ℓ, EnforceValue gct₂ heap₂ v₂
        (compileBoundaryRaw (.negClass cname)) ℓ (.ok v₂) := by
    intro ℓ
    cases hval with
    | objRef hheap hlookVal =>
        rename_i oid obj₁
        cases hshape with
        | objRef _ =>
            have hok₁ :
                EnforceValue gct₁ heap₁ (.objRef oid)
                  (compileBoundaryRaw (.negClass cname)) ℓ (.ok (.objRef oid)) := by
              simpa [compileBoundaryRaw] using hok ℓ
            cases hok₁ with
            | negClassObjRefOk hlook₁ hfind₁ hmro₁ hnmem₁ =>
                obtain ⟨_, hlook₂, hobjprec⟩ := hheap.lookup_prec_left _ _ hlook₁
                obtain ⟨_, hfind₂, hclsPrec⟩ := findGClass_precision hct hfind₁
                have hmro₂ := gComputeMro_transport hct hclsPrec hmro₁
                cases hobjprec <;>
                  simpa [compileBoundaryRaw] using
                    (EnforceValue.negClassObjRefOk (labels := ℓ)
                      hlook₂ hfind₂ hmro₂ hnmem₁)
  exact .mk (wellFormedGTy_transport hct hwf₁) (.negClass hshape₂ hok₂)

private theorem checkedCallableView_transport
    (hheapwf₂ : CheckedHeapWellFormed gct₂ cct₂ heap₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (hview : CheckedCallableView gct₁ cct₁ heap₁ v₁) :
    CheckedCallableView gct₂ cct₂ heap₂ v₂ := by
  cases hval with
  | objRef hheap _ =>
      cases hview with
      | objRefBoundMethod hlook _ _ =>
          obtain ⟨_, hlook₂, hobjprec⟩ := hheap.lookup_prec_left _ _ hlook
          cases hobjprec with
          | boundMethod _ =>
              obtain ⟨_, hrecv₂, hmro₂⟩ := hheapwf₂.payloadReceiverValid _ _ _ _ hlook₂
              exact .objRefBoundMethod hlook₂ hrecv₂ hmro₂

private def checkedValueWitness_transport_refl
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hheapwf₂ : CheckedHeapWellFormed gct₂ cct₂ heap₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (w₁ : CheckedValueWitness gct₁ cct₁ heap₁ v₁ G) :
    CheckedValueWitness gct₂ cct₂ heap₂ v₂ G :=
  match w₁ with
  | .mk hwf₁ (.any hshape) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.any (checkedAnyShape_transport hval hshape))
  | .mk hwf₁ (.class_ hview) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.class_ (checkedClassView_transport hct hval hview))
  | .mk hwf₁ (.callable hview) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.callable (checkedCallableView_transport hheapwf₂ hval hview))
  | .mk hwf₁ (.unionLeft wG) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.unionLeft (checkedValueWitness_transport_refl hct hheapwf₂ hval wG))
  | .mk hwf₁ (.unionRight wH) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.unionRight (checkedValueWitness_transport_refl hct hheapwf₂ hval wH))
  | .mk hwf₁ (.intersection wG wH) =>
      .mk (wellFormedGTy_transport hct hwf₁)
        (.intersection
          (checkedValueWitness_transport_refl hct hheapwf₂ hval wG)
          (checkedValueWitness_transport_refl hct hheapwf₂ hval wH))
  | .mk hwf₁ (.negClass hshape hok) =>
      checkedNegClass_transport hct hval hwf₁ hshape hok

theorem checkedValuePrecision_transport_heap
    (hheap' : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂')
    (hleft : ∀ oid obj, heap₁.lookup oid = some obj → heap₁'.lookup oid = some obj)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂) :
    CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁' heap₂' v₁ v₂ := by
  cases hval with
  | objRef _ hlook₁ =>
      exact .objRef hheap' (hleft _ _ hlook₁)

theorem checkedEnvPrecision_transport_heap
    (hheap' : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂')
    (hleft : ∀ oid obj, heap₁.lookup oid = some obj → heap₁'.lookup oid = some obj)
    (henv : CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ env₁ env₂) :
    CheckedEnvPrecision gct₁ gct₂ cct₁ cct₂ heap₁' heap₂' env₁ env₂ := by
  induction henv with
  | nil => exact .nil
  | cons hval _ ih =>
      exact .cons (checkedValuePrecision_transport_heap hheap' hleft hval) ih

theorem checkedFramePrecision_transport_heap
    (hheap' : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂')
    (hleft : ∀ oid obj, heap₁.lookup oid = some obj → heap₁'.lookup oid = some obj)
    (hframe : CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ f₁ f₂) :
    CheckedFramePrecision gct₁ gct₂ cct₁ cct₂ heap₁' heap₂' f₁ f₂ := by
  cases hframe with
  | attrAccess => exact .attrAccess
  | callCallee harg hparam hret => exact .callCallee harg hparam hret
  | callValue harg hparam hret =>
      exact .callValue (checkedValuePrecision_transport_heap hheap' hleft harg) hparam hret
  | awaitArgument hmeth hret => exact .awaitArgument hmeth hret
  | cond hthen helse => exact .cond hthen helse
  | returnTo henv => exact .returnTo (checkedEnvPrecision_transport_heap hheap' hleft henv)
  | enforce hboundary => exact .enforce hboundary
  | dynAttrAccess => exact .dynAttrAccess

theorem checkedContinuationPrecision_transport_heap
    (hheap' : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂')
    (hleft : ∀ oid obj, heap₁.lookup oid = some obj → heap₁'.lookup oid = some obj)
    (hcont : CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ k₁ k₂) :
    CheckedContinuationPrecision gct₁ gct₂ cct₁ cct₂ heap₁' heap₂' k₁ k₂ := by
  induction hcont with
  | nil => exact .nil
  | cons hframe _ ih =>
      exact .cons (checkedFramePrecision_transport_heap hheap' hleft hframe) ih

private theorem wellFormedGTy_checkedTargetPrecision
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hprec : CheckedTargetPrecision T₁ T₂)
    (hwf : WellFormedGTy gct₁ (interpTarget T₁)) :
    WellFormedGTy gct₂ (interpTarget T₂) := by
  induction hprec with
  | refl =>
      exact wellFormedGTy_transport hct hwf
  | toAny =>
      exact .any
  | callable _ _ ihP ihR =>
      let .callable hwfP hwfR := hwf
      exact .callable (ihP hwfP) (ihR hwfR)
  | union _ _ ihG ihH =>
      let .union hwfG hwfH := hwf
      exact .union (ihG hwfG) (ihH hwfH)
  | intersection _ _ ihG ihH =>
      let .intersection hwfG hwfH := hwf
      exact .intersection (ihG hwfG) (ihH hwfH)

private theorem checkedValueSatisfies_compileTargetPrecision
    (hprec : CompileTargetPrecision T₁ T₂)
    (hsat : CheckedValueSatisfies gct cct heap v T₁) :
    CheckedValueSatisfies gct cct heap v T₂ := by
  induction hprec generalizing v with
  | refl =>
      exact hsat
  | toAny =>
      exact checkedValueSatisfies_toAnyShape hsat
  | callable _ _ =>
      simpa [CheckedValueSatisfies] using hsat
  | union _ _ ihLeft ihRight =>
      rcases hsat with hsatLeft | hsatRight
      · exact Or.inl (ihLeft hsatLeft)
      · exact Or.inr (ihRight hsatRight)
  | intersection _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat.1, ihRight hsat.2⟩
  | fromBottom =>
      cases hsat
  | intersection_left_toAny _ _ _ ihRight =>
      exact ihRight hsat.2
  | intersection_right_toAny _ _ ihLeft _ =>
      exact ihLeft hsat.1
  | meet _ _ ihLeft ihRight =>
      exact ⟨ihLeft hsat, ihRight hsat⟩

theorem checkedValuePrecision_transport_checkedTarget
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hheapwf₂ : CheckedHeapWellFormed gct₂ cct₂ heap₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (w₁ : CheckedValueWitness gct₁ cct₁ heap₁ v₁ (interpTarget T₁))
    (hprec : CheckedTargetPrecision T₁ T₂) :
    CheckedValueWitness gct₂ cct₂ heap₂ v₂ (interpTarget T₂) := by
  have w₂same :
      CheckedValueWitness gct₂ cct₂ heap₂ v₂ (interpTarget T₁) :=
    checkedValueWitness_transport_refl hct hheapwf₂ hval w₁
  have hsat₂ :
      CheckedValueSatisfies gct₂ cct₂ heap₂ v₂ T₁ :=
    checkedValueWitness_satisfies w₂same
  have hsat₂' :
      CheckedValueSatisfies gct₂ cct₂ heap₂ v₂ T₂ :=
    checkedValueSatisfies_precision hprec hsat₂
  exact checkedValueSatisfies_toWitness hheapwf₂
    (wellFormedGTy_checkedTargetPrecision hct hprec w₁.wf)
    hsat₂'

theorem checkedValuePrecision_transport_compileTarget
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hheapwf₂ : CheckedHeapWellFormed gct₂ cct₂ heap₂)
    (hval : CheckedValuePrecision gct₁ gct₂ cct₁ cct₂ heap₁ heap₂ v₁ v₂)
    (w₁ : CheckedValueWitness gct₁ cct₁ heap₁ v₁ (interpTarget T₁))
    (hprec : CompileTargetPrecision T₁ T₂)
    (hwf₂ : WellFormedGTy gct₂ (interpTarget T₂)) :
    CheckedValueWitness gct₂ cct₂ heap₂ v₂ (interpTarget T₂) := by
  have w₂same :
      CheckedValueWitness gct₂ cct₂ heap₂ v₂ (interpTarget T₁) :=
    checkedValueWitness_transport_refl hct hheapwf₂ hval w₁
  have hsat₂ :
      CheckedValueSatisfies gct₂ cct₂ heap₂ v₂ T₁ :=
    checkedValueWitness_satisfies w₂same
  have hsat₂' :
      CheckedValueSatisfies gct₂ cct₂ heap₂ v₂ T₂ :=
    checkedValueSatisfies_compileTargetPrecision hprec hsat₂
  exact checkedValueSatisfies_toWitness hheapwf₂ hwf₂ hsat₂'

private theorem alloc_heap_precision_aux
    (hprec : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁ heap₂)
    (hobj : ∀ o, CheckedHeapObjectPrecision gct₁ cct₁ cct₂ o newObj₁ newObj₂)
    (halloc₁ : heap₁.alloc newObj₁ = (oid, heap₁'))
    (halloc₂ : heap₂.alloc newObj₂ = (oid, heap₂')) :
    CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj halloc₁
  obtain ⟨hcounter₂, rfl⟩ := Prod.mk.inj halloc₂
  refine ⟨by simp [CheckedHeap.heapCounter, hcounter₂], ?_, ?_⟩
  · intro oid' obj₁ hlook₁
    unfold CheckedHeap.lookup at hlook₁
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook₁
    split at hlook₁
    · rename_i heq₁
      cases hlook₁
      have heq₁' : oid' = heap₁.heapCounter := by
        exact heq₁.symm
      have heq₂ : oid' = heap₂.heapCounter :=
        heq₁'.trans hcounter₂.symm
      exact ⟨newObj₂, by
        unfold CheckedHeap.lookup RuntimeHeap.lookup RuntimeHeap.lookupList
        rw [heq₂]
        rw [if_pos rfl]
      , hobj _⟩
    · rename_i hneq₁
      rcases hprec.lookup_prec_left oid' _ hlook₁ with ⟨obj₂, hlook₂, hobjprec⟩
      have hneq₁' : oid' ≠ heap₁.heapCounter := by
        intro hEq
        exact hneq₁ hEq.symm
      have hneq₂ : oid' ≠ heap₂.heapCounter := by
        intro hEq
        exact hneq₁' (hEq.trans hcounter₂)
      have hlook₂' : RuntimeHeap.lookupList oid' heap₂.heapMap = some obj₂ := by
        simpa [CheckedHeap.lookup, RuntimeHeap.lookup] using hlook₂
      exact ⟨obj₂, by
        unfold CheckedHeap.lookup RuntimeHeap.lookup RuntimeHeap.lookupList
        rw [if_neg (fun hEq => hneq₂ hEq.symm)]
        exact hlook₂'
      , hobjprec⟩
  · intro oid' obj₂ hlook₂
    unfold CheckedHeap.lookup at hlook₂
    simp only [RuntimeHeap.lookup, RuntimeHeap.lookupList] at hlook₂
    split at hlook₂
    · rename_i heq₂
      cases hlook₂
      have heq₂' : oid' = heap₂.heapCounter := by
        exact heq₂.symm
      have heq₁ : oid' = heap₁.heapCounter :=
        heq₂'.trans hcounter₂
      exact ⟨newObj₁, by
        unfold CheckedHeap.lookup RuntimeHeap.lookup RuntimeHeap.lookupList
        rw [heq₁]
        rw [if_pos rfl]
      , hobj _⟩
    · rename_i hneq₂
      rcases hprec.lookup_prec_right oid' _ hlook₂ with ⟨obj₁, hlook₁, hobjprec⟩
      have hneq₂' : oid' ≠ heap₂.heapCounter := by
        intro hEq
        exact hneq₂ hEq.symm
      have hneq₁ : oid' ≠ heap₁.heapCounter := by
        intro hEq
        exact hneq₂' (hEq.trans hcounter₂.symm)
      have hlook₁' : RuntimeHeap.lookupList oid' heap₁.heapMap = some obj₁ := by
        simpa [CheckedHeap.lookup, RuntimeHeap.lookup] using hlook₁
      exact ⟨obj₁, by
        unfold CheckedHeap.lookup RuntimeHeap.lookup RuntimeHeap.lookupList
        rw [if_neg (fun hEq => hneq₁ hEq.symm)]
        exact hlook₁'
      , hobjprec⟩

theorem new_alloc_heap_precision
    (hprec : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁ heap₂)
    (hcname : cname₁ = cname₂)
    (halloc₁ : heap₁.alloc ⟨cname₁, .ordinary⟩ = (oid, heap₁'))
    (halloc₂ : heap₂.alloc ⟨cname₂, .ordinary⟩ = (oid, heap₂')) :
    CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂' := by
  cases hcname
  exact alloc_heap_precision_aux hprec (fun _ => .ordinary) halloc₁ halloc₂

theorem boundMethod_alloc_heap_precision
    (hprec : CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁ heap₂)
    (hmeth : CheckedMethodPrecision gct₁ m₁ m₂)
    (halloc₁ : heap₁.alloc ⟨boundMethodClass, .boundMethod recvOid m₁⟩ = (oid, heap₁'))
    (halloc₂ : heap₂.alloc ⟨boundMethodClass, .boundMethod recvOid m₂⟩ = (oid, heap₂')) :
    CheckedHeapPrecision gct₁ cct₁ cct₂ heap₁' heap₂' :=
  alloc_heap_precision_aux hprec (fun _ => .boundMethod hmeth) halloc₁ halloc₂

theorem initial_state_precision
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    CheckedStatePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes
      (initialState cp₁)
      (initialState cp₂) := by
  have hstatic := static_gradual_guarantee hgp helab₁ helab₂ hP
  refine ⟨checkedHeapInitial_precision gp₁.classes, .nil, ?_, .nil⟩
  exact .expr (by simpa [CheckedExprPrecision, initialState, expressionState, eraseLabelsProgram]
    using hstatic.main_prec)

theorem initial_state_precision_main_moreStatic
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    MoreStatic gp₂.classes helab₁.main_srcTy helab₂.main_srcTy ∧
    CheckedStatePrecision gp₁.classes gp₂.classes cp₁.classes cp₂.classes
      (initialState cp₁)
      (initialState cp₂) := by
  exact
    ⟨(static_gradual_guarantee_main_moreStatic hgp helab₁ helab₂ hP).1,
      initial_state_precision hgp helab₁ helab₂ hP⟩

theorem wellElaboratedState_initial
    (hcompiled : ElaboratesProgramAt gp P cp) :
    WellElaboratedState hcompiled (initialState cp) :=
  initialState_registered hcompiled

theorem wellElaboratedState_step
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hwell : WellElaboratedState hcompiled s)
    (hstep : Checked.Step gp.classes cp.classes s s') :
    WellElaboratedState hcompiled s' :=
  step_preserves_registered hcompiled hwell hstep

theorem wellElaboratedState_steps
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hwell : WellElaboratedState hcompiled s)
    (hsteps : Checked.Steps gp.classes cp.classes s s') :
    WellElaboratedState hcompiled s' :=
  steps_preserve_registered hcompiled hwell hsteps

theorem initial_state_elaborated_precision
    (hgp : ProgramTargetPrecision gp₁ gp₂)
    (helab₁ : ElaboratesProgramAt gp₁ P₁ cp₁)
    (helab₂ : ElaboratesProgramAt gp₂ P₂ cp₂)
    (hP : ProgramRootTargetInputPrecision P₁ P₂) :
    ElaboratedStatePrecision helab₁ helab₂
      (initialState cp₁)
      (initialState cp₂) := by
  refine ⟨initial_state_precision hgp helab₁ helab₂ hP, ?_, ?_⟩
  · exact wellElaboratedState_initial helab₁
  · exact wellElaboratedState_initial helab₂

end Checked

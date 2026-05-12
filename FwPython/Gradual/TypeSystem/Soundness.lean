import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.Preservation
import FwPython.Gradual.TypeSystem.Progress

/-! # End-to-end soundness for the target-relative gradual type system

If a gradual program has a `GSrcInfer` witness and an explicit expected
checked target `P`, the compiled checked program starts safe at
`runtimePublicTy P`. Any final result reached from that state is either a
successful value witnessing `runtimePublicTy P` or blame. Raw
`runtimeError` is ruled out. -/

namespace Checked

theorem compiled_initial_safe_at
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct cct)
    (hsrc : GSrcInfer gct hwfct [] e srcTy)
    (hPruntime : RuntimePublicAnnotation gct P)
    (hPwf : WellFormedGTy gct P)
    (n : Nat) :
    CheckedStateSafe gct cct CheckedHeap.initial []
      (.expr (compileCheck .main hsrc [] P n).1)
      []
      (runtimePublicTy P) := by
  refine ⟨[], [], runtimePublicTy P,
    hwfct,
    checkedHeapInitial_wellFormed hwfct.raw,
    halign,
    fun _ _ hlook => by simp [NamedEnv.lookup] at hlook,
    .expr ?_,
    .nil⟩
  exact elabCheck_checked .main hsrc
    (henv := by intro b hb; cases hb)
    (helab := .nil)
    hPruntime hPwf compileCheck_elaborates

theorem compiled_initial_safe_from_elaboration_at
    (hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedStateSafe gp.classes cp.classes
      (initialState cp).heap
      (initialState cp).env
      (initialState cp).control
      (initialState cp).continuation
      (runtimePublicTy P) := by
  refine ⟨[], [], runtimePublicTy P,
    hcompiled.hwfct,
    checkedHeapInitial_wellFormed hcompiled.hwfct.raw,
    alignedCheckedClassTable_of_compiled hcompiled.hwfct hcompiled.classes_elab,
    fun _ _ hlook => by simp [NamedEnv.lookup] at hlook,
    .expr ?_,
    .nil⟩
  simpa [initialState, expressionState] using
    (elabCheck_checked
      .main
      hcompiled.main_hsrc
      (henv := by intro b hb; cases hb)
      (helab := .nil)
      hcompiled.target_runtimePublic
      hcompiled.target_wf
      hcompiled.main_elabCheck)

theorem checked_safe_execution_result
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hsteps : Steps gct cct
      { heap, env, control := ctrl, continuation := cont }
      finalState)
    (hfinal : finalResult? finalState = some (heap', result)) :
    (∃ v, result = .success v ∧
      CheckedValueWitness gct cct heap' v expectedType) \/
    (∃ ℓ, result = .blame ℓ) := by
  obtain ⟨Γ, outΓ, G, _, hheap, _, henv, hctrl, hcont⟩ :=
    checked_preservation_multi hsafe hsteps
  simp only [finalResult?] at hfinal
  split at hfinal
  · obtain ⟨rfl, rfl⟩ := Option.some.inj hfinal
    cases hctrl with
    | val hvty => cases hcont with | nil => exact .inl ⟨_, rfl, hvty⟩
  · obtain ⟨rfl, rfl⟩ := Option.some.inj hfinal
    exact .inr ⟨_, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Option.some.inj hfinal
    cases hctrl
  · cases hfinal

theorem checked_safe_final_result
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hfinal : finalResult?
      { heap, env, control := ctrl, continuation := cont } = some (heap', result)) :
    (∃ v, result = .success v ∧
      CheckedValueWitness gct cct heap' v expectedType) \/
    (∃ ℓ, result = .blame ℓ) :=
  checked_safe_execution_result hsafe .refl hfinal

theorem checked_safe_execution_no_runtimeError
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hsteps : Steps gct cct
      { heap, env, control := ctrl, continuation := cont }
      finalState) :
    ∀ err, finalState.control ≠ .runtimeError err := by
  intro err hEq
  have hsafe' :=
    checked_preservation_multi hsafe hsteps
  exact hsafe'.not_runtimeError err hEq

theorem gradual_soundness_at
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Steps gp.classes cp.classes
      (initialState cp)
      finalState)
    (hfinal : finalResult? finalState = some (heap', result)) :
    (∃ v, result = .success v ∧
      CheckedValueWitness gp.classes cp.classes heap' v (runtimePublicTy P)) \/
    (∃ ℓ, result = .blame ℓ) :=
  checked_safe_execution_result
    (compiled_initial_safe_from_elaboration_at hcompiled) hsteps hfinal

end Checked

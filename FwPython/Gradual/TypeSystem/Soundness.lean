import FwPython.Gradual.TypeSystem.Source.Compile
import FwPython.Gradual.TypeSystem.ClassTable.Compile
import FwPython.Gradual.TypeSystem.Preservation
import FwPython.Gradual.TypeSystem.Progress

/-! # End-to-end soundness for the target-relative gradual type system

If a gradual program has a `GSrcInfer` witness and an explicit expected
checked target `P`, the compiled checked program starts safe at `P`. Any
final result reached from that state is either a successful value
witnessing `P` or blame. Raw `runtimeError` is ruled out. -/

namespace Checked

/-- A checked expression produced by source compilation at `site` starts in a
safe initial checked state when the checked class table is aligned. -/
theorem compiled_initial_safe_at
    (hwfct : WellFormedGClassTableCore gct)
    (halign : AlignedCheckedClassTable gct hwfct.toWellFormedClassHierarchy cct)
    (hsrc : GSrcInfer gct hwfct [] e srcTy)
    (hPruntime : CheckedTargetTy gct P)
    (hPwf : WellFormedGTy gct P)
    (site : SourceExpressionSite) :
    CheckedStateSafe gct cct CheckedHeap.initial []
      (.expr (compileCheck hsrc [] P site))
      []
      P := by
  refine ⟨[], [], P,
    hwfct,
    checkedHeapInitial_wellFormed hwfct.raw,
    halign,
    nofun,
    .expr (compileCheck_checked
      (helab := .nil)
      hwfct
      hPruntime hPwf hsrc site),
    .nil⟩

/-- A whole-program checked elaboration artifact starts in a safe initial
checked state at its requested target. -/
theorem compiled_initial_safe_from_elaboration_at
    (hcompiled : ElaboratesProgramAt gp P cp) :
    CheckedStateSafe gp.classes cp.classes
      (initialState cp).heap
      (initialState cp).env
      (initialState cp).control
      (initialState cp).continuation
      P := by
  refine ⟨[], [], P,
    hcompiled.hwfct,
    checkedHeapInitial_wellFormed hcompiled.hwfct.raw,
    alignedCheckedClassTable_of_compiled hcompiled.classes_elab,
    nofun,
    .expr ?_,
    .nil⟩
  exact hcompiled.main_eq ▸
    (compileCheck_checked
      (helab := .nil)
      hcompiled.hwfct
      hcompiled.target_checkedTarget
      hcompiled.target_wf
      hcompiled.main_hsrc
      (.main []))

theorem checked_safe_execution_result
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hsteps : Steps gct cct
      { heap, env, control := ctrl, continuation := cont }
      finalState)
    (hfinal : finalResult? finalState = some (heap', result)) :
    (∃ v, result = .success v ∧
      CheckedValueWitness gct cct heap' v expectedType) \/
    (∃ info, result = .blame info) := by
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
    (∃ info, result = .blame info) :=
  checked_safe_execution_result hsafe .refl hfinal

theorem checked_safe_execution_no_runtimeError
    (hsafe : CheckedStateSafe gct cct heap env ctrl cont expectedType)
    (hsteps : Steps gct cct
      { heap, env, control := ctrl, continuation := cont }
      finalState) :
    ∀ err, finalState.control ≠ .runtimeError err :=
  (checked_preservation_multi hsafe hsteps).not_runtimeError

theorem gradual_soundness_at
    (hcompiled : ElaboratesProgramAt gp P cp)
    (hsteps : Steps gp.classes cp.classes
      (initialState cp)
      finalState)
    (hfinal : finalResult? finalState = some (heap', result)) :
    (∃ v, result = .success v ∧
      CheckedValueWitness gp.classes cp.classes heap' v P) \/
    (∃ info, result = .blame info) :=
  checked_safe_execution_result
    (compiled_initial_safe_from_elaboration_at hcompiled) hsteps hfinal

end Checked

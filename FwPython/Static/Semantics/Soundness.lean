import FwPython.Static.Semantics.Progress
import FwPython.Static.Semantics.Preservation
import FwPython.Static.Semantics.MultiStep

/-! # Soundness

A well-typed initial expression state can only terminate in a successful
value of the claimed type. -/

variable {ct : ClassTable}

namespace SmallStep

/-- A safe final state must end in a value (not a runtime error),
    and that value has the expected type. -/
theorem safe_final_is_success
    (_hwf : WellTypedClassHierarchy ct)
    (hsafe : StateSafe _hwf.toWellFormedClassHierarchy heap env ctrl [] expectedType)
    (hfinal : finalResult? { heap, env, control := ctrl, continuation := [] } = some (heap', result)) :
    ∃ v, result = .success v ∧ ValueHasType _hwf.toWellFormedClassHierarchy heap' v expectedType := by
  obtain ⟨Γ, outΓ, T, hheap, henv, hctrl, hcont⟩ := hsafe
  cases hcont
  cases hctrl with
  | expr htype => simp [finalResult?] at hfinal
  | val hval =>
    simp [finalResult?] at hfinal
    obtain ⟨rfl, rfl⟩ := hfinal
    exact ⟨_, rfl, hval⟩

/-- **Soundness**: well-typed programs do not get stuck.
    If we start from a well-typed expression state and reach a final state,
    the result is a successful value of the claimed type. -/
theorem soundness
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy h env Γ)
    (htype : HasType hwf.toWellFormedClassHierarchy Γ e T)
    (hexec : evaluatesFrom ct h env e h' result) :
    ∃ v, result = .success v ∧ ValueHasType hwf.toWellFormedClassHierarchy h' v T := by
  obtain ⟨finalState, hsteps, hfinal⟩ := hexec
  -- Build the initial StateSafe for the expression state
  have hsafe₀ : StateSafe hwf.toWellFormedClassHierarchy h env (.expr e) [] T :=
    ⟨Γ, Γ, T, hheap, henv, .expr htype, .nil⟩
  -- Destructure the final state
  obtain ⟨fh, fe, fc, fk⟩ := finalState
  -- Unfold expressionState so the Steps goal matches preservation_multi's signature
  unfold expressionState at hsteps
  -- Apply multi-step preservation to obtain safety of the final state
  have hsafe_final := preservation_multi hwf hsafe₀ hsteps
  -- The final state must have an empty continuation (finalResult? ≠ none)
  cases fk with
  | cons f rest =>
    simp [finalResult_none_of_nonempty_continuation] at hfinal
  | nil =>
    exact safe_final_is_success hwf hsafe_final hfinal

/-- A closed, well-typed program that terminates returns a value of its main type.
The initial heap requirements follow from the class table. -/
theorem program_soundness (hwf : WellTypedClassHierarchy p.classes)
    (typing : HasType hwf.toWellFormedClassHierarchy [] p.main T)
    (execution : programExecute p result) :
    ∃ heap value, result = .success value ∧ ValueHasType hwf.toWellFormedClassHierarchy heap value T := by
  obtain ⟨state, heap, steps, final⟩ := execution
  have execution : evaluatesFrom p.classes Heap.initial [] p.main heap result :=
    ⟨state, steps, final⟩
  have env : EnvHasType hwf.toWellFormedClassHierarchy Heap.initial [] [] := by
    intro name type lookup
    cases lookup
  obtain ⟨value, success, valueTyping⟩ :=
    soundness hwf (Heap.initial_wellFormed hwf) env typing execution
  exact ⟨heap, value, success, valueTyping⟩

end SmallStep

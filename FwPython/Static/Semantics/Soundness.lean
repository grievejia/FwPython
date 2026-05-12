import FwPython.Static.Semantics.Progress
import FwPython.Static.Semantics.Preservation
import FwPython.Static.Semantics.MultiStep

/-! # Soundness

A well-typed initial expression state can only terminate in a successful
value of the claimed type. -/

namespace SmallStep

/-- A safe final state must end in a value (not a runtime error),
    and that value has the expected type. -/
theorem safe_final_is_success
    (_hwf : WellFormedClassTable ct)
    (hsafe : StateSafe ct heap env ctrl [] expectedType)
    (hfinal : finalResult? { heap, env, control := ctrl, continuation := [] } = some (heap', result)) :
    ∃ v, result = .success v ∧ ValueHasType ct heap' v expectedType := by
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
    (hwf : WellFormedClassTable ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType ct h env Γ)
    (htype : HasType ct Γ e T)
    (hexec : evaluatesFrom ct h env e h' result) :
    ∃ v, result = .success v ∧ ValueHasType ct h' v T := by
  obtain ⟨finalState, hsteps, hfinal⟩ := hexec
  -- Build the initial StateSafe for the expression state
  have hsafe₀ : StateSafe ct h env (.expr e) [] T :=
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

end SmallStep

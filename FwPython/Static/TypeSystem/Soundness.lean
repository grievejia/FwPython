import FwPython.Static.Semantics.Soundness

/-! ## Soundness

The small-step soundness theorem, re-exported as the public interface. -/

variable {ct : ClassTable}

/-- **Soundness**: well-typed programs do not get stuck.
    If we start from a well-typed expression state and reach a final state,
    the result is a successful value of the claimed type. -/
theorem soundness
    (hwf : WellTypedClassHierarchy ct)
    (hheap : HeapWellFormed ct h)
    (henv : EnvHasType hwf.toWellFormedClassHierarchy h env Γ)
    (htype : HasType hwf.toWellFormedClassHierarchy Γ e T)
    (hexec : SmallStep.evaluatesFrom ct h env e h' result) :
    ∃ v, result = .success v ∧ ValueHasType hwf.toWellFormedClassHierarchy h' v T :=
  SmallStep.soundness hwf hheap henv htype hexec

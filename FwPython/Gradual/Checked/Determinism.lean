import FwPython.Gradual.Checked.MultiStep
import FwPython.Gradual.Checked.Enforce

/-! # Determinism of the Checked Small-Step Machine

Proves that the one-step reduction relation `Checked.Step` is deterministic. -/

namespace Checked

private theorem payload_absurd
    {hp : CheckedHeap} {oid : Nat} {c₁ c₂ : Identifier} {r : Nat} {m : CheckedMethod}
    (h1 : hp.lookup oid = some ⟨c₁, .boundMethod r m⟩)
    (h2 : hp.lookup oid = some ⟨c₂, .ordinary⟩) : False :=
  CheckedObjectPayload.noConfusion
    (congrArg CheckedHeapObject.payload (Option.some.inj (h1.symm.trans h2)))

/-- The one-step reduction relation is deterministic. -/
theorem step_deterministic :
    Step ct cct s s₁ → Step ct cct s s₂ → s₁ = s₂ := by
  intro h1 h2
  cases h1 with
  -- Focus rules
  | focusAttrAccess | focusCall | focusEnforce | focusDynAttrAccess
  | constNone | constTrue | constFalse | returnFromBody =>
      cases h2; rfl
  | focusCond hne₁ =>
      cases h2 with
      | focusCond => rfl
      | condIsInstanceTrue | condIsInstanceFalse | condIsInstanceVarNotFound =>
          exact absurd rfl (hne₁ _ _)
  | condIsInstanceTrue henv₁ hlook₁ hfind₁ hmro₁ hmem₁ =>
      cases h2 with
      | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
      | condIsInstanceTrue => rfl
      | condIsInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ hnotmem₂ =>
          simp [henv₁] at henv₂; subst henv₂
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro₁ hmro₂ ▸ hmem₁) hnotmem₂
      | condIsInstanceVarNotFound henv₂ => simp [henv₁] at henv₂
  | condIsInstanceFalse henv₁ hlook₁ hfind₁ hmro₁ hnotmem₁ =>
      cases h2 with
      | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
      | condIsInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ hmem₂ =>
          simp [henv₁] at henv₂; subst henv₂
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro₁ hmro₂ ▸ hmem₂) hnotmem₁
      | condIsInstanceFalse => rfl
      | condIsInstanceVarNotFound henv₂ => simp [henv₁] at henv₂
  | condIsInstanceVarNotFound henv₁ =>
      cases h2 with
      | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
      | condIsInstanceTrue henv₂ | condIsInstanceFalse henv₂ => simp [henv₁] at henv₂
      | condIsInstanceVarNotFound => rfl
  -- Atomic evaluation
  | varSuccess hlook₁ =>
      cases h2 with
      | varSuccess hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂; rfl
      | varError hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂
  | varError hlook₁ =>
      cases h2 with
      | varSuccess hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂
      | varError => rfl
  | newSuccess hfind₁ hnb₁ hnn₁ hnbm₁ halloc₁ =>
      cases h2 with
      | newSuccess _ _ _ _ halloc₂ => rw [halloc₁] at halloc₂; cases halloc₂; rfl
      | newClassNotFound hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
      | newBuiltinError _ hbuiltin₂ =>
          rcases hbuiltin₂ with rfl | rfl | rfl <;> contradiction
  | newClassNotFound hfind₁ =>
      cases h2 with
      | newSuccess hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
      | newClassNotFound => rfl
      | newBuiltinError hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
  | newBuiltinError hfind₁ hbuiltin₁ =>
      cases h2 with
      | newSuccess _ hnb₂ hnn₂ hnbm₂ =>
          rw [hfind₁] at *
          rcases hbuiltin₁ with rfl | rfl | rfl <;> contradiction
      | newClassNotFound hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
      | newBuiltinError => rfl
  | isInstanceTrue henv₁ hlook₁ hfind₁ hmro₁ hmem₁ =>
      cases h2 with
      | isInstanceTrue => rfl
      | isInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ hnotmem₂ =>
          rw [henv₁] at henv₂; cases henv₂
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro₁ hmro₂ ▸ hmem₁) hnotmem₂
      | isInstanceVarNotFound henv₂ => simp [henv₁] at henv₂
  | isInstanceFalse henv₁ hlook₁ hfind₁ hmro₁ hnotmem₁ =>
      cases h2 with
      | isInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ hmem₂ =>
          rw [henv₁] at henv₂; cases henv₂
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro₁ hmro₂ ▸ hmem₂) hnotmem₁
      | isInstanceFalse => rfl
      | isInstanceVarNotFound henv₂ => simp [henv₁] at henv₂
  | isInstanceVarNotFound henv₁ =>
      cases h2 with
      | isInstanceTrue henv₂ | isInstanceFalse henv₂ => simp [henv₁] at henv₂
      | isInstanceVarNotFound => rfl
  -- Return: attribute access
  | returnAttrAccess hlook₁ hfind₁ hmro₁ hmethod₁ halloc₁ =>
      cases h2 with
      | returnAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ halloc₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
          rw [halloc₁] at halloc₂; cases halloc₂; rfl
      | returnAttrAccessNotFound hlook₂ hfind₂ hmro₂ hmethod₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
  | returnAttrAccessNotFound hlook₁ hfind₁ hmro₁ hmethod₁ =>
      cases h2 with
      | returnAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
      | returnAttrAccessNotFound hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂; rfl
  -- Return: dynamic attribute access
  | returnDynAttrAccess hlook₁ hfind₁ hmro₁ hmethod₁ halloc₁ =>
      cases h2 with
      | returnDynAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ halloc₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
          rw [halloc₁] at halloc₂; cases halloc₂; rfl
      | returnDynAttrAccessNotFound hlook₂ hfind₂ hmro₂ hmethod₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
  | returnDynAttrAccessNotFound hlook₁ hfind₁ hmro₁ hmethod₁ =>
      cases h2 with
      | returnDynAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ =>
          rw [hlook₁] at hlook₂; cases hlook₂
          rw [hfind₁] at hfind₂; cases hfind₂
          rw [gComputeMro_determinism hmro₁ hmro₂] at hmethod₁
          rw [hmethod₁] at hmethod₂; cases hmethod₂
      | returnDynAttrAccessNotFound => rfl
  -- Return: call callee
  | returnCallCalleeBound hlook₁ =>
      cases h2 with
      | returnCallCalleeBound hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂; rfl
      | returnCallCalleeNotCallable hlook₂ => exact (payload_absurd hlook₁ hlook₂).elim
  | returnCallCalleeNotCallable hlook₁ =>
      cases h2 with
      | returnCallCalleeBound hlook₂ => exact (payload_absurd hlook₂ hlook₁).elim
      | returnCallCalleeNotCallable => rfl
  -- Return: await argument
  | returnAwaitArgumentOk henf₁ =>
      cases h2 with
      | returnAwaitArgumentOk henf₂ => cases enforceValue_deterministic henf₁ henf₂; rfl
      | returnAwaitArgumentBlame henf₂ => cases enforceValue_deterministic henf₁ henf₂
  | returnAwaitArgumentBlame henf₁ =>
      cases h2 with
      | returnAwaitArgumentOk henf₂ => cases enforceValue_deterministic henf₁ henf₂
      | returnAwaitArgumentBlame => rfl
  -- Return: call value
  | returnCallValueBound hlook₁ =>
      cases h2 with
      | returnCallValueBound hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂; rfl
      | returnCallValueNotCallable hlook₂ => exact (payload_absurd hlook₁ hlook₂).elim
  | returnCallValueNotCallable hlook₁ =>
      cases h2 with
      | returnCallValueBound hlook₂ => exact (payload_absurd hlook₂ hlook₁).elim
      | returnCallValueNotCallable => rfl
  -- Return: enforce expression
  | returnEnforceOk henf₁ =>
      cases h2 with
      | returnEnforceOk henf₂ => cases enforceValue_deterministic henf₁ henf₂; rfl
      | returnEnforceBlame henf₂ => cases enforceValue_deterministic henf₁ henf₂
  | returnEnforceBlame henf₁ =>
      cases h2 with
      | returnEnforceOk henf₂ => cases enforceValue_deterministic henf₁ henf₂
      | returnEnforceBlame => rfl
  -- Return: conditionals
  | returnCondTrue =>
      cases h2 with
      | returnCondTrue => rfl
      | returnCondNotBool hne₁ => exact absurd rfl hne₁
  | returnCondFalse =>
      cases h2 with
      | returnCondFalse => rfl
      | returnCondNotBool _ hne₂ => exact absurd rfl hne₂
  | returnCondNotBool hne₁ hne₂ =>
      cases h2 with
      | returnCondTrue => exact absurd rfl hne₁
      | returnCondFalse => exact absurd rfl hne₂
      | returnCondNotBool => rfl
  -- Blame propagation
  | blameUnwindAttrAccess | blameUnwindCallCallee | blameUnwindAwaitArgument
  | blameUnwindCallValue | blameUnwindCond | blameUnwindReturnTo
  | blameUnwindEnforce | blameUnwindDynAttrAccess =>
      cases h2; rfl
  -- Error propagation
  | errorUnwindAttrAccess | errorUnwindCallCallee | errorUnwindAwaitArgument
  | errorUnwindCallValue | errorUnwindCond | errorUnwindReturnTo
  | errorUnwindEnforce | errorUnwindDynAttrAccess =>
      cases h2; rfl

theorem steps_final_eq
    (hsteps₁ : Steps ct cct init s₁)
    (hfinal₁ : ∃ r, finalResult? s₁ = some r)
    (hsteps₂ : Steps ct cct init s₂)
    (hfinal₂ : ∃ r, finalResult? s₂ = some r) :
    s₁ = s₂ := by
  obtain ⟨_, hfinal₁⟩ := hfinal₁
  revert s₂
  induction hsteps₁ with
  | refl =>
      intro s₂ hsteps₂ _
      cases hsteps₂ with
      | refl => rfl
      | step hs _ => exact (final_states_do_not_step hfinal₁ hs).elim
  | step hs₁ _ ih =>
      intro s₂ hsteps₂ hfinal₂
      obtain ⟨_, hfinal₂⟩ := hfinal₂
      cases hsteps₂ with
      | refl => exact (final_states_do_not_step hfinal₂ hs₁).elim
      | step hs₂ hrest₂ =>
          have := step_deterministic hs₁ hs₂
          subst this
          exact ih hfinal₁ hrest₂ ⟨_, hfinal₂⟩

/-- Multi-step execution to a final state is deterministic. -/
theorem evaluatesFrom_deterministic
    (h1 : evaluatesFrom ct cct heap env expr heap₁ result₁)
    (h2 : evaluatesFrom ct cct heap env expr heap₂ result₂) :
    heap₁ = heap₂ ∧ result₁ = result₂ := by
  obtain ⟨s₁, hsteps₁, hfinal₁⟩ := h1
  obtain ⟨s₂, hsteps₂, hfinal₂⟩ := h2
  have := steps_final_eq hsteps₁ ⟨_, hfinal₁⟩ hsteps₂ ⟨_, hfinal₂⟩
  subst this
  rw [hfinal₁] at hfinal₂
  cases hfinal₂
  exact ⟨rfl, rfl⟩

end Checked

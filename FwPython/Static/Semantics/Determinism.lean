import FwPython.Static.Semantics.Core
import FwPython.Static.Semantics.Heap

/-! # Determinism of the Small-Step Continuation Machine

This file proves that the one-step reduction relation `Step` is deterministic:
if a state can step to two states, those states are equal. It also proves that
final states (empty continuation with a value or error) are irreducible. -/

namespace SmallStep

/-! ## Determinism -/

/-- The one-step reduction relation is deterministic. -/
theorem step_deterministic :
    Step ct s s₁ → Step ct s s₂ → s₁ = s₂ := by
  intro h1 h2
  cases h1 with
  -- Expression-focus rules: these decompose compound expressions
  | focusAttrAccess => cases h2 with | focusAttrAccess => rfl
  | focusCall => cases h2 with | focusCall => rfl
  | focusCond hne₁ =>
    cases h2 with
    | focusCond => rfl
    | condIsInstanceTrue => exact absurd rfl (hne₁ _ _)
    | condIsInstanceFalse => exact absurd rfl (hne₁ _ _)
    | condIsInstanceVarNotFound => exact absurd rfl (hne₁ _ _)
  | condIsInstanceTrue henv₁ hlook₁ hfind₁ hmro₁ hmem₁ =>
    cases h2 with
    | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
    | condIsInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ => rfl
    | condIsInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ hnotmem₂ =>
      rw [henv₁] at henv₂; cases henv₂
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      exact absurd (determinism hmro₁ hmro₂ ▸ hmem₁) hnotmem₂
    | condIsInstanceVarNotFound henv₂ => rw [henv₁] at henv₂; cases henv₂
  | condIsInstanceFalse henv₁ hlook₁ hfind₁ hmro₁ hnotmem₁ =>
    cases h2 with
    | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
    | condIsInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ hmem₂ =>
      rw [henv₁] at henv₂; cases henv₂
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      exact absurd (determinism hmro₁ hmro₂ ▸ hmem₂) hnotmem₁
    | condIsInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ => rfl
    | condIsInstanceVarNotFound henv₂ => rw [henv₁] at henv₂; cases henv₂
  | condIsInstanceVarNotFound henv₁ =>
    cases h2 with
    | focusCond hne₂ => exact absurd rfl (hne₂ _ _)
    | condIsInstanceTrue henv₂ => rw [henv₁] at henv₂; cases henv₂
    | condIsInstanceFalse henv₂ => rw [henv₁] at henv₂; cases henv₂
    | condIsInstanceVarNotFound => rfl
  -- Variable lookup
  | varSuccess hlook₁ =>
    cases h2 with
    | varSuccess hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂; rfl
    | varError hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂
  | varError hlook₁ =>
    cases h2 with
    | varSuccess hlook₂ => rw [hlook₁] at hlook₂; cases hlook₂
    | varError => rfl
  -- Object creation
  | newSuccess hfind₁ hnb₁ hnn₁ hnbm₁ halloc₁ =>
    cases h2 with
    | newSuccess hfind₂ _ _ _ halloc₂ =>
      rw [halloc₁] at halloc₂; cases halloc₂; rfl
    | newClassNotFound hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
    | newBuiltinError hfind₂ hbuiltin₂ =>
      rcases hbuiltin₂ with rfl | rfl | rfl <;> contradiction
  | newClassNotFound hfind₁ =>
    cases h2 with
    | newSuccess hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
    | newClassNotFound => rfl
    | newBuiltinError hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
  | newBuiltinError hfind₁ hbuiltin₁ =>
    cases h2 with
    | newSuccess hfind₂ hnb₂ hnn₂ hnbm₂ =>
      rw [hfind₁] at hfind₂; cases hfind₂
      rcases hbuiltin₁ with rfl | rfl | rfl <;> contradiction
    | newClassNotFound hfind₂ => rw [hfind₁] at hfind₂; cases hfind₂
    | newBuiltinError hfind₂ hbuiltin₂ =>
      rfl
  -- Constants
  | constNone => cases h2 with | constNone => rfl
  | constTrue => cases h2 with | constTrue => rfl
  | constFalse => cases h2 with | constFalse => rfl
  -- isinstance
  | isInstanceTrue henv₁ hlook₁ hfind₁ hmro₁ hmem₁ =>
    cases h2 with
    | isInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ => rfl
    | isInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ hnotmem₂ =>
      rw [henv₁] at henv₂; cases henv₂
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      exact absurd (determinism hmro₁ hmro₂ ▸ hmem₁) hnotmem₂
    | isInstanceVarNotFound henv₂ => rw [henv₁] at henv₂; cases henv₂
  | isInstanceFalse henv₁ hlook₁ hfind₁ hmro₁ hnotmem₁ =>
    cases h2 with
    | isInstanceTrue henv₂ hlook₂ hfind₂ hmro₂ hmem₂ =>
      rw [henv₁] at henv₂; cases henv₂
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      exact absurd (determinism hmro₁ hmro₂ ▸ hmem₂) hnotmem₁
    | isInstanceFalse henv₂ hlook₂ hfind₂ hmro₂ => rfl
    | isInstanceVarNotFound henv₂ => rw [henv₁] at henv₂; cases henv₂
  | isInstanceVarNotFound henv₁ =>
    cases h2 with
    | isInstanceTrue henv₂ => rw [henv₁] at henv₂; cases henv₂
    | isInstanceFalse henv₂ => rw [henv₁] at henv₂; cases henv₂
    | isInstanceVarNotFound => rfl
  -- Return from attribute access
  | returnAttrAccess hlook₁ hfind₁ hmro₁ hmethod₁ halloc₁ =>
    cases h2 with
    | returnAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ halloc₂ =>
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      rw [determinism hmro₁ hmro₂] at hmethod₁
      rw [hmethod₁] at hmethod₂; cases hmethod₂
      rw [halloc₁] at halloc₂; cases halloc₂; rfl
    | returnAttrAccessNotFound hlook₂ hfind₂ hmro₂ hmethod₂ =>
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      rw [determinism hmro₁ hmro₂] at hmethod₁
      rw [hmethod₁] at hmethod₂; cases hmethod₂
  | returnAttrAccessNotFound hlook₁ hfind₁ hmro₁ hmethod₁ =>
    cases h2 with
    | returnAttrAccess hlook₂ hfind₂ hmro₂ hmethod₂ =>
      rw [hlook₁] at hlook₂; cases hlook₂
      rw [hfind₁] at hfind₂; cases hfind₂
      rw [determinism hmro₁ hmro₂] at hmethod₁
      rw [hmethod₁] at hmethod₂; cases hmethod₂
    | returnAttrAccessNotFound hlook₂ hfind₂ hmro₂ hmethod₂ =>
      rw [hlook₁] at hlook₂; cases hlook₂; rfl
  -- Return from call callee evaluation
  | returnCallCallee hlook₁ =>
    cases h2 with
    | returnCallCallee hlook₂ =>
      have ⟨_, rfl, rfl⟩ := unify_payload hlook₁ hlook₂; rfl
    | returnCallNotInvokable hlook₂ =>
      exact False.elim (payload_absurd hlook₁ hlook₂)
  | returnCallNotInvokable hlook₁ =>
    cases h2 with
    | returnCallCallee hlook₂ =>
      exact False.elim (payload_absurd hlook₂ hlook₁)
    | returnCallNotInvokable => rfl
  -- Return from argument evaluation (await argument)
  | returnAwaitArgument => cases h2 with | returnAwaitArgument => rfl
  -- Conditional returns
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
  -- Return from body
  | returnFromBody => cases h2 with | returnFromBody => rfl
  -- Error unwinding
  | errorUnwindAttrAccess => cases h2 with | errorUnwindAttrAccess => rfl
  | errorUnwindCallCallee => cases h2 with | errorUnwindCallCallee => rfl
  | errorUnwindAwaitArgument => cases h2 with | errorUnwindAwaitArgument => rfl
  | errorUnwindCond => cases h2 with | errorUnwindCond => rfl
  | errorUnwindReturnTo => cases h2 with | errorUnwindReturnTo => rfl

end SmallStep

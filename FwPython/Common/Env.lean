import FwPython.Common.Identifier

/-! # Shared named environments -/

/-- Shared association-list environment shape keyed by `Identifier`. -/
abbrev NamedEnv (α : Type) := List (Identifier × α)

/-- Look up the first binding for key `k` in an association list. -/
def NamedEnv.lookup : NamedEnv α → Identifier → Option α
  | [], _ => none
  | (k', v') :: rest, k =>
      if k' = k then
        some v'
      else
        lookup rest k

/-- Replace the first entry for key `k` in an association list with value `v`.
    Only the first match is replaced; shadowed bindings are left untouched. -/
def NamedEnv.update : NamedEnv α → Identifier → α → NamedEnv α
  | [], _, _ => []
  | (k', v') :: rest, k, v =>
    if k' = k then (k', v) :: rest
    else (k', v') :: update rest k v

theorem namedEnv_update_lookup_eq
    {Γ : NamedEnv α} {x : Identifier} (S : α)
    (hx : ∃ T, Γ.lookup x = some T) :
    (Γ.update x S).lookup x = some S := by
  induction Γ with
  | nil => simp [NamedEnv.lookup] at hx
  | cons p rest ih =>
    by_cases hpx : p.1 = x
    · subst hpx
      simp [NamedEnv.update, NamedEnv.lookup]
    · simp [NamedEnv.update, NamedEnv.lookup, hpx]
      exact ih (by simp [NamedEnv.lookup, hpx] at hx; exact hx)

theorem namedEnv_update_lookup_ne
    {Γ : NamedEnv α} {x y : Identifier} (S : α)
    (hne : y ≠ x) :
    (Γ.update x S).lookup y = Γ.lookup y := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 = x
    · subst hpx
      have hpy : p.1 ≠ y := by simpa using hne.symm
      simp [NamedEnv.update, NamedEnv.lookup, hpy]
    · simp [NamedEnv.update, NamedEnv.lookup, hpx]
      split
      · rfl
      · exact ih

/-- Updating twice at the same key keeps only the final update. -/
theorem namedEnv_update_shadow
    {Γ : NamedEnv α} {x : Identifier} {S T : α} :
    (Γ.update x S).update x T = Γ.update x T := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 = x
    · subst hpx
      simp [NamedEnv.update]
    · simp [NamedEnv.update, hpx, ih]

/-- Updates at distinct keys commute. -/
theorem namedEnv_update_commute
    {Γ : NamedEnv α} {x y : Identifier} {S T : α}
    (hne : x ≠ y) :
    (Γ.update x S).update y T = (Γ.update y T).update x S := by
  induction Γ with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 = x
    · subst hpx
      simp [NamedEnv.update, hne]
    · by_cases hpy : p.1 = y
      · subst hpy
        simp [NamedEnv.update, hpx]
      · simp [NamedEnv.update, hpx, hpy, ih]

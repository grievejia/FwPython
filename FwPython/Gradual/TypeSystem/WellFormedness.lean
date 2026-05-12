import FwPython.Gradual.TypeSystem.Context
import FwPython.Gradual.MRO.Compute
import FwPython.Gradual.TypeSystem.ClassTable.Transport

/-! ## Well-formedness of gradual types and type environments -/

/-- A gradual type is well-formed under a gradual class table if every class
    name it mentions exists in the class table and has a valid MRO.
    `any` is always well-formed (it represents the unknown fully static type). -/
inductive WellFormedGTy : GClassTable → GTy → Prop where
  | any : WellFormedGTy gct .any
  | bottom : WellFormedGTy gct .bottom
  | class_ :
      findGClass gct cname = some c →
      GComputeMro gct c mro →
      WellFormedGTy gct (.class_ cname)
  | callable :
      WellFormedGTy gct P →
      WellFormedGTy gct R →
      WellFormedGTy gct (.callable P R)
  | union :
      WellFormedGTy gct T →
      WellFormedGTy gct U →
      WellFormedGTy gct (.union T U)
  | intersection :
      WellFormedGTy gct T →
      WellFormedGTy gct U →
      WellFormedGTy gct (.intersection T U)
  | negClass :
      findGClass gct cname = some c →
      GComputeMro gct c mro →
      WellFormedGTy gct (.negClass cname)

/-- A gradual type environment is well-formed when every type in it is well-formed. -/
def WellFormedGTyEnv (gct : GClassTable) (Γ : GTyEnv) : Prop :=
  ∀ x G, Γ.lookup x = some G → WellFormedGTy gct G

/-! ## Type environment update helpers -/

theorem gTyEnv_update_lookup_eq
    {Γ : GTyEnv} {x : Identifier} (S : GTy)
    (hx : ∃ G, Γ.lookup x = some G) :
    (Γ.update x S).lookup x = some S :=
  namedEnv_update_lookup_eq S hx

theorem gTyEnv_update_lookup_ne
    {Γ : GTyEnv} {x y : Identifier} (S : GTy)
    (hne : y ≠ x) :
    (Γ.update x S).lookup y = Γ.lookup y :=
  namedEnv_update_lookup_ne S hne

/-- Overwrite: updating twice at the same key yields the last update. -/
theorem gTyEnv_update_overwrite
    {Γ : GTyEnv} {x : Identifier} (S T : GTy) :
    (Γ.update x S).update x T = Γ.update x T := by
  exact namedEnv_update_shadow

/-- Commutation: updates at different keys commute. -/
theorem gTyEnv_update_comm
    {Γ : GTyEnv} {x y : Identifier} (hne : x ≠ y) (S T : GTy) :
    (Γ.update x S).update y T = (Γ.update y T).update x S :=
  namedEnv_update_commute hne

/-- Updating a well-formed gradual type environment at a bound variable with a
    well-formed type preserves well-formedness. -/
theorem wellFormedGTyEnv_update
    (hΓwf : WellFormedGTyEnv gct Γ)
    (hlook : Γ.lookup x = some oldG)
    (hwfNew : WellFormedGTy gct newG) :
    WellFormedGTyEnv gct (Γ.update x newG) := by
  intro y G hlookΓ'
  by_cases hyx : y = x
  · subst hyx
    rw [gTyEnv_update_lookup_eq newG ⟨oldG, hlook⟩] at hlookΓ'
    cases hlookΓ'; exact hwfNew
  · rw [gTyEnv_update_lookup_ne newG hyx] at hlookΓ'
    exact hΓwf y G hlookΓ'

/-! ## Transport under class-table precision -/

theorem wellFormedGTy_transport
    (hct : ClassTableAnnotationPrecision gct₁ gct₂)
    (hwf : WellFormedGTy gct₁ G) :
    WellFormedGTy gct₂ G := by
  induction hwf with
  | any => exact .any
  | bottom => exact .bottom
  | class_ hfind hmro =>
    obtain ⟨_, hfind₂, hc⟩ := findGClass_precision hct hfind
    exact .class_ hfind₂ (gComputeMro_transport hct hc hmro)
  | callable _ _ ihP ihR => exact .callable ihP ihR
  | union _ _ ihT ihU => exact .union ihT ihU
  | intersection _ _ ihT ihU => exact .intersection ihT ihU
  | negClass hfind hmro =>
    obtain ⟨_, hfind₂, hc⟩ := findGClass_precision hct hfind
    exact .negClass hfind₂ (gComputeMro_transport hct hc hmro)

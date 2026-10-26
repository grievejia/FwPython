import FwPython.Gradual.Checked.Invariants
import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore

/-! ## EnforceValue theorems

Basic metatheory for the runtime enforcement relation: determinism, outcome
exclusivity, totality, and heap monotonicity.
-/

/-- Enforcement is deterministic: given the same inputs, the result is unique. -/
theorem enforceValue_deterministic
    (h1 : EnforceValue ct heap v T r₁)
    (h2 : EnforceValue ct heap v T r₂) : r₁ = r₂ := by
  induction h1 generalizing r₂ with
  | unknown | bottom => cases h2; rfl
  | classObjRefOk hlook hfind hmro hmem =>
      cases h2 with
      | classObjRefOk => rfl
      | classObjRefBlame hlook₂ hfind₂ hmro₂ hnotmem =>
          rw [hlook] at hlook₂; cases hlook₂; rw [hfind] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro hmro₂ ▸ hmem) hnotmem
  | classObjRefBlame hlook hfind hmro hnotmem =>
      cases h2 with
      | classObjRefOk hlook₂ hfind₂ hmro₂ hmem₂ =>
          rw [hlook] at hlook₂; cases hlook₂; rw [hfind] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro hmro₂ ▸ hmem₂) hnotmem
      | classObjRefBlame => rfl
  | callableObjRefTransparentOk hlook =>
      cases h2 with
      | callableObjRefTransparentOk => rfl
      | callableObjRefBlame hlook₂ => rw [hlook] at hlook₂; cases hlook₂
  | callableObjRefBlame hlook =>
      cases h2 with
      | callableObjRefTransparentOk hlook₂ => rw [hlook] at hlook₂; cases hlook₂
      | callableObjRefBlame => rfl
  | unionLeft _ ihT =>
      cases h2 with
      | unionLeft h2T => exact ihT h2T
      | unionRight h2T _ | unionBlame h2T _ => cases ihT h2T
  | unionRight _ _ ihT ihU =>
      cases h2 with
      | unionLeft h2T => cases ihT h2T
      | unionRight _ h2U => exact ihU h2U
      | unionBlame _ h2U => cases ihU h2U
  | unionBlame _ _ ihT ihU =>
      cases h2 with
      | unionLeft h2T => cases ihT h2T
      | unionRight _ h2U => cases ihU h2U
      | unionBlame => rfl
  | intersectionOk _ _ ihT ihU =>
      cases h2 with
      | intersectionOk h2T h2U => cases ihT h2T; exact ihU h2U
      | intersectionBlameLeft h2T => cases ihT h2T
      | intersectionBlameRight h2T h2U => cases ihT h2T; cases ihU h2U
  | intersectionBlameLeft _ ihT =>
      cases h2 with
      | intersectionOk h2T _ | intersectionBlameRight h2T _ => cases ihT h2T
      | intersectionBlameLeft => rfl
  | intersectionBlameRight _ _ ihT ihU =>
      cases h2 with
      | intersectionOk h2T h2U => cases ihT h2T; cases ihU h2U
      | intersectionBlameLeft h2T => cases ihT h2T
      | intersectionBlameRight h2T h2U => cases ihT h2T; exact ihU h2U
  | negClassObjRefOk hlook hfind hmro hnmem =>
      cases h2 with
      | negClassObjRefOk => rfl
      | negClassObjRefBlame hlook₂ hfind₂ hmro₂ hmem =>
          rw [hlook] at hlook₂; cases hlook₂; rw [hfind] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro hmro₂ ▸ hmem) hnmem
  | negClassObjRefBlame hlook hfind hmro hmem =>
      cases h2 with
      | negClassObjRefOk hlook₂ hfind₂ hmro₂ hnmem =>
          rw [hlook] at hlook₂; cases hlook₂; rw [hfind] at hfind₂; cases hfind₂
          exact absurd (gComputeMro_determinism hmro hmro₂ ▸ hmem) hnmem
      | negClassObjRefBlame => rfl

/-! ## Enforcement totality -/

/-- Enforcement always either succeeds or blames for heap-present object references. -/
theorem enforceValue_total
    (hheap : CheckedHeapWellFormed gct cct heap)
    (c : BoundaryContract)
    (v : CheckedValue)
    (hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj) :
    EnforceValue gct heap v c .ok ∨
    EnforceValue gct heap v c .blame := by
  induction c generalizing v with
  | unknown => exact .inl .unknown
  | bottom => exact .inr .bottom
  | class_ cname =>
      obtain ⟨oid⟩ := v
      obtain ⟨obj, hlook⟩ := hvlook oid rfl
      obtain ⟨cls, mro, hfind, hmro⟩ := hheap.classesExist oid obj hlook
      by_cases hmem : cname ∈ mro
      · exact .inl (.classObjRefOk hlook hfind hmro hmem)
      · exact .inr (.classObjRefBlame hlook hfind hmro hmem)
  | callable domC codC =>
      obtain ⟨oid⟩ := v
      obtain ⟨obj, hlook⟩ := hvlook oid rfl
      obtain ⟨cname, payload⟩ := obj
      cases payload with
      | ordinary => exact .inr (.callableObjRefBlame hlook)
      | boundMethod recvOid m =>
          cases (hheap.boundMethodShape oid _ hlook).mpr ⟨recvOid, m, rfl⟩
          exact .inl (.callableObjRefTransparentOk hlook)
  | union T U ihT ihU =>
      cases ihT v hvlook with
      | inl hokT => exact .inl (.unionLeft hokT)
      | inr hblT =>
          cases ihU v hvlook with
          | inl hokU => exact .inl (.unionRight hblT hokU)
          | inr hblU => exact .inr (.unionBlame hblT hblU)
  | intersection T U ihT ihU =>
      cases ihT v hvlook with
      | inl hokT =>
          cases ihU v hvlook with
          | inl hokU => exact .inl (.intersectionOk hokT hokU)
          | inr hblU => exact .inr (.intersectionBlameRight hokT hblU)
      | inr hblT => exact .inr (.intersectionBlameLeft hblT)
  | negClass cname =>
      obtain ⟨oid⟩ := v
      obtain ⟨obj, hlook⟩ := hvlook oid rfl
      obtain ⟨cls, mro, hfind, hmro⟩ := hheap.classesExist oid obj hlook
      by_cases hmem : cname ∈ mro
      · exact .inr (.negClassObjRefBlame hlook hfind hmro hmem)
      · exact .inl (.negClassObjRefOk hlook hfind hmro hmem)

/-! ## Enforcement heap monotonicity -/

/-- Enforcement is monotone in the heap: if all old lookups are preserved,
    enforcement results transfer unchanged. -/
theorem enforceValue_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (henf : EnforceValue ct heap v c r) :
    EnforceValue ct heap' v c r := by
  induction henf with
  | unknown => exact .unknown
  | bottom => exact .bottom
  | classObjRefOk hlook hfind hmro hmem => exact .classObjRefOk (hmono _ _ hlook) hfind hmro hmem
  | classObjRefBlame hlook hfind hmro hnmem => exact .classObjRefBlame (hmono _ _ hlook) hfind hmro hnmem
  | callableObjRefTransparentOk hlook => exact .callableObjRefTransparentOk (hmono _ _ hlook)
  | callableObjRefBlame hlook => exact .callableObjRefBlame (hmono _ _ hlook)
  | unionLeft _ ih => exact .unionLeft ih
  | unionRight _ _ ihT ihU => exact .unionRight ihT ihU
  | unionBlame _ _ ihT ihU => exact .unionBlame ihT ihU
  | intersectionOk _ _ ihT ihU => exact .intersectionOk ihT ihU
  | intersectionBlameLeft _ ih => exact .intersectionBlameLeft ih
  | intersectionBlameRight _ _ ihT ihU => exact .intersectionBlameRight ihT ihU
  | negClassObjRefOk hlook hfind hmro hnmem => exact .negClassObjRefOk (hmono _ _ hlook) hfind hmro hnmem
  | negClassObjRefBlame hlook hfind hmro hmem => exact .negClassObjRefBlame (hmono _ _ hlook) hfind hmro hmem

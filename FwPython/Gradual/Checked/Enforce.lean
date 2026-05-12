import FwPython.Gradual.Checked.Invariants
import FwPython.Gradual.TypeSystem.ClassTable.WellFormednessCore

/-! ## EnforceValue theorems

Basic metatheory for the runtime enforcement relation:
determinism, same-value success, totality, and heap monotonicity. -/

/-- Enforcement is deterministic: given the same inputs, the result is unique. -/
theorem enforceValue_deterministic
    (h1 : EnforceValue ct heap v T ℓ r₁)
    (h2 : EnforceValue ct heap v T ℓ r₂) : r₁ = r₂ := by
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
      | unionLeft h2T => rw [ihT h2T]
      | unionRight h2T _ | unionBlame h2T _ => cases ihT h2T
  | unionRight _ _ ihT ihU =>
      cases h2 with
      | unionLeft h2T => cases ihT h2T
      | unionRight _ h2U => rw [ihU h2U]
      | unionBlame _ h2U => cases ihU h2U
  | unionBlame _ _ ihT ihU =>
      cases h2 with
      | unionLeft h2T => cases ihT h2T
      | unionRight _ h2U => cases ihU h2U
      | unionBlame => rfl
  | intersectionOk _ _ ihT ihU =>
      cases h2 with
      | intersectionOk h2T h2U => cases ihT h2T; rw [ihU h2U]
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
      | intersectionBlameRight h2T h2U => cases ihT h2T; rfl
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

/-- Auxiliary form of `enforce_ok_same_value` with an unconstrained result index. -/
private theorem enforce_ok_same_value_aux
    (henf : EnforceValue gct heap v c labels r) :
    ∀ v', r = .ok v' → v' = v := by
  induction henf with
  | unknown => intro _ hr; cases hr; rfl
  | bottom | classObjRefBlame _ _ _ _ | callableObjRefBlame _
  | unionBlame _ _ | intersectionBlameLeft _ | intersectionBlameRight _ _
  | negClassObjRefBlame _ _ _ _ => intro _ hr; cases hr
  | classObjRefOk | callableObjRefTransparentOk | negClassObjRefOk =>
      intro _ hr; cases hr; rfl
  | unionLeft _ ih | unionRight _ _ _ ih => exact ih
  | intersectionOk _ _ ihT ihU =>
      intro _ hr; cases hr; exact (ihU _ rfl).trans (ihT _ rfl)

/-- Successful enforcement always returns the original value. -/
theorem enforce_ok_same_value
    (henf : EnforceValue gct heap v c labels (.ok v')) :
    v' = v :=
  enforce_ok_same_value_aux henf _ rfl

/-- For fixed inputs, successful and blameing enforcement outcomes are
mutually exclusive. -/
theorem enforce_outcomes_exclusive
    (hok : EnforceValue gct heap v c labels (.ok v'))
    (hbl : EnforceValue gct heap v c labels (.blame blameLabel)) :
    False := by
  have hdet := enforceValue_deterministic hok hbl
  cases hdet

/-! ## Enforcement totality -/

/-- Enforcement always either succeeds or blames for heap-present object references. -/
theorem enforceValue_total
    (hheap : CheckedHeapWellFormed gct cct heap)
    (hwfct : WellFormedGClassTableCore gct)
    (c : BoundaryContract) (labels : BoundaryLabels c)
    (v : CheckedValue)
    (hvlook : ∀ oid, v = .objRef oid → ∃ obj, heap.lookup oid = some obj) :
    (∃ v', EnforceValue gct heap v c labels (.ok v')) ∨
    EnforceValue gct heap v c labels (.blame labels.direct) := by
  let _ := hwfct
  induction c generalizing v with
  | unknown => exact .inl ⟨v, .unknown⟩
  | bottom => exact .inr .bottom
  | class_ cname =>
      cases v with
      | objRef oid =>
          obtain ⟨obj, hlook⟩ := hvlook oid rfl
          obtain ⟨cls, mro, hfind, hmro⟩ := hheap.classesExist oid obj hlook
          by_cases hmem : cname ∈ mro
          · exact .inl ⟨_, .classObjRefOk hlook hfind hmro hmem⟩
          · exact .inr (.classObjRefBlame hlook hfind hmro hmem)
  | callable domC codC =>
      cases v with
      | objRef oid =>
          obtain ⟨obj, hlook⟩ := hvlook oid rfl
          rcases obj with ⟨cname, payload⟩
          cases payload with
          | ordinary => exact .inr (.callableObjRefBlame hlook)
          | boundMethod recvOid m =>
              cases hheap.payloadBoundMethod oid cname recvOid m hlook
              exact .inl ⟨_, .callableObjRefTransparentOk hlook⟩
  | union T U ihT ihU =>
      cases ihT (labels := labels.subtree (.unionLeft .here)) v hvlook with
      | inl hsuccessT =>
          obtain ⟨v', henfT⟩ := hsuccessT
          exact .inl ⟨v', .unionLeft henfT⟩
      | inr hblT =>
          cases ihU (labels := labels.subtree (.unionRight .here)) v hvlook with
          | inl hsuccessU =>
              obtain ⟨v', henfU⟩ := hsuccessU
              exact .inl ⟨v', .unionRight hblT henfU⟩
          | inr hblU => exact .inr (.unionBlame hblT hblU)
  | intersection T U ihT ihU =>
      cases ihT (labels := labels.subtree (.intersectionLeft .here)) v hvlook with
      | inl hsuccessT =>
          obtain ⟨v', henfT⟩ := hsuccessT
          cases enforce_ok_same_value henfT
          cases ihU (labels := labels.subtree (.intersectionRight .here)) v hvlook with
          | inl hsuccessU =>
              obtain ⟨v'', henfU⟩ := hsuccessU
              exact .inl ⟨v'', .intersectionOk henfT henfU⟩
          | inr hblU => exact .inr (.intersectionBlameRight henfT hblU)
      | inr hblT => exact .inr (.intersectionBlameLeft hblT)
  | negClass cname =>
      cases v with
      | objRef oid =>
          obtain ⟨obj, hlook⟩ := hvlook oid rfl
          obtain ⟨cls, mro, hfind, hmro⟩ := hheap.classesExist oid obj hlook
          by_cases hmem : cname ∈ mro
          · exact .inr (.negClassObjRefBlame hlook hfind hmro hmem)
          · exact .inl ⟨_, .negClassObjRefOk hlook hfind hmro hmem⟩

/-! ## Enforcement heap monotonicity -/

/-- Enforcement is monotone in the heap: if all old lookups are preserved,
    enforcement results transfer unchanged. -/
theorem enforceValue_heapMono
    (hmono : ∀ oid obj, heap.lookup oid = some obj → heap'.lookup oid = some obj)
    (henf : EnforceValue ct heap v c ℓ r) :
    EnforceValue ct heap' v c ℓ r := by
  induction henf with
  | unknown => exact .unknown
  | bottom => exact .bottom
  | classObjRefOk hlook hfind hmro hmem =>
      exact .classObjRefOk (hmono _ _ hlook) hfind hmro hmem
  | classObjRefBlame hlook hfind hmro hnmem =>
      exact .classObjRefBlame (hmono _ _ hlook) hfind hmro hnmem
  | callableObjRefTransparentOk hlook => exact .callableObjRefTransparentOk (hmono _ _ hlook)
  | callableObjRefBlame hlook => exact .callableObjRefBlame (hmono _ _ hlook)
  | unionLeft _ ih => exact .unionLeft ih
  | unionRight hblT _ ihT ihU => exact .unionRight ihT ihU
  | unionBlame _ _ ihT ihU => exact .unionBlame ihT ihU
  | intersectionOk _ _ ihT ihU => exact .intersectionOk ihT ihU
  | intersectionBlameLeft _ ih => exact .intersectionBlameLeft ih
  | intersectionBlameRight _ _ ihT ihU => exact .intersectionBlameRight ihT ihU
  | negClassObjRefOk hlook hfind hmro hnmem =>
      exact .negClassObjRefOk (hmono _ _ hlook) hfind hmro hnmem
  | negClassObjRefBlame hlook hfind hmro hmem =>
      exact .negClassObjRefBlame (hmono _ _ hlook) hfind hmro hmem

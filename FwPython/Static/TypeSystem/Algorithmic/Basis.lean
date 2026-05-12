import FwPython.Static.TypeSystem.TypingLemmas
import FwPython.Static.Subtyping.Completeness.Infra.Atoms

/-! ## Basis saturation -/

def allBoolMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      let rest := allBoolMasks n
      rest.map (fun bits => false :: bits) ++ rest.map (fun bits => true :: bits)

theorem allBoolMasks_length
    {n : Nat} {bits : List Bool}
    (hmem : bits ∈ allBoolMasks n) :
    bits.length = n := by
  induction n generalizing bits with
  | zero =>
      simp [allBoolMasks] at hmem
      cases hmem
      rfl
  | succ n ih =>
      simp [allBoolMasks] at hmem
      rcases hmem with ⟨bs, hbs, rfl⟩ | ⟨bs, hbs, rfl⟩
      · simp [ih hbs]
      · simp [ih hbs]

theorem allBoolMasks_complete
    {n : Nat} (bits : List Bool)
    (hlen : bits.length = n) :
    bits ∈ allBoolMasks n := by
  induction bits generalizing n with
  | nil =>
      cases n with
      | zero =>
          simp [allBoolMasks]
      | succ n =>
          cases hlen
  | cons b bits ih =>
      cases n with
      | zero =>
          cases hlen
      | succ n =>
          have hlenTail : bits.length = n := by
            cases hlen
            rfl
          cases b <;> simp [allBoolMasks, ih hlenTail]

structure SelectionMask (B : List Ty) where
  bits : List Bool
  length_eq : bits.length = B.length
  some_true : true ∈ bits

private def orBits : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | b1 :: bs1, b2 :: bs2 => (b1 || b2) :: orBits bs1 bs2

private theorem orBits_length
    (hlen : bits1.length = bits2.length) :
    (orBits bits1 bits2).length = bits1.length := by
  induction bits1 generalizing bits2 with
  | nil =>
      cases bits2 with
      | nil =>
          rfl
      | cons _ _ =>
          cases hlen
  | cons b1 bs1 ih =>
      cases bits2 with
      | nil =>
          cases hlen
      | cons b2 bs2 =>
          have hlenTail : bs1.length = bs2.length := by
            exact Nat.succ.inj hlen
          simp [orBits, ih hlenTail]

private theorem orBits_mem_true_left
    (hmem : true ∈ bits1)
    (hlen : bits1.length = bits2.length) :
    true ∈ orBits bits1 bits2 := by
  induction bits1 generalizing bits2 with
  | nil =>
      cases hmem
  | cons b1 bs1 ih =>
      cases bits2 with
      | nil =>
          cases hlen
      | cons b2 bs2 =>
          have hlenTail : bs1.length = bs2.length := by
            exact Nat.succ.inj hlen
          cases b1 <;> cases b2
          · simp [orBits] at hmem ⊢
            exact ih hmem hlenTail
          · simp [orBits]
          · simp [orBits]
          · simp [orBits]

def SelectionMask.combineOr
    (m1 m2 : SelectionMask B) : SelectionMask B where
  bits := orBits m1.bits m2.bits
  length_eq := by
    have hlen : m1.bits.length = m2.bits.length := by
      rw [m1.length_eq, m2.length_eq]
    simpa [m1.length_eq] using orBits_length (bits1 := m1.bits) (bits2 := m2.bits) hlen
  some_true := by
    have hlen : m1.bits.length = m2.bits.length := by
      rw [m1.length_eq, m2.length_eq]
    exact orBits_mem_true_left (bits1 := m1.bits) (bits2 := m2.bits) m1.some_true hlen

private def selectByBits : List Ty → List Bool → List Ty
  | [], _ => []
  | _, [] => []
  | T :: Ts, keep :: ks =>
      if keep then T :: selectByBits Ts ks else selectByBits Ts ks

def selectByMask (B : List Ty) (mask : SelectionMask B) : List Ty :=
  selectByBits B mask.bits

private theorem selectByBits_mem_source
    (hmem : A ∈ selectByBits B bits) :
    A ∈ B := by
  induction B generalizing bits with
  | nil =>
      cases hmem
  | cons T Ts ih =>
      cases bits with
      | nil =>
          cases hmem
      | cons keep ks =>
          cases keep <;> simp [selectByBits] at hmem ⊢
          · exact Or.inr (ih hmem)
          · rcases hmem with rfl | hmem
            · exact Or.inl rfl
            · exact Or.inr (ih hmem)

private theorem selectByBits_exists_mem
    (hlen : bits.length = B.length)
    (hsome : true ∈ bits) :
    ∃ A, A ∈ selectByBits B bits := by
  induction B generalizing bits with
  | nil =>
      cases bits with
      | nil =>
          cases hsome
      | cons b bs =>
          cases hlen
  | cons T Ts ih =>
      cases bits with
      | nil =>
          cases hlen
      | cons b bs =>
          have hlenTail : bs.length = Ts.length := by
            exact Nat.succ.inj hlen
          cases b with
          | false =>
              simp at hsome
              obtain ⟨A, hA⟩ := ih hlenTail hsome
              exact ⟨A, by simp [selectByBits, hA]⟩
          | true =>
              exact ⟨T, by simp [selectByBits]⟩

private theorem selectByMask_exists_mem
    (mask : SelectionMask B) :
    ∃ A, A ∈ selectByMask B mask := by
  exact selectByBits_exists_mem (B := B) mask.length_eq mask.some_true

private theorem selectByMask_ne_nil
    (mask : SelectionMask B) :
    selectByMask B mask ≠ [] := by
  obtain ⟨A, hA⟩ := selectByMask_exists_mem (B := B) mask
  intro hnil
  rw [hnil] at hA
  cases hA

private theorem selectByBits_replicate_false :
    selectByBits B (List.replicate B.length false) = [] := by
  induction B with
  | nil =>
      rfl
  | cons T Ts ih =>
      simp [List.replicate, selectByBits, ih]

private theorem mem_selectByBits_or_left
    (hmem : A ∈ selectByBits B bits1)
    (hlen : bits1.length = bits2.length) :
    A ∈ selectByBits B (orBits bits1 bits2) := by
  induction B generalizing bits1 bits2 with
  | nil =>
      cases hmem
  | cons T Ts ih =>
      cases bits1 with
      | nil =>
          cases hmem
      | cons b1 bs1 =>
          cases bits2 with
          | nil =>
              cases hlen
          | cons b2 bs2 =>
              have hlenTail : bs1.length = bs2.length := by
                exact Nat.succ.inj hlen
              cases b1 <;> cases b2
              · simp [selectByBits, orBits] at hmem ⊢
                exact ih hmem hlenTail
              · simp [selectByBits, orBits] at hmem ⊢
                exact Or.inr (ih hmem hlenTail)
              · simp [selectByBits, orBits] at hmem ⊢
                rcases hmem with rfl | hmem
                · simp
                · exact Or.inr (ih hmem hlenTail)
              · simp [selectByBits, orBits] at hmem ⊢
                rcases hmem with rfl | hmem
                · simp
                · exact Or.inr (ih hmem hlenTail)

private theorem orBits_comm :
    orBits bits1 bits2 = orBits bits2 bits1 := by
  induction bits1 generalizing bits2 with
  | nil =>
      cases bits2 <;> rfl
  | cons b1 bs1 ih =>
      cases bits2 with
      | nil =>
          rfl
      | cons b2 bs2 =>
          cases b1 <;> cases b2 <;> simp [orBits, ih]

private theorem mem_selectByBits_or_right
    (hmem : A ∈ selectByBits B bits2)
    (hlen : bits1.length = bits2.length) :
    A ∈ selectByBits B (orBits bits1 bits2) := by
  have hmem' :
      A ∈ selectByBits B (orBits bits2 bits1) :=
    mem_selectByBits_or_left (B := B) (bits1 := bits2) (bits2 := bits1) hmem hlen.symm
  simpa [orBits_comm] using hmem'

private theorem selectByMask_subset_combineOr_left
    (m1 m2 : SelectionMask B)
    (hmem : A ∈ selectByMask B m1) :
    A ∈ selectByMask B (SelectionMask.combineOr m1 m2) := by
  have hlen : m1.bits.length = m2.bits.length := by
    rw [m1.length_eq, m2.length_eq]
  exact mem_selectByBits_or_left (B := B) (bits1 := m1.bits) (bits2 := m2.bits) hmem hlen

private theorem selectByMask_subset_combineOr_right
    (m1 m2 : SelectionMask B)
    (hmem : A ∈ selectByMask B m2) :
    A ∈ selectByMask B (SelectionMask.combineOr m1 m2) := by
  have hlen : m1.bits.length = m2.bits.length := by
    rw [m1.length_eq, m2.length_eq]
  exact mem_selectByBits_or_right (B := B) (bits1 := m1.bits) (bits2 := m2.bits) hmem hlen

private theorem interAtomsFold_wellFormed_of_nonempty
    (hall : ∀ A, A ∈ atoms → WellFormedTy ct A)
    (hne : atoms ≠ []) :
    WellFormedTy ct (Ty.interAtomsFold atoms) := by
  induction atoms with
  | nil =>
      cases hne rfl
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.interAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.interAtomsFold]
          exact .intersection
            (hall A (by simp))
            (ih (by
              intro X hX
              exact hall X (by simp [hX])) (by simp))

private theorem hasType_interAtomsFold
    (hall : ∀ A, A ∈ atoms → HasType ct Γ e A)
    (hne : atoms ≠ []) :
    HasType ct Γ e (Ty.interAtomsFold atoms) := by
  induction atoms with
  | nil =>
      cases hne rfl
  | cons A As ih =>
      cases As with
      | nil =>
          simpa [Ty.interAtomsFold] using hall A (by simp)
      | cons B Bs =>
          simp [Ty.interAtomsFold]
          exact .interIntro
            (hall A (by simp))
            (ih (by
              intro X hX
              exact hall X (by simp [hX])) (by simp))

private theorem exists_singletonMask_of_mem
    (hmem : T ∈ B) :
    ∃ mask : SelectionMask B, selectByMask B mask = [T] := by
  induction B with
  | nil =>
      cases hmem
  | cons A As ih =>
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · let bits := true :: List.replicate As.length false
        have hlen : bits.length = (T :: As).length := by
          simp [bits]
        have htrue : true ∈ bits := by
          simp [bits]
        refine ⟨⟨bits, hlen, htrue⟩, ?_⟩
        simp [selectByMask, selectByBits, bits, selectByBits_replicate_false]
      · obtain ⟨mask, hmask⟩ := ih hmemTail
        let bits := false :: mask.bits
        have hlen : bits.length = (A :: As).length := by
          simp [bits, mask.length_eq]
        have htrue : true ∈ bits := by
          simp [bits, mask.some_true]
        refine ⟨⟨bits, hlen, htrue⟩, ?_⟩
        have htail : selectByBits As mask.bits = [T] := by
          simpa [selectByMask] using hmask
        simp [selectByMask, selectByBits, bits, htail]

def intersectionsOfNonemptySelections (B : List Ty) : List Ty :=
  (allBoolMasks B.length).attach.flatMap fun bits =>
    if hsome : true ∈ bits.1 then
      [Ty.interAtomsFold (selectByMask B
        { bits := bits.1
          length_eq := allBoolMasks_length bits.2
          some_true := hsome })]
    else
      []

def saturateBasis : List Ty → List Ty :=
  intersectionsOfNonemptySelections

private theorem saturateBasis_contains_mask
    (mask : SelectionMask B) :
    Ty.interAtomsFold (selectByMask B mask) ∈ saturateBasis B := by
  unfold saturateBasis intersectionsOfNonemptySelections
  have hbits : mask.bits ∈ allBoolMasks B.length :=
    allBoolMasks_complete mask.bits mask.length_eq
  simp [selectByMask]
  exact ⟨mask.bits, hbits, mask.some_true, rfl⟩

theorem saturateBasis_member_witness
    (hmem : U ∈ saturateBasis B) :
    ∃ mask : SelectionMask B,
      U = Ty.interAtomsFold (selectByMask B mask) := by
  unfold saturateBasis intersectionsOfNonemptySelections at hmem
  simp [selectByMask] at hmem
  rcases hmem with ⟨bits, hbits, htrue, hEq⟩
  refine ⟨⟨bits, allBoolMasks_length hbits, htrue⟩, ?_⟩
  simpa [selectByMask] using hEq

theorem saturateBasis_mem_of_mem
    (hmem : T ∈ B) :
    T ∈ saturateBasis B := by
  obtain ⟨mask, hmask⟩ := exists_singletonMask_of_mem (B := B) hmem
  have hsat := saturateBasis_contains_mask (B := B) mask
  simpa [hmask, Ty.interAtomsFold] using hsat

theorem saturateBasis_member_wellFormed
    (hwfRaw : ∀ T, T ∈ B → WellFormedTy ct T)
    (hmem : U ∈ saturateBasis B) :
    WellFormedTy ct U := by
  obtain ⟨mask, rfl⟩ := saturateBasis_member_witness (B := B) hmem
  refine interAtomsFold_wellFormed_of_nonempty ?_ (selectByMask_ne_nil (B := B) mask)
  intro A hA
  exact hwfRaw A (selectByBits_mem_source (B := B) (bits := mask.bits) hA)

theorem saturateBasis_member_sound
    (hall : ∀ T, T ∈ B → HasType ct Γ e T)
    (hmem : U ∈ saturateBasis B) :
    HasType ct Γ e U := by
  obtain ⟨mask, rfl⟩ := saturateBasis_member_witness (B := B) hmem
  refine hasType_interAtomsFold ?_ (selectByMask_ne_nil (B := B) mask)
  intro A hA
  exact hall A (selectByBits_mem_source (B := B) (bits := mask.bits) hA)

theorem saturateBasis_intersection_cover
    (hS : S ∈ saturateBasis B)
    (hT : T ∈ saturateBasis B) :
    ∃ U, U ∈ saturateBasis B ∧ IsSubtype ct U (.intersection S T) := by
  obtain ⟨m1, rfl⟩ := saturateBasis_member_witness (B := B) hS
  obtain ⟨m2, rfl⟩ := saturateBasis_member_witness (B := B) hT
  let mor := SelectionMask.combineOr m1 m2
  refine ⟨Ty.interAtomsFold (selectByMask B mor), saturateBasis_contains_mask (B := B) mor, ?_⟩
  refine .interIntro ?_ ?_
  · exact interAtomsFold_subtype_of_subset
      (ct := ct)
      (atoms₁ := selectByMask B m1)
      (atoms₂ := selectByMask B mor)
      (fun A hA => selectByMask_subset_combineOr_left (B := B) m1 m2 hA)
  · exact interAtomsFold_subtype_of_subset
      (ct := ct)
      (atoms₁ := selectByMask B m2)
      (atoms₂ := selectByMask B mor)
      (fun A hA => selectByMask_subset_combineOr_right (B := B) m1 m2 hA)

structure CertifiedBasis (ct : ClassTable) where
  elems : List Ty
  wf : ∀ T, T ∈ elems → WellFormedTy ct T

structure InferredBasis (ct : ClassTable) (Γ : TyEnv) (e : Expr) where
  raw : List Ty
  elems : List Ty
  saturated : elems = saturateBasis raw
  wf : ∀ T, T ∈ elems → WellFormedTy ct T
  sound : ∀ T, T ∈ elems → HasType ct Γ e T

import FwPython.Static.Subtyping.Completeness.Infra.Atoms

/-! ### Clean source summaries -/

structure CleanSourceSummary where
  hasBottom : Bool
  leafClassAtom : Option Identifier
  leafConflict : Bool
  nonleafClassAtoms : List Identifier
  negAtoms : List Identifier
  callableAtoms : List (Ty × Ty)

def emptyCleanSourceSummary : CleanSourceSummary :=
  { hasBottom := false
    leafClassAtom := none
    leafConflict := false
    nonleafClassAtoms := []
    negAtoms := []
    callableAtoms := [] }

def insertId (x : Identifier) (xs : List Identifier) : List Identifier :=
  if x ∈ xs then xs else x :: xs

def insertCallable (pr : Ty × Ty) (xs : List (Ty × Ty)) : List (Ty × Ty) :=
  if pr ∈ xs then xs else pr :: xs

def updateDistinct
    (x : Identifier)
    (curr : Option Identifier)
    (conflict : Bool) :
    Option Identifier × Bool :=
  match curr with
  | none => (some x, conflict)
  | some y => if x = y then (curr, conflict) else (curr, true)

theorem insertId_nodup (hxs : xs.Nodup) : (insertId x xs).Nodup := by
  unfold insertId
  by_cases hmem : x ∈ xs
  · simp [hmem, hxs]
  · simp [hmem, hxs]

theorem insertCallable_nodup (hxs : xs.Nodup) :
    (insertCallable pr xs).Nodup := by
  unfold insertCallable
  by_cases hmem : pr ∈ xs
  · simp [hmem, hxs]
  · simp [hmem, hxs]

theorem mem_insertId : y ∈ insertId x xs ↔ y = x ∨ y ∈ xs := by
  unfold insertId
  by_cases hmem : x ∈ xs
  · constructor
    · intro hy
      simpa [hmem] using Or.inr hy
    · intro hy
      rcases hy with rfl | hy
      · simp [hmem]
      · simpa [hmem] using hy
  · simp [hmem]

theorem mem_insertCallable : q ∈ insertCallable pr xs ↔ q = pr ∨ q ∈ xs := by
  unfold insertCallable
  by_cases hmem : pr ∈ xs
  · constructor
    · intro hy
      simpa [hmem] using Or.inr hy
    · intro hy
      rcases hy with rfl | hy
      · simp [hmem]
      · simpa [hmem] using hy
  · simp [hmem]

theorem insertCallable_tySizeSum_le
    (pr : Ty × Ty) (xs : List (Ty × Ty)) :
    tySizeSum ((insertCallable pr xs).map callableAtomTy) ≤
      tySizeSum ((callableAtomTy pr) :: xs.map callableAtomTy) := by
  unfold insertCallable
  by_cases hmem : pr ∈ xs
  · simp [hmem, tySizeSum]
  · simp [hmem]

def summarizeInterAtoms (hwfct : WellFormedClassTable ct) : List Ty → CleanSourceSummary
  | [] => emptyCleanSourceSummary
  | atom :: atoms =>
      let s := summarizeInterAtoms hwfct atoms
      match atom with
      | .bottom =>
          { s with hasBottom := true }
      | .class_ C =>
          match builtinLeafDecidable (ct := ct) (C := C) hwfct with
          | isTrue _ =>
              let upd := updateDistinct C s.leafClassAtom s.leafConflict
              { s with leafClassAtom := upd.1, leafConflict := upd.2 }
          | isFalse _ =>
              { s with nonleafClassAtoms := insertId C s.nonleafClassAtoms }
      | .negClass C =>
          { s with negAtoms := insertId C s.negAtoms }
      | .callable P R =>
          { s with callableAtoms := insertCallable (P, R) s.callableAtoms }
      | .union _ _ =>
          { s with hasBottom := s.hasBottom }
      | .intersection _ _ =>
          { s with hasBottom := s.hasBottom }

theorem updateDistinct_fst_eq_some
    (h : (updateDistinct x curr conflict).1 = some y) :
    x = y ∨ curr = some y := by
  unfold updateDistinct at h
  cases curr with
  | none =>
      simp at h
      exact Or.inl h
  | some z =>
      by_cases hxz : x = z
      · simp [hxz] at h
        exact Or.inr (by simp [h])
      · simp [hxz] at h
        exact Or.inr (by simp [h])

theorem updateDistinct_self_or_conflict :
    (updateDistinct x curr conflict).2 = true ∨
      (updateDistinct x curr conflict).1 = some x := by
  unfold updateDistinct
  cases curr with
  | none =>
      simp
  | some y =>
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy]

theorem updateDistinct_preserve_some_or_conflict
    (hsome : curr = some y) :
    (updateDistinct x curr conflict).2 = true ∨
      (updateDistinct x curr conflict).1 = some y := by
  unfold updateDistinct
  rw [hsome]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy]

theorem updateDistinct_snd_eq_true
    (h : (updateDistinct x curr conflict).2 = true) :
    conflict = true ∨ ∃ y, curr = some y ∧ x ≠ y := by
  unfold updateDistinct at h
  cases curr with
  | none =>
      simp at h
      exact Or.inl h
  | some y =>
      by_cases hxy : x = y
      · simp [hxy] at h
        exact Or.inl h
      · simp [hxy] at h
        exact Or.inr ⟨y, rfl, hxy⟩

theorem summarizeInterAtoms_hasBottom_iff :
    (summarizeInterAtoms hwfct atoms).hasBottom = true ↔ .bottom ∈ atoms := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | bottom | negClass | union | intersection | callable =>
          simp [summarizeInterAtoms, ih]
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec] using ih

theorem summarizeInterAtoms_nonleaf_nodup :
    (summarizeInterAtoms hwfct atoms).nonleafClassAtoms.Nodup := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec] using insertId_nodup (x := C) ih
      | bottom | negClass | union | intersection | callable =>
          simpa [summarizeInterAtoms] using ih

theorem summarizeInterAtoms_neg_nodup :
    (summarizeInterAtoms hwfct atoms).negAtoms.Nodup := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | negClass C =>
          simpa [summarizeInterAtoms] using insertId_nodup (x := C) ih
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec] using ih
      | bottom | union | intersection | callable =>
          simpa [summarizeInterAtoms] using ih

theorem summarizeInterAtoms_callable_nodup :
    (summarizeInterAtoms hwfct atoms).callableAtoms.Nodup := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | callable P R =>
          simpa [summarizeInterAtoms] using insertCallable_nodup (pr := (P, R)) ih
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec] using ih
      | bottom | negClass | union | intersection =>
          simpa [summarizeInterAtoms] using ih

theorem tySizeSum_le_cons
    (A : Ty) (h : n ≤ tySizeSum atoms) :
    n ≤ tySizeSum (A :: atoms) := by
  have hpos : 1 ≤ A.size := Ty.size_pos A
  simp [tySizeSum]
  omega

theorem summarizeInterAtoms_callable_tySizeSum_le
    (hwfct : WellFormedClassTable ct) :
    tySizeSum ((summarizeInterAtoms hwfct atoms).callableAtoms.map callableAtomTy) ≤
      tySizeSum atoms := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary, tySizeSum]
  | cons atom atoms ih =>
      cases atom with
      | callable P R =>
          have hinsert :=
            insertCallable_tySizeSum_le (pr := (P, R))
              ((summarizeInterAtoms hwfct atoms).callableAtoms)
          calc
            tySizeSum ((summarizeInterAtoms hwfct (.callable P R :: atoms)).callableAtoms.map callableAtomTy)
                = tySizeSum ((insertCallable (P, R) (summarizeInterAtoms hwfct atoms).callableAtoms).map callableAtomTy) := by
                    simp [summarizeInterAtoms]
            _ ≤ tySizeSum ((callableAtomTy (P, R)) :: (summarizeInterAtoms hwfct atoms).callableAtoms.map callableAtomTy) :=
                hinsert
            _ = (callableAtomTy (P, R)).size +
                  tySizeSum ((summarizeInterAtoms hwfct atoms).callableAtoms.map callableAtomTy) := by
                    simp [tySizeSum]
            _ ≤ (callableAtomTy (P, R)).size + tySizeSum atoms := by
                  exact Nat.add_le_add_left ih _
            _ = tySizeSum (.callable P R :: atoms) := by
                  simp [callableAtomTy, tySizeSum]
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              exact (by
                simpa [summarizeInterAtoms, hdec] using
                  tySizeSum_le_cons (.class_ C) ih)
          | isFalse _ =>
              exact (by
                simpa [summarizeInterAtoms, hdec] using
                  tySizeSum_le_cons (.class_ C) ih)
      | bottom =>
          simpa [summarizeInterAtoms] using
            tySizeSum_le_cons Ty.bottom ih
      | negClass C =>
          simpa [summarizeInterAtoms] using
            tySizeSum_le_cons (.negClass C) ih
      | union T U =>
          simpa [summarizeInterAtoms] using
            tySizeSum_le_cons (.union T U) ih
      | intersection T U =>
          simpa [summarizeInterAtoms] using
            tySizeSum_le_cons (.intersection T U) ih

theorem tySizeSum_interAtoms_le_size (S : Ty) :
    tySizeSum S.interAtoms ≤ S.size := by
  have hsize := size_eq_tySizeSum_interAtoms S
  have hlen : 1 ≤ S.interAtoms.length := interAtoms_length_pos S
  omega

theorem callableSummary_sizes_le_source
    (hwfct : WellFormedClassTable ct)
    (S : Ty) :
    (callableParamsUnion (summarizeInterAtoms hwfct S.interAtoms).callableAtoms).size ≤ S.size ∧
      (callableReturnsInter (summarizeInterAtoms hwfct S.interAtoms).callableAtoms).size ≤ S.size := by
  let summary := summarizeInterAtoms hwfct S.interAtoms
  cases hcall : summary.callableAtoms with
  | nil =>
      constructor
      · simpa [summary, hcall, callableParamsUnion, Ty.size] using Ty.size_pos S
      · simpa [summary, hcall, callableReturnsInter, Ty.size] using Ty.size_pos S
  | cons pr prs =>
      have hcallne : summary.callableAtoms ≠ [] := by
        simp [hcall]
      have hsumLe :
          tySizeSum ((pr :: prs).map callableAtomTy) ≤ tySizeSum S.interAtoms := by
        simpa [summary, hcall] using
          summarizeInterAtoms_callable_tySizeSum_le (hwfct := hwfct) (atoms := S.interAtoms)
      have hatomsLe : tySizeSum S.interAtoms ≤ S.size :=
        tySizeSum_interAtoms_le_size S
      have hP :=
        (show (callableParamsUnion (pr :: prs)).size ≤ tySizeSum ((pr :: prs).map callableAtomTy) by
          simpa [hcall] using
            callableParamsUnion_size_le_callAtoms (callAtoms := summary.callableAtoms) hcallne)
      have hR :=
        (show (callableReturnsInter (pr :: prs)).size ≤ tySizeSum ((pr :: prs).map callableAtomTy) by
          simpa [hcall] using
            callableReturnsInter_size_le_callAtoms (callAtoms := summary.callableAtoms) hcallne)
      constructor
      · exact Nat.le_trans hP (Nat.le_trans hsumLe hatomsLe)
      · exact Nat.le_trans hR (Nat.le_trans hsumLe hatomsLe)

theorem summarizeInterAtoms_nonleaf_mem_iff
    (hwfct : WellFormedClassTable ct)
    (hC : ¬ LeafBuiltin ct C) :
    C ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms ↔ .class_ C ∈ atoms := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | class_ D =>
          cases hdec : builtinLeafDecidable (C := D) hwfct with
          | isTrue hleafD =>
              have hCD : C ≠ D := by
                intro hEq
                exact hC (hEq ▸ hleafD)
              simp [summarizeInterAtoms, hdec, ih, hCD]
          | isFalse hnonleafD =>
              by_cases hCD : C = D
              · subst hCD
                simp [summarizeInterAtoms, hdec, mem_insertId]
              · simp [summarizeInterAtoms, hdec, ih, mem_insertId, hCD]
      | bottom | negClass | union | intersection | callable =>
          simp [summarizeInterAtoms, ih]

theorem summarizeInterAtoms_nonleaf_atom_mem
    (hwfct : WellFormedClassTable ct)
    (hmem : C ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms) :
    .class_ C ∈ atoms ∧ ¬ LeafBuiltin ct C := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary] at hmem
  | cons atom atoms ih =>
      cases atom with
      | class_ D =>
          cases hdec : builtinLeafDecidable (C := D) hwfct with
          | isTrue _ =>
              rcases ih (by simpa [summarizeInterAtoms, hdec] using hmem) with ⟨hmemC, hnonleafC⟩
              exact ⟨List.mem_cons_of_mem _ hmemC, hnonleafC⟩
          | isFalse hnonleafD =>
              have hmem' : C ∈ insertId D (summarizeInterAtoms hwfct atoms).nonleafClassAtoms := by
                simpa [summarizeInterAtoms, hdec] using hmem
              rcases (mem_insertId (x := D) (y := C) (xs := (summarizeInterAtoms hwfct atoms).nonleafClassAtoms)).1 hmem' with
                hCD | htail
              · subst hCD
                exact ⟨by simp, hnonleafD⟩
              · rcases ih htail with ⟨hmemC, hnonleafC⟩
                exact ⟨List.mem_cons_of_mem _ hmemC, hnonleafC⟩
      | bottom | negClass | union | intersection | callable =>
          rcases ih (by simpa [summarizeInterAtoms] using hmem) with ⟨hmemC, hnonleafC⟩
          exact ⟨List.mem_cons_of_mem _ hmemC, hnonleafC⟩

theorem summarizeInterAtoms_neg_mem_iff :
    C ∈ (summarizeInterAtoms hwfct atoms).negAtoms ↔ .negClass C ∈ atoms := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary]
  | cons atom atoms ih =>
      cases atom with
      | negClass D =>
          by_cases hCD : C = D
          · subst hCD
            simp [summarizeInterAtoms, mem_insertId]
          · simp [summarizeInterAtoms, ih, mem_insertId, hCD]
      | class_ D =>
          cases hdec : builtinLeafDecidable (C := D) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec] using ih
      | bottom | union | intersection | callable =>
          simp [summarizeInterAtoms, ih]

theorem summarizeInterAtoms_callable_mem_iff :
    pr ∈ (summarizeInterAtoms hwfct atoms).callableAtoms ↔ callableAtomTy pr ∈ atoms := by
  induction atoms with
  | nil =>
      cases pr
      simp [summarizeInterAtoms, emptyCleanSourceSummary, callableAtomTy]
  | cons atom atoms ih =>
      cases atom with
      | callable P R =>
          cases pr with
          | mk P' R' =>
              by_cases hpr : (P', R') = (P, R)
              · cases hpr
                simp [summarizeInterAtoms, mem_insertCallable, callableAtomTy]
              · have hcallneq : callableAtomTy (P', R') ≠ .callable P R := by
                  intro hEq
                  apply hpr
                  cases hEq
                  rfl
                constructor
                · intro h
                  have h' : (P', R') ∈ insertCallable (P, R) (summarizeInterAtoms hwfct atoms).callableAtoms := by
                    simpa [summarizeInterAtoms] using h
                  rcases (mem_insertCallable (pr := (P, R)) (q := (P', R'))).1 h' with hEq | hTail
                  · exact False.elim (hpr hEq)
                  · exact List.mem_cons_of_mem _ ((ih).1 hTail)
                · intro h
                  rcases List.mem_cons.mp h with hHead | hTail
                  · exfalso
                    exact hcallneq hHead
                  · have hTail' : (P', R') ∈ (summarizeInterAtoms hwfct atoms).callableAtoms :=
                      (ih).2 hTail
                    exact (mem_insertCallable (pr := (P, R)) (q := (P', R'))).2 (Or.inr hTail')
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue _ =>
              simpa [summarizeInterAtoms, hdec, callableAtomTy] using ih
          | isFalse _ =>
              simpa [summarizeInterAtoms, hdec, callableAtomTy] using ih
      | bottom | negClass | union | intersection =>
          simp [summarizeInterAtoms, ih, callableAtomTy]

theorem summarizeInterAtoms_leafAtom_mem
    (hwfct : WellFormedClassTable ct)
    (hleaf : (summarizeInterAtoms hwfct atoms).leafClassAtom = some B) :
    .class_ B ∈ atoms ∧ LeafBuiltin ct B := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary] at hleaf
  | cons atom atoms ih =>
      cases atom with
      | class_ C =>
          cases hdec : builtinLeafDecidable (C := C) hwfct with
          | isTrue hleafC =>
              let s := summarizeInterAtoms hwfct atoms
              have hupd : (updateDistinct C s.leafClassAtom s.leafConflict).1 = some B := by
                simpa [summarizeInterAtoms, s, hdec] using hleaf
              rcases updateDistinct_fst_eq_some hupd with hCB | htail
              · subst hCB
                exact ⟨by simp, hleafC⟩
              · rcases ih htail with ⟨hmem, hleafB⟩
                exact ⟨List.mem_cons_of_mem _ hmem, hleafB⟩
          | isFalse _ =>
              rcases ih (by simpa [summarizeInterAtoms, hdec] using hleaf) with ⟨hmem, hleafB⟩
              exact ⟨List.mem_cons_of_mem _ hmem, hleafB⟩
      | bottom | negClass | union | intersection | callable =>
          rcases ih (by simpa [summarizeInterAtoms] using hleaf) with ⟨hmem, hleafB⟩
          exact ⟨List.mem_cons_of_mem _ hmem, hleafB⟩

theorem summarizeInterAtoms_leaf_mem_cases
    (hwfct : WellFormedClassTable ct)
    (hleaf : LeafBuiltin ct B)
    (hmem : .class_ B ∈ atoms) :
    (summarizeInterAtoms hwfct atoms).leafConflict = true ∨
      (summarizeInterAtoms hwfct atoms).leafClassAtom = some B := by
  induction atoms with
  | nil =>
      cases hmem
  | cons atom atoms ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        cases hdec : builtinLeafDecidable (C := B) hwfct with
        | isTrue _ =>
            let s := summarizeInterAtoms hwfct atoms
            simpa [summarizeInterAtoms, s, hdec] using
              (updateDistinct_self_or_conflict
                (x := B) (curr := s.leafClassAtom) (conflict := s.leafConflict))
        | isFalse hnotleaf =>
            exact False.elim (hnotleaf hleaf)
      · cases atom with
        | class_ C =>
            cases hdec : builtinLeafDecidable (C := C) hwfct with
            | isTrue hleafC =>
                let s := summarizeInterAtoms hwfct atoms
                rcases ih htail with hconf | hsome
                · have hupd : (updateDistinct C s.leafClassAtom true).2 = true := by
                    unfold updateDistinct
                    cases s.leafClassAtom <;> simp
                  exact Or.inl (by simpa [summarizeInterAtoms, s, hdec, hconf] using hupd)
                · simpa [summarizeInterAtoms, s, hdec] using
                    updateDistinct_preserve_some_or_conflict
                    (x := C) (curr := s.leafClassAtom) (conflict := s.leafConflict) (y := B)
                    (by simpa [s] using hsome)
            | isFalse _ =>
                simpa [summarizeInterAtoms, hdec] using ih htail
        | bottom | negClass | union | intersection | callable =>
            simpa [summarizeInterAtoms] using ih htail

theorem summarizeInterAtoms_leafConflict_witness
    (hwfct : WellFormedClassTable ct)
    (hconf : (summarizeInterAtoms hwfct atoms).leafConflict = true) :
    ∃ B C, B ≠ C ∧ LeafBuiltin ct B ∧ LeafBuiltin ct C ∧ .class_ B ∈ atoms ∧ .class_ C ∈ atoms := by
  induction atoms with
  | nil =>
      simp [summarizeInterAtoms, emptyCleanSourceSummary] at hconf
  | cons atom atoms ih =>
      cases atom with
      | class_ E =>
          cases hdec : builtinLeafDecidable (C := E) hwfct with
          | isTrue hleafE =>
              let s := summarizeInterAtoms hwfct atoms
              have hupd : (updateDistinct E s.leafClassAtom s.leafConflict).2 = true := by
                simpa [summarizeInterAtoms, s, hdec] using hconf
              rcases updateDistinct_snd_eq_true hupd with htail | ⟨C, hsome, hEC⟩
              · rcases ih htail with ⟨B, C, hBC, hleafB, hleafC, hmemB, hmemC⟩
                exact ⟨B, C, hBC, hleafB, hleafC,
                  List.mem_cons_of_mem _ hmemB, List.mem_cons_of_mem _ hmemC⟩
              · rcases summarizeInterAtoms_leafAtom_mem (hwfct := hwfct) hsome with ⟨hmemC, hleafC⟩
                exact ⟨E, C, hEC, hleafE, hleafC, by simp, List.mem_cons_of_mem _ hmemC⟩
          | isFalse _ =>
              rcases ih (by simpa [summarizeInterAtoms, hdec] using hconf) with
                ⟨B, C, hBC, hleafB, hleafC, hmemB, hmemC⟩
              exact ⟨B, C, hBC, hleafB, hleafC,
                List.mem_cons_of_mem _ hmemB, List.mem_cons_of_mem _ hmemC⟩
      | bottom | negClass | union | intersection | callable =>
          rcases ih (by simpa [summarizeInterAtoms] using hconf) with
            ⟨B, C, hBC, hleafB, hleafC, hmemB, hmemC⟩
          exact ⟨B, C, hBC, hleafB, hleafC,
            List.mem_cons_of_mem _ hmemB, List.mem_cons_of_mem _ hmemC⟩

theorem leafAtom_eq_of_mem
    (hwfct : WellFormedClassTable ct)
    (hconf : (summarizeInterAtoms hwfct atoms).leafConflict = false)
    (hleafAtom : (summarizeInterAtoms hwfct atoms).leafClassAtom = some B)
    (hleaf : LeafBuiltin ct D)
    (hmem : .class_ D ∈ atoms) :
    D = B := by
  rcases summarizeInterAtoms_leaf_mem_cases (hwfct := hwfct) hleaf hmem with hconf' | hsome
  · rw [hconf] at hconf'
    cases hconf'
  · rw [hleafAtom] at hsome
    injection hsome with hEq
    exact hEq.symm

theorem no_leaf_atom_of_none
    (hwfct : WellFormedClassTable ct)
    (hconf : (summarizeInterAtoms hwfct atoms).leafConflict = false)
    (hnone : (summarizeInterAtoms hwfct atoms).leafClassAtom = none)
    (hleaf : LeafBuiltin ct D)
    (hmem : .class_ D ∈ atoms) :
    False := by
  rcases summarizeInterAtoms_leaf_mem_cases (hwfct := hwfct) hleaf hmem with hconf' | hsome
  · rw [hconf] at hconf'
    cases hconf'
  · rw [hnone] at hsome
    cases hsome

theorem no_callable_atom_of_nil
    (hcall : (summarizeInterAtoms hwfct atoms).callableAtoms = [])
    (hmem : .callable P R ∈ atoms) :
    False := by
  have hpair : (P, R) ∈ (summarizeInterAtoms hwfct atoms).callableAtoms :=
    (summarizeInterAtoms_callable_mem_iff (hwfct := hwfct) (pr := (P, R))).2 hmem
  rw [hcall] at hpair
  cases hpair

theorem no_bottom_atom_of_false
    (hbot : (summarizeInterAtoms hwfct atoms).hasBottom = false)
    (hmem : .bottom ∈ atoms) :
    False := by
  have hhas : (summarizeInterAtoms hwfct atoms).hasBottom = true :=
    (summarizeInterAtoms_hasBottom_iff (hwfct := hwfct)).2 hmem
  rw [hbot] at hhas
  cases hhas

theorem semDenotes_source_of_atoms
    (huf : S.unionFree)
    (hall : ∀ A, A ∈ S.interAtoms → Ty.semDenotes ct A obj) :
    Ty.semDenotes ct S obj := by
  exact semDenotes_at_obj_sound
    (obj := obj)
    (interAtomsFold_subtype_self (ct := ct) (T := S) huf)
    (semDenotes_interAtomsFold_intro (ct := ct) (obj := obj) (atoms := S.interAtoms) hall)

theorem subtype_source_of_atoms
    (huf : S.unionFree)
    (hall : ∀ A, A ∈ S.interAtoms → IsSubtype ct T A) :
    IsSubtype ct T S := by
  exact .trans
    (subtype_interAtomsFold_intro (ct := ct) (T := T) (atoms := S.interAtoms) hall)
    (interAtomsFold_subtype_self (ct := ct) (T := S) huf)


import FwPython.Static.Subtyping.Completeness.Infra.Summaries

/-! ### Case analysis over clean source witnesses -/

inductive CleanSourceCase
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S) : Prop where
  | empty :
      IsSubtype ct S .bottom →
      CleanSourceCase hwfct hwfS
  | currentFromLeaf
      (cname : Identifier)
      (cls : Class)
      (mro : List Identifier)
      (hleaf : LeafBuiltin ct cname)
      (hfind : findClass ct cname = some cls)
      (hmro : ComputeMro ct cls mro)
      (hden : Ty.semDenotes ct S (currentObjOf (ct := ct) cname hfind hmro))
      (hsub : IsSubtype ct S (.class_ cname))
      (hrev : IsSubtype ct (.class_ cname) S) :
      CleanSourceCase hwfct hwfS
  | freshFromSeeds
      (seeds : List Identifier)
      (hseeds_ne : seeds ≠ [])
      (hseeds_nodup : seeds.Nodup)
      (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
      (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
      (seed_source : ∀ s, s ∈ seeds → s = objectClass ∨ .class_ s ∈ S.interAtoms)
      (hden : Ty.semDenotes ct S
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
      CleanSourceCase hwfct hwfS
  | boundMethodFromCallables
      (Psum Rsum : Ty)
      (hden : Ty.semDenotes ct S (boundMethodObj (ct := ct) hwfct Psum Rsum))
      (hsub : IsSubtype ct S (.callable Psum Rsum)) :
      CleanSourceCase hwfct hwfS

def firstOutside : List Identifier → List Identifier → Option Identifier
  | [], _ => none
  | x :: xs, mro => if x ∈ mro then firstOutside xs mro else some x

theorem firstOutside_some
    (h : firstOutside xs mro = some x) :
    x ∈ xs ∧ x ∉ mro := by
  induction xs with
  | nil =>
      simp [firstOutside] at h
  | cons y ys ih =>
      unfold firstOutside at h
      by_cases hym : y ∈ mro
      · simp [hym] at h
        rcases ih h with ⟨hmem, hnot⟩
        exact ⟨List.mem_cons_of_mem _ hmem, hnot⟩
      · simp [hym] at h
        subst h
        exact ⟨List.Mem.head _, hym⟩

theorem firstOutside_none
    (h : firstOutside xs mro = none) :
    ∀ x, x ∈ xs → x ∈ mro := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      unfold firstOutside at h
      by_cases hym : y ∈ mro
      · simp [hym] at h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hym
        · exact ih h x hx
      · simp [hym] at h

def firstInside : List Identifier → List Identifier → Option Identifier
  | [], _ => none
  | x :: xs, mro => if x ∈ mro then some x else firstInside xs mro

theorem firstInside_some
    (h : firstInside xs mro = some x) :
    x ∈ xs ∧ x ∈ mro := by
  induction xs with
  | nil =>
      simp [firstInside] at h
  | cons y ys ih =>
      unfold firstInside at h
      by_cases hym : y ∈ mro
      · simp [hym] at h
        subst h
        exact ⟨List.Mem.head _, hym⟩
      · simp [hym] at h
        rcases ih h with ⟨hmem, hyes⟩
        exact ⟨List.mem_cons_of_mem _ hmem, hyes⟩

theorem firstInside_none
    (h : firstInside xs mro = none) :
    ∀ x, x ∈ xs → x ∉ mro := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      unfold firstInside at h
      by_cases hym : y ∈ mro
      · simp [hym] at h
      · simp [hym] at h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hym
        · exact ih h x hx

theorem seeds_neg_conflict_or_clear
    (seeds : List Identifier)
    (negs : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s) :
    (∃ s hs E, E ∈ negs ∧ E ∈ (seedWitness s hs).mro) ∨
      (∀ s hs E, E ∈ negs → E ∉ (seedWitness s hs).mro) := by
  induction seeds with
  | nil =>
      right
      intro s hs
      cases hs
  | cons s ss ih =>
      cases hfirst : firstInside negs (seedWitness s (by simp)).mro with
      | some E =>
          left
          rcases firstInside_some hfirst with ⟨hEmem, hEin⟩
          exact ⟨s, by simp, E, hEmem, by simpa using hEin⟩
      | none =>
          let tailWitness : ∀ s, s ∈ ss → FreshSeedInfo ct s :=
            fun s hs => seedWitness s (by simp [hs])
          have ih' :
              (∃ s hs E, E ∈ negs ∧ E ∈ (tailWitness s hs).mro) ∨
                (∀ s hs E, E ∈ negs → E ∉ (tailWitness s hs).mro) :=
            ih tailWitness
          rcases ih' with hconf | hclear
          · rcases hconf with ⟨s', hs', E, hEmem, hEin⟩
            exact Or.inl ⟨s', by simp [hs'], E, hEmem, hEin⟩
          · right
            intro s' hs' E hEmem
            rcases List.mem_cons.mp hs' with rfl | hs'
            · exact firstInside_none hfirst E hEmem
            · exact hclear s' hs' E hEmem

theorem seeds_class_hit_or_clear
    (seeds : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (D : Identifier) :
    (∃ s hs, D ∈ (seedWitness s hs).mro) ∨
      (∀ s hs, D ∉ (seedWitness s hs).mro) := by
  induction seeds with
  | nil =>
      right
      intro s hs
      cases hs
  | cons s ss ih =>
      have hsHead : s ∈ s :: ss := by simp
      by_cases hhead : D ∈ (seedWitness s hsHead).mro
      · exact Or.inl ⟨s, by simp, hhead⟩
      · let tailWitness : ∀ s, s ∈ ss → FreshSeedInfo ct s :=
            fun s hs => seedWitness s (by simp [hs])
        rcases ih tailWitness with htail | htail
        · rcases htail with ⟨s', hs', hmem⟩
          exact Or.inl ⟨s', by simp [hs'], hmem⟩
        · right
          intro s' hs'
          rcases List.mem_cons.mp hs' with rfl | hs'
          · exact hhead
          · exact htail s' hs'

theorem analyzeCleanSource
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree) :
    CleanSourceCase (ct := ct) (S := S) hwfct hwfS := by
  let atoms : List Ty := S.interAtoms
  let summary : CleanSourceSummary := summarizeInterAtoms hwfct atoms
  have hatoms : atoms = S.interAtoms := rfl
  have hsummary : summary = summarizeInterAtoms hwfct atoms := rfl
  have hproj : ∀ {A}, A ∈ atoms → IsSubtype ct S A := by
    intro A hmem
    have hmem' : A ∈ S.interAtoms := by simpa [hatoms] using hmem
    exact interAtoms_projection (ct := ct) (T := S) (A := A) huf hmem'
  have hwfAtom : ∀ {A}, A ∈ atoms → WellFormedTy ct A := by
    intro A hmem
    have hmem' : A ∈ S.interAtoms := by simpa [hatoms] using hmem
    exact interAtoms_member_wellFormed (ct := ct) (T := S) (A := A) hwfS huf hmem'
  have hnoUnionAtom : ∀ {T U}, .union T U ∈ atoms → False := by
    intro T U hmem
    have hmem' : .union T U ∈ S.interAtoms := by simpa [hatoms] using hmem
    exact interAtoms_union_not_mem S T U huf hmem'
  have hnoInterAtom : ∀ {T U}, .intersection T U ∈ atoms → False := by
    intro T U hmem
    have hmem' : .intersection T U ∈ S.interAtoms := by simpa [hatoms] using hmem
    exact interAtoms_intersection_not_mem S T U huf hmem'
  cases hbot : summary.hasBottom with
  | true =>
      have hbot' : (summarizeInterAtoms hwfct atoms).hasBottom = true := by
        simpa [hsummary] using hbot
      have hmemBot : .bottom ∈ atoms :=
        (summarizeInterAtoms_hasBottom_iff (hwfct := hwfct) (atoms := atoms)).1 hbot'
      exact .empty (hproj hmemBot)
  | false =>
      have hbot' : (summarizeInterAtoms hwfct atoms).hasBottom = false := by
        simpa [hsummary] using hbot
      cases hleafconf : summary.leafConflict with
      | true =>
          have hleafconf' : (summarizeInterAtoms hwfct atoms).leafConflict = true := by
            simpa [hsummary] using hleafconf
          rcases summarizeInterAtoms_leafConflict_witness (hwfct := hwfct) (atoms := atoms) hleafconf' with
            ⟨B, C, hBC, hleafB, hleafC, hmemB, hmemC⟩
          exact .empty <| .trans
            (.interIntro (hproj hmemB) (hproj hmemC))
            (leaf_conflict_bottom (ct := ct) (B := B) (C := C) hwfct hleafB hleafC hBC)
      | false =>
          have hleafconf' : (summarizeInterAtoms hwfct atoms).leafConflict = false := by
            simpa [hsummary] using hleafconf
          cases hcall : summary.callableAtoms with
          | nil =>
              have hcall' : (summarizeInterAtoms hwfct atoms).callableAtoms = [] := by
                simpa [hsummary] using hcall
              cases hleafAtom : summary.leafClassAtom with
                      | some B =>
                          have hleafAtom' :
                              (summarizeInterAtoms hwfct atoms).leafClassAtom = some B := by
                            simpa [hsummary] using hleafAtom
                          rcases summarizeInterAtoms_leafAtom_mem
                            (ct := ct) (B := B) (atoms := atoms) hwfct hleafAtom' with
                            ⟨hmemB, hleafB⟩
                          obtain ⟨bcls, bmro, hfindB, hmroB⟩ :=
                            leafBuiltin_find_mro (ct := ct) (B := B) hwfct hleafB
                          cases hnonleafOff : firstOutside summary.nonleafClassAtoms bmro with
                          | some C =>
                              rcases firstOutside_some hnonleafOff with ⟨hCmemList, hCnotmem⟩
                              rcases summarizeInterAtoms_nonleaf_atom_mem
                                (ct := ct) (C := C) (atoms := atoms) hwfct
                                (by simpa [hsummary] using hCmemList) with ⟨hmemC, _⟩
                              exact .empty <| .trans
                                (.interIntro (hproj hmemC) (hproj hmemB))
                                (leaf_inter_class_outside_bottom
                                  (ct := ct) (B := B) (C := C) hleafB hfindB hmroB hCnotmem)
                          | none =>
                              have hnonleafClear :
                                  ∀ C, C ∈ summary.nonleafClassAtoms → C ∈ bmro :=
                                firstOutside_none hnonleafOff
                              cases hnegOff : firstInside summary.negAtoms bmro with
                              | some E =>
                                  rcases firstInside_some hnegOff with ⟨hEmemList, hEmem⟩
                                  have hmemE : .negClass E ∈ atoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                      (by simpa [hsummary] using hEmemList)
                                  exact .empty <| .trans
                                    (.interIntro (hproj hmemB) (hproj hmemE))
                                    (classNegClassBottom
                                      (.class_ hfindB hmroB hEmem))
                              | none =>
                                  have hnegClear :
                                      ∀ E, E ∈ summary.negAtoms → E ∉ bmro :=
                                    firstInside_none hnegOff
                                  have hclassMem : ∀ D, .class_ D ∈ atoms → D ∈ bmro := by
                                    intro D hmemD
                                    cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                    | isTrue hleafD =>
                                        have hDB := leafAtom_eq_of_mem
                                          (ct := ct) (B := B) (D := D) (atoms := atoms)
                                          hwfct hleafconf' hleafAtom' hleafD hmemD
                                        subst D
                                        simpa [findClass_name hfindB] using mro_self_mem hmroB
                                    | isFalse hnonleafD =>
                                        have hDmemList : D ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms :=
                                          (summarizeInterAtoms_nonleaf_mem_iff
                                            (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                        exact hnonleafClear D (by simpa [hsummary] using hDmemList)
                                  have hnegNotMem : ∀ E, .negClass E ∈ atoms → E ∉ bmro := by
                                    intro E hmemE
                                    have hEmemList : E ∈ (summarizeInterAtoms hwfct atoms).negAtoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
                                    exact hnegClear E (by simpa [hsummary] using hEmemList)
                                  have hden :
                                      Ty.semDenotes ct S
                                        (currentObjOf (ct := ct) B hfindB hmroB) := by
                                    refine semDenotes_source_of_atoms (ct := ct) (S := S)
                                      (obj := currentObjOf (ct := ct) B hfindB hmroB) huf ?_
                                    intro A hmemA
                                    cases A with
                                    | bottom =>
                                        exact False.elim <| no_bottom_atom_of_false
                                          (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                    | class_ D =>
                                        exact (currentObjOf_denotes_class
                                          (ct := ct) (C := B) (D := D) hfindB hmroB).2
                                          (hclassMem D hmemA)
                                    | negClass E =>
                                        exact (currentObjOf_denotes_neg_iff
                                          (ct := ct) (C := B) (D := E) hfindB hmroB).2
                                          (hnegNotMem E hmemA)
                                    | callable P R =>
                                        exact False.elim <|
                                          no_callable_atom_of_nil
                                            (hwfct := hwfct) (atoms := atoms)
                                            (P := P) (R := R) hcall' hmemA
                                    | union T U =>
                                        exact False.elim (hnoUnionAtom hmemA)
                                    | intersection T U =>
                                        exact False.elim (hnoInterAtom hmemA)
                                  have hrev :
                                      IsSubtype ct (.class_ B) S := by
                                    refine subtype_source_of_atoms (ct := ct) (T := .class_ B)
                                      (S := S) huf ?_
                                    intro A hmemA
                                    cases A with
                                    | bottom =>
                                        exact False.elim <| no_bottom_atom_of_false
                                          (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                    | class_ D =>
                                        cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                        | isTrue hleafD =>
                                            have hDB := leafAtom_eq_of_mem
                                              (ct := ct) (B := B) (D := D) (atoms := atoms)
                                              hwfct hleafconf' hleafAtom' hleafD hmemA
                                            subst D
                                            exact .refl
                                        | isFalse _ =>
                                            exact .class_ hfindB hmroB (hclassMem D hmemA)
                                    | negClass E =>
                                        exact .sealedClassNegClass hleafB hfindB hmroB (hnegNotMem E hmemA)
                                    | callable P R =>
                                        exact False.elim <|
                                          no_callable_atom_of_nil
                                            (hwfct := hwfct) (atoms := atoms)
                                            (P := P) (R := R) hcall' hmemA
                                    | union T U =>
                                        exact False.elim (hnoUnionAtom hmemA)
                                    | intersection T U =>
                                        exact False.elim (hnoInterAtom hmemA)
                                  exact .currentFromLeaf B bcls bmro hleafB hfindB hmroB hden (hproj hmemB) hrev
                      | none =>
                          have hleafAtom' :
                              (summarizeInterAtoms hwfct atoms).leafClassAtom = none := by
                            simpa [hsummary] using hleafAtom
                          cases hseeds : summary.nonleafClassAtoms with
                          | nil =>
                              have hseeds' :
                                  (summarizeInterAtoms hwfct atoms).nonleafClassAtoms = [] := by
                                simpa [hsummary] using hseeds
                              by_cases hobjNeg : objectClass ∈ summary.negAtoms
                              · have hobjNeg' : objectClass ∈ (summarizeInterAtoms hwfct atoms).negAtoms := by
                                  simpa [hsummary] using hobjNeg
                                have hmemObj : .negClass objectClass ∈ atoms :=
                                  (summarizeInterAtoms_neg_mem_iff
                                    (hwfct := hwfct) (atoms := atoms) (C := objectClass)).1 hobjNeg'
                                exact .empty <| .trans
                                  (hproj hmemObj)
                                  (negClass_bottom_of_objectSubtype
                                    (ct := ct) (C := objectClass) hwfct .refl)
                              · let seedWitness : ∀ s, s ∈ [objectClass] → FreshSeedInfo ct s := fun s hs => by
                                   simp at hs
                                   subst hs
                                   exact ⟨hwfct.objectExists.cls, [objectClass],
                                     hwfct.objectExists.hfind, mro_of_object (ct := ct) hwfct⟩
                                let seed_nonleaf : ∀ s, s ∈ [objectClass] → ¬ LeafBuiltin ct s := fun s hs => by
                                  simp at hs
                                  subst hs
                                  exact object_not_leaf (ct := ct) hwfct
                                let seed_source : ∀ s, s ∈ [objectClass] → s = objectClass ∨ .class_ s ∈ S.interAtoms := fun s hs => by
                                  simp at hs
                                  subst hs
                                  exact Or.inl rfl
                                have hden :
                                    Ty.semDenotes ct S
                                      (freshSeedsObj (ct := ct)
                                        [objectClass] (by simp) (by simp) seedWitness seed_nonleaf) := by
                                  refine semDenotes_source_of_atoms (ct := ct) (S := S)
                                    (obj := freshSeedsObj (ct := ct)
                                      [objectClass] (by simp) (by simp) seedWitness seed_nonleaf) huf ?_
                                  intro A hmemA
                                  cases A with
                                  | bottom =>
                                      exact False.elim <| no_bottom_atom_of_false
                                        (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                  | class_ D =>
                                      cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                      | isTrue hleafD =>
                                          exact False.elim <|
                                            no_leaf_atom_of_none
                                              (hwfct := hwfct) (atoms := atoms) (D := D)
                                              hleafconf' hleafAtom' hleafD hmemA
                                      | isFalse hnonleafD =>
                                          have hDmemList : D ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms :=
                                            (summarizeInterAtoms_nonleaf_mem_iff
                                              (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemA
                                          rw [hseeds'] at hDmemList
                                          cases hDmemList
                                  | negClass E =>
                                      have hEmemList : E ∈ (summarizeInterAtoms hwfct atoms).negAtoms :=
                                        (summarizeInterAtoms_neg_mem_iff
                                          (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemA
                                      have hEne : E ≠ objectClass := by
                                        intro hEq
                                        apply hobjNeg
                                        simpa [hEq] using hEmemList
                                      exact (freshSeedsObj_denotes_neg_iff
                                        (ct := ct) (C := E)
                                        [objectClass] (by simp) (by simp)
                                        seedWitness seed_nonleaf).2 <| by
                                          intro hanc
                                          rcases hanc with ⟨s, hs, hEin⟩
                                          simp at hs
                                          subst hs
                                          have : E = objectClass := by
                                            simpa [seedWitness] using hEin
                                          exact hEne this
                                  | callable P R =>
                                      exact False.elim <|
                                        no_callable_atom_of_nil
                                          (hwfct := hwfct) (atoms := atoms)
                                          (P := P) (R := R) hcall' hmemA
                                  | union T U =>
                                      exact False.elim (hnoUnionAtom hmemA)
                                  | intersection T U =>
                                      exact False.elim (hnoInterAtom hmemA)
                                exact .freshFromSeeds
                                  [objectClass] (by simp) (by simp) seedWitness seed_nonleaf seed_source hden
                          | cons s ss =>
                              let seeds := summary.nonleafClassAtoms
                              have hseeds_ne : seeds ≠ [] := by
                                intro hnil
                                have : summary.nonleafClassAtoms = [] := by
                                  simpa [seeds] using hnil
                                rw [hseeds] at this
                                simp at this
                              have hseeds_nodup : seeds.Nodup := by
                                simpa [hsummary] using summarizeInterAtoms_nonleaf_nodup
                                  (hwfct := hwfct) (atoms := atoms)
                              let seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s := fun s hs => by
                                rcases summarizeInterAtoms_nonleaf_atom_mem
                                  (ct := ct) (C := s) (atoms := atoms) hwfct
                                  (by simpa [seeds, hsummary] using hs) with ⟨hmemS, _⟩
                                have hfind_ne : findClass ct s ≠ none :=
                                  (hwfAtom hmemS).class_find_ne_none
                                cases hfindS : findClass ct s with
                                | none =>
                                    exact False.elim (hfind_ne hfindS)
                                | some clsS =>
                                    let hmroS := hwfct.allMrosExist s clsS hfindS
                                    exact ⟨clsS, hmroS.mro, hfindS, hmroS.hmro⟩
                              let seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s := fun s hs => by
                                exact (summarizeInterAtoms_nonleaf_atom_mem
                                  (ct := ct) (C := s) (atoms := atoms) hwfct
                                  (by simpa [seeds, hsummary] using hs)).2
                              let seed_source : ∀ s, s ∈ seeds → s = objectClass ∨ .class_ s ∈ S.interAtoms := fun s hs => by
                                exact Or.inr <|
                                  (summarizeInterAtoms_nonleaf_atom_mem
                                    (ct := ct) (C := s) (atoms := atoms) hwfct
                                    (by simpa [seeds, hsummary] using hs)).1
                              rcases seeds_neg_conflict_or_clear
                                (ct := ct)
                                seeds
                                summary.negAtoms
                                seedWitness with hconf | hclear
                              · rcases hconf with ⟨s, hs, E, hEmemList, hEin⟩
                                rcases summarizeInterAtoms_nonleaf_atom_mem
                                  (ct := ct) (C := s) (atoms := atoms) hwfct
                                  (by simpa [seeds, hsummary] using hs) with ⟨hmemS, _⟩
                                have hmemE : .negClass E ∈ atoms :=
                                  (summarizeInterAtoms_neg_mem_iff
                                    (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                    (by simpa [hsummary] using hEmemList)
                                let info := seedWitness s hs
                                exact .empty <| .trans
                                  (.interIntro (hproj hmemS) (hproj hmemE))
                                  (classNegClassBottom
                                    (.class_ info.hfind info.hmro hEin))
                              · have hden :
                                    Ty.semDenotes ct S
                                      (freshSeedsObj (ct := ct)
                                        seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
                                  refine semDenotes_source_of_atoms (ct := ct) (S := S)
                                    (obj := freshSeedsObj (ct := ct)
                                      seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) huf ?_
                                  intro A hmemA
                                  cases A with
                                  | bottom =>
                                      exact False.elim <| no_bottom_atom_of_false
                                        (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                  | class_ D =>
                                      cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                      | isTrue hleafD =>
                                          exact False.elim <|
                                            no_leaf_atom_of_none
                                              (hwfct := hwfct) (atoms := atoms) (D := D)
                                              hleafconf' hleafAtom' hleafD hmemA
                                      | isFalse hnonleafD =>
                                          have hDmemSeeds : D ∈ seeds :=
                                            (summarizeInterAtoms_nonleaf_mem_iff
                                              (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemA
                                          have hself : D ∈ (seedWitness D hDmemSeeds).mro := by
                                            simpa [findClass_name (seedWitness D hDmemSeeds).hfind] using
                                              mro_self_mem (seedWitness D hDmemSeeds).hmro
                                          exact (freshSeedsObj_denotes_class_iff
                                            (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup
                                            seedWitness seed_nonleaf).2
                                            ⟨D, hDmemSeeds, hself⟩
                                  | negClass E =>
                                      have hEmemList : E ∈ summary.negAtoms :=
                                        (summarizeInterAtoms_neg_mem_iff
                                          (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemA
                                      exact (freshSeedsObj_denotes_neg_iff
                                        (ct := ct) (C := E) seeds hseeds_ne hseeds_nodup
                                        seedWitness seed_nonleaf).2 <|
                                        by
                                          intro hex
                                          rcases hex with ⟨s, hs, hEin⟩
                                          exact hclear s hs E hEmemList hEin
                                  | callable P R =>
                                      exact False.elim <|
                                        no_callable_atom_of_nil
                                          (hwfct := hwfct) (atoms := atoms)
                                          (P := P) (R := R) hcall' hmemA
                                  | union T U =>
                                      exact False.elim (hnoUnionAtom hmemA)
                                  | intersection T U =>
                                      exact False.elim (hnoInterAtom hmemA)
                                exact .freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden
              | cons pr prs =>
                  have hcall' : (summarizeInterAtoms hwfct atoms).callableAtoms = pr :: prs := by
                    simpa [hsummary] using hcall
                  have hcallne : summary.callableAtoms ≠ [] := by
                    simp [hcall]
                  let Psum := callableParamsUnion summary.callableAtoms
                  let Rsum := callableReturnsInter summary.callableAtoms
                  have hcallSub :
                      IsSubtype ct S (.callable Psum Rsum) := by
                    refine source_projects_callable_summary
                      (ct := ct) (T := S) huf (callAtoms := summary.callableAtoms) hcallne ?_
                    intro pr hpr
                    exact (summarizeInterAtoms_callable_mem_iff
                      (hwfct := hwfct) (atoms := atoms) (pr := pr)).1 <|
                      by simpa [hsummary] using hpr
                  cases hleafAtom : summary.leafClassAtom with
                      | some B =>
                          have hleafAtom' :
                              (summarizeInterAtoms hwfct atoms).leafClassAtom = some B := by
                            simpa [hsummary] using hleafAtom
                          rcases summarizeInterAtoms_leafAtom_mem
                            (ct := ct) (B := B) (atoms := atoms) hwfct hleafAtom' with
                            ⟨hmemB, _⟩
                          by_cases hBmem : B ∈ hwfct.boundMethodExists.mro
                          · cases hnonleafOff : firstOutside summary.nonleafClassAtoms hwfct.boundMethodExists.mro with
                            | some D =>
                                rcases firstOutside_some hnonleafOff with ⟨hDmemList, hDnotmem⟩
                                rcases summarizeInterAtoms_nonleaf_atom_mem
                                  (ct := ct) (C := D) (atoms := atoms) hwfct
                                  (by simpa [hsummary] using hDmemList) with ⟨hmemD, _⟩
                                exact .empty <| .trans
                                  (.interIntro (hproj hmemD) hcallSub)
                                  (leaf_class_callable_bottom
                                    (ct := ct) (C := D) (P := Psum) (R := Rsum)
                                    (leafBuiltin_boundMethod hwfct)
                                    hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro
                                    hDnotmem)
                            | none =>
                                have hnonleafClear :
                                    ∀ D, D ∈ summary.nonleafClassAtoms → D ∈ hwfct.boundMethodExists.mro :=
                                  firstOutside_none hnonleafOff
                                cases hnegOff : firstInside summary.negAtoms hwfct.boundMethodExists.mro with
                                | some E =>
                                    rcases firstInside_some hnegOff with ⟨hEmemList, hEmem⟩
                                    have hmemE : .negClass E ∈ atoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                        (by simpa [hsummary] using hEmemList)
                                    have hclassE : IsSubtype ct S (.class_ E) := by
                                      exact .trans hcallSub <| .trans
                                        (callable_to_class (ct := ct) (P := Psum) (R := Rsum) hwfct)
                                        (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hEmem)
                                    exact .empty <| .trans
                                      (.interIntro hclassE (hproj hmemE))
                                      .classSelfNegClassBottom
                                | none =>
                                    have hnegClear :
                                        ∀ E, E ∈ summary.negAtoms → E ∉ hwfct.boundMethodExists.mro :=
                                      firstInside_none hnegOff
                                    have hden :
                                        Ty.semDenotes ct S
                                          (boundMethodObj (ct := ct) hwfct Psum Rsum) := by
                                      refine semDenotes_source_of_atoms (ct := ct) (S := S)
                                        (obj := boundMethodObj (ct := ct) hwfct Psum Rsum) huf ?_
                                      intro A hmemA
                                      cases A with
                                      | bottom =>
                                          exact False.elim <| no_bottom_atom_of_false
                                            (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                      | class_ D =>
                                          cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                          | isTrue hleafD =>
                                              have hDB := leafAtom_eq_of_mem
                                                (ct := ct) (B := B) (D := D) (atoms := atoms)
                                                hwfct hleafconf' hleafAtom' hleafD hmemA
                                              subst D
                                              exact (boundMethodObj_denotes_class_iff
                                                (ct := ct) (C := B) (P := Psum) (R := Rsum) hwfct).2 hBmem
                                          | isFalse hnonleafD =>
                                              have hDmemList : D ∈ summary.nonleafClassAtoms :=
                                                (summarizeInterAtoms_nonleaf_mem_iff
                                                  (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemA
                                              exact (boundMethodObj_denotes_class_iff
                                                (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).2
                                                (hnonleafClear D hDmemList)
                                      | negClass E =>
                                          have hEmemList : E ∈ summary.negAtoms :=
                                            (summarizeInterAtoms_neg_mem_iff
                                              (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemA
                                          exact (boundMethodObj_denotes_neg_iff
                                            (ct := ct) (C := E) (P := Psum) (R := Rsum) hwfct).2
                                            (hnegClear E hEmemList)
                                      | callable P R =>
                                          have hpair : (P, R) ∈ summary.callableAtoms :=
                                            (summarizeInterAtoms_callable_mem_iff
                                              (hwfct := hwfct) (atoms := atoms) (pr := (P, R))).2 hmemA
                                          simpa [Psum, Rsum] using
                                            boundMethodObj_denotes_callable_of_mem
                                              (ct := ct) (pr := (P, R))
                                              (callAtoms := summary.callableAtoms) hwfct hpair
                                      | union T U =>
                                          exact False.elim (hnoUnionAtom hmemA)
                                      | intersection T U =>
                                          exact False.elim (hnoInterAtom hmemA)
                                    exact .boundMethodFromCallables Psum Rsum hden hcallSub
                          · exact .empty <| .trans
                              (.interIntro (hproj hmemB) hcallSub)
                              (leaf_class_callable_bottom
                                (ct := ct) (C := B) (P := Psum) (R := Rsum)
                                (leafBuiltin_boundMethod hwfct)
                                hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro
                                hBmem)
                      | none =>
                          have hleafAtom' :
                              (summarizeInterAtoms hwfct atoms).leafClassAtom = none := by
                            simpa [hsummary] using hleafAtom
                          cases hnonleafOff : firstOutside summary.nonleafClassAtoms hwfct.boundMethodExists.mro with
                          | some D =>
                              rcases firstOutside_some hnonleafOff with ⟨hDmemList, hDnotmem⟩
                              rcases summarizeInterAtoms_nonleaf_atom_mem
                                (ct := ct) (C := D) (atoms := atoms) hwfct
                                (by simpa [hsummary] using hDmemList) with ⟨hmemD, _⟩
                              exact .empty <| .trans
                                (.interIntro (hproj hmemD) hcallSub)
                                (leaf_class_callable_bottom
                                  (ct := ct) (C := D) (P := Psum) (R := Rsum)
                                  (leafBuiltin_boundMethod hwfct)
                                  hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro
                                  hDnotmem)
                          | none =>
                              have hnonleafClear :
                                  ∀ D, D ∈ summary.nonleafClassAtoms → D ∈ hwfct.boundMethodExists.mro :=
                                firstOutside_none hnonleafOff
                              cases hnegOff : firstInside summary.negAtoms hwfct.boundMethodExists.mro with
                              | some E =>
                                  rcases firstInside_some hnegOff with ⟨hEmemList, hEmem⟩
                                  have hmemE : .negClass E ∈ atoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                      (by simpa [hsummary] using hEmemList)
                                  have hclassE : IsSubtype ct S (.class_ E) := by
                                    exact .trans hcallSub <| .trans
                                      (callable_to_class (ct := ct) (P := Psum) (R := Rsum) hwfct)
                                      (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hEmem)
                                  exact .empty <| .trans
                                    (.interIntro hclassE (hproj hmemE))
                                    .classSelfNegClassBottom
                              | none =>
                                  have hnegClear :
                                      ∀ E, E ∈ summary.negAtoms → E ∉ hwfct.boundMethodExists.mro :=
                                    firstInside_none hnegOff
                                  have hden :
                                      Ty.semDenotes ct S
                                        (boundMethodObj (ct := ct) hwfct Psum Rsum) := by
                                    refine semDenotes_source_of_atoms (ct := ct) (S := S)
                                      (obj := boundMethodObj (ct := ct) hwfct Psum Rsum) huf ?_
                                    intro A hmemA
                                    cases A with
                                    | bottom =>
                                        exact False.elim <| no_bottom_atom_of_false
                                          (hwfct := hwfct) (atoms := atoms) hbot' hmemA
                                    | class_ D =>
                                        cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                        | isTrue hleafD =>
                                            exact False.elim <|
                                              no_leaf_atom_of_none
                                                (hwfct := hwfct) (atoms := atoms) (D := D)
                                                hleafconf' hleafAtom' hleafD hmemA
                                        | isFalse hnonleafD =>
                                            have hDmemList : D ∈ summary.nonleafClassAtoms :=
                                              (summarizeInterAtoms_nonleaf_mem_iff
                                                (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemA
                                            exact (boundMethodObj_denotes_class_iff
                                              (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).2
                                              (hnonleafClear D hDmemList)
                                    | negClass E =>
                                        have hEmemList : E ∈ summary.negAtoms :=
                                          (summarizeInterAtoms_neg_mem_iff
                                            (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemA
                                        exact (boundMethodObj_denotes_neg_iff
                                          (ct := ct) (C := E) (P := Psum) (R := Rsum) hwfct).2
                                          (hnegClear E hEmemList)
                                    | callable P R =>
                                        have hpair : (P, R) ∈ summary.callableAtoms :=
                                          (summarizeInterAtoms_callable_mem_iff
                                            (hwfct := hwfct) (atoms := atoms) (pr := (P, R))).2 hmemA
                                        simpa [Psum, Rsum] using
                                          boundMethodObj_denotes_callable_of_mem
                                            (ct := ct) (pr := (P, R))
                                            (callAtoms := summary.callableAtoms) hwfct hpair
                                    | union T U =>
                                        exact False.elim (hnoUnionAtom hmemA)
                                    | intersection T U =>
                                        exact False.elim (hnoInterAtom hmemA)
                                  exact .boundMethodFromCallables Psum Rsum hden hcallSub

def cleanSourceSeedWitness
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree) :
    ∀ s, s ∈ (summarizeInterAtoms hwfct S.interAtoms).nonleafClassAtoms → FreshSeedInfo ct s := by
  intro s hs
  rcases summarizeInterAtoms_nonleaf_atom_mem
    (ct := ct) (C := s) (atoms := S.interAtoms) hwfct hs with ⟨hmemS, _⟩
  have hwfClass : WellFormedTy ct (.class_ s) :=
    interAtoms_member_wellFormed (ct := ct) (T := S) (A := .class_ s) hwfS huf hmemS
  have hfind_ne : findClass ct s ≠ none := hwfClass.class_find_ne_none
  cases hfindS : findClass ct s with
  | none =>
      exact False.elim (hfind_ne hfindS)
  | some clsS =>
      let hmroS := hwfct.allMrosExist s clsS hfindS
      exact ⟨clsS, hmroS.mro, hfindS, hmroS.hmro⟩

theorem cleanSourceSeed_nonleaf
    (hwfct : WellFormedClassTable ct)
    (hs : s ∈ (summarizeInterAtoms hwfct (Ty.interAtoms S)).nonleafClassAtoms) :
    ¬ LeafBuiltin ct s :=
  (summarizeInterAtoms_nonleaf_atom_mem
    (ct := ct) (C := s) (atoms := Ty.interAtoms S) hwfct hs).2

theorem freshSeedInfo_object_mro
    (hwfct : WellFormedClassTable ct)
    (info : FreshSeedInfo ct objectClass) :
    info.mro = [objectClass] := by
  cases info with
  | mk cls mro hfind hmro =>
      have hcls : cls = hwfct.objectExists.cls := by
        rw [hwfct.objectExists.hfind] at hfind
        injection hfind with hEq
        exact hEq.symm
      subst hcls
      exact object_mro_unique (ct := ct) hwfct hmro

theorem complete_clean_bottom
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hsem : SemSubtype ct S .bottom) :
    IsSubtype ct S .bottom := by
  cases analyzeCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | empty hsub =>
      exact hsub
  | currentFromLeaf _ _ _ _ _ _ hden _ _ =>
      exact False.elim (hsem _ hden)
  | freshFromSeeds _ _ _ _ _ _ hden =>
      exact False.elim (hsem _ hden)
  | boundMethodFromCallables _ _ hden _ =>
      exact False.elim (hsem _ hden)

theorem complete_clean_class_nonobject
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hwfT : WellFormedTy ct (.class_ D))
    (hD : D ≠ objectClass)
    (hsem : SemSubtype ct S (.class_ D)) :
    IsSubtype ct S (.class_ D) := by
  cases analyzeCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | empty hsub =>
      exact .trans hsub .bottom
  | currentFromLeaf cname cls mro hleaf hfind hmro hden hsub hrev =>
      have hsem' : SemSubtype ct (.class_ cname) (.class_ D) :=
        SemSubtype.trans (semSubtype_sound hrev) hsem
      exact .trans hsub <|
        complete_class_class
          (ct := ct) (C := cname) (D := D)
          hwfct (.class_ hfind hmro) hwfT hsem'
  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden =>
      have hclass :
          Ty.semDenotes ct (.class_ D)
            (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) :=
        hsem _ hden
      rcases (freshSeedsObj_denotes_class_iff
        (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1 hclass with
        ⟨s, hs, hmemD⟩
      rcases seed_source s hs with rfl | hmemS
      · let info := seedWitness objectClass hs
        have hmroObj : info.mro = [objectClass] :=
          freshSeedInfo_object_mro (ct := ct) hwfct info
        have : D = objectClass := by simpa [info, hmroObj] using hmemD
        exact False.elim (hD this)
      · let info := seedWitness s hs
        exact .trans
          (interAtoms_projection (ct := ct) (T := S) (A := .class_ s) huf hmemS)
          (.class_ info.hfind info.hmro hmemD)
  | boundMethodFromCallables Psum Rsum hden hsub =>
      have hmem : D ∈ hwfct.boundMethodExists.mro :=
        (boundMethodObj_denotes_class_iff
          (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).1 (hsem _ hden)
      exact .trans hsub <| .trans
        (callable_to_class (ct := ct) (P := Psum) (R := Rsum) hwfct)
        (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hmem)

theorem complete_clean_callable
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hsem : SemSubtype ct S (.callable P R)) :
    IsSubtype ct S (.callable P R) := by
  cases analyzeCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | empty hsub =>
      exact .trans hsub .bottom
  | currentFromLeaf cname cls mro hleaf hfind hmro hden hsub hrev =>
      have hsem' : SemSubtype ct (.class_ cname) (.callable P R) :=
        SemSubtype.trans (semSubtype_sound hrev) hsem
      exact False.elim (not_semSubtype_class_callable (ct := ct) (.class_ hfind hmro) hsem')
  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden =>
      exact False.elim <|
        freshSeedsObj_not_denotes_callable
          (ct := ct) (P := P) (R := R)
          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
          (hsem _ hden)
  | boundMethodFromCallables Psum Rsum hden hsub =>
      exact .trans hsub <|
        callable_summary_intro (ct := ct) (P := P) (R := R)
          (Psum := Psum) (Rsum := Rsum) hwfct (hsem _ hden)

theorem complete_clean_neg
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hwfT : WellFormedTy ct (.negClass D))
    (hsem : SemSubtype ct S (.negClass D)) :
    IsSubtype ct S (.negClass D) := by
  obtain ⟨clsD, mroD, hfindD, hmroD⟩ := hwfT.negClass_find
  cases analyzeCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | empty hsub =>
      exact .trans hsub .bottom
  | currentFromLeaf cname cls mro hleaf hfind hmro hden hsub hrev =>
      have hsem' : SemSubtype ct (.class_ cname) (.negClass D) :=
        SemSubtype.trans (semSubtype_sound hrev) hsem
      exact .trans hsub <|
        complete_class_neg
          (ct := ct) (C := cname) (D := D)
          hwfct (.class_ hfind hmro) hwfT hsem'
  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden =>
      let oldW :=
        freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
      have holdAtom : ∀ A, A ∈ S.interAtoms → Ty.semDenotes ct A oldW := by
        intro A hmemA
        exact semDenotes_at_obj_sound
          (ct := ct)
          (obj := oldW)
          (interAtoms_projection (ct := ct) (T := S) (A := A) huf hmemA)
          hden
      let negAtoms := (summarizeInterAtoms hwfct S.interAtoms).negAtoms
      cases hnegHit : firstInside negAtoms mroD with
      | some E =>
          rcases firstInside_some hnegHit with ⟨hEmemList, hEmem⟩
          have hmemE : .negClass E ∈ S.interAtoms :=
            (summarizeInterAtoms_neg_mem_iff
              (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).1 hEmemList
          exact .trans
            (interAtoms_projection (ct := ct) (T := S) (A := .negClass E) huf hmemE)
            (negClassAntitone
              (.class_ hfindD hmroD hEmem))
      | none =>
          have hnegClear :
              ∀ E, E ∈ negAtoms → E ∉ mroD :=
            firstInside_none hnegHit
          cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
          | isTrue hleafD =>
              cases hseedOff : firstOutside seeds mroD with
              | some s =>
                  rcases firstOutside_some hseedOff with ⟨hs, hsOut⟩
                  rcases seed_source s hs with rfl | hmemS
                  · exact False.elim <| hsOut <| mro_contains_object hmroD
                  · exact .trans
                      (interAtoms_projection (ct := ct) (T := S) (A := .class_ s) huf hmemS)
                      (leafBuiltinNegClass
                        (ct := ct) (B := D) (C := s)
                        hleafD hfindD hmroD hsOut)
              | none =>
                  have hseedAll : ∀ s, s ∈ seeds → s ∈ mroD :=
                    firstOutside_none hseedOff
                  have hclassMem : ∀ C, .class_ C ∈ S.interAtoms → C ∈ mroD := by
                    intro C hmemC
                    have holdC : Ty.semDenotes ct (.class_ C) oldW := holdAtom (.class_ C) hmemC
                    rcases (freshSeedsObj_denotes_class_iff
                      (ct := ct) (C := C) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1 holdC with
                      ⟨s, hs, hCmem⟩
                    let info := seedWitness s hs
                    have hsIn : s ∈ mroD := hseedAll s hs
                    have hsIn' : info.cls.name ∈ mroD := by
                      simpa [findClass_name info.hfind] using hsIn
                    have hfindSelfD : findClass ct clsD.name = some clsD := by
                      simpa [findClass_name hfindD] using hfindD
                    have hfindInfo : findClass ct info.cls.name = some info.cls := by
                      simpa [findClass_name info.hfind] using info.hfind
                    exact mro_mem_trans ct clsD info.cls mroD info.mro C
                      hfindSelfD hmroD hfindInfo info.hmro hsIn' hCmem
                  have hdenCur :
                      Ty.semDenotes ct S
                        (currentObjOf (ct := ct) D hfindD hmroD) := by
                    refine semDenotes_source_of_atoms (ct := ct) (S := S)
                      (obj := currentObjOf (ct := ct) D hfindD hmroD) huf ?_
                    intro A hmemA
                    cases A with
                    | bottom =>
                        exact False.elim (holdAtom .bottom hmemA)
                    | class_ C =>
                        exact (currentObjOf_denotes_class
                          (ct := ct) (C := D) (D := C) hfindD hmroD).2
                          (hclassMem C hmemA)
                    | negClass E =>
                        have hEmemList : E ∈ negAtoms :=
                          (summarizeInterAtoms_neg_mem_iff
                            (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).2 hmemA
                        exact (currentObjOf_denotes_neg_iff
                          (ct := ct) (C := D) (D := E) hfindD hmroD).2
                          (hnegClear E hEmemList)
                    | callable P R =>
                        exact False.elim <|
                          freshSeedsObj_not_denotes_callable
                            (ct := ct) (P := P) (R := R)
                            seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
                            (holdAtom (.callable P R) hmemA)
                    | union T U =>
                        exact False.elim <|
                          interAtoms_union_not_mem S T U huf hmemA
                    | intersection T U =>
                        exact False.elim <|
                          interAtoms_intersection_not_mem S T U huf hmemA
                  have hnegCur :
                      Ty.semDenotes ct (.negClass D)
                        (currentObjOf (ct := ct) D hfindD hmroD) :=
                    hsem _ hdenCur
                  have hclassSelf :
                      Ty.semDenotes ct (.class_ D)
                        (currentObjOf (ct := ct) D hfindD hmroD) :=
                    (currentObjOf_denotes_class
                      (ct := ct) (C := D) (D := D) hfindD hmroD).2
                      (by simpa [findClass_name hfindD] using mro_self_mem hmroD)
                  exact False.elim (hnegCur hclassSelf)
          | isFalse hnonleafD =>
              by_cases hDseed : D ∈ seeds
              · have hself : D ∈ (seedWitness D hDseed).mro := by
                  simpa [findClass_name (seedWitness D hDseed).hfind] using
                    mro_self_mem (seedWitness D hDseed).hmro
                have hnegOld :
                    Ty.semDenotes ct (.negClass D) oldW :=
                  hsem _ hden
                exact False.elim <|
                  (freshSeedsObj_denotes_neg_iff
                    (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup
                    seedWitness seed_nonleaf).1 hnegOld ⟨D, hDseed, hself⟩
              · let newSeeds : List Identifier := D :: seeds
                let newSeedWitness : ∀ s, s ∈ newSeeds → FreshSeedInfo ct s := fun s hs => by
                  by_cases hEq : s = D
                  · subst hEq
                    exact ⟨clsD, mroD, hfindD, hmroD⟩
                  · exact seedWitness s (by simpa [newSeeds, hEq] using hs)
                let newSeedNonleaf : ∀ s, s ∈ newSeeds → ¬ LeafBuiltin ct s := fun s hs => by
                  by_cases hEq : s = D
                  · subst hEq
                    exact hnonleafD
                  · exact seed_nonleaf s (by simpa [newSeeds, hEq] using hs)
                have hnew_ne : newSeeds ≠ [] := by simp [newSeeds]
                have hnew_nodup : newSeeds.Nodup := by
                  simp [newSeeds, hDseed, hseeds_nodup]
                have hdenNew :
                    Ty.semDenotes ct S
                      (freshSeedsObj (ct := ct)
                        newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf) := by
                  refine semDenotes_source_of_atoms (ct := ct) (S := S)
                    (obj := freshSeedsObj (ct := ct)
                      newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf) huf ?_
                  intro A hmemA
                  cases A with
                  | bottom =>
                      exact False.elim (holdAtom .bottom hmemA)
                  | class_ C =>
                      have holdC : Ty.semDenotes ct (.class_ C) oldW := holdAtom (.class_ C) hmemA
                      rcases (freshSeedsObj_denotes_class_iff
                        (ct := ct) (C := C) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1 holdC with
                        ⟨s, hs, hCmem⟩
                      have hsNew : s ∈ newSeeds := by
                        simp [newSeeds, hs]
                      exact (freshSeedsObj_denotes_class_iff
                        (ct := ct) (C := C) newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf).2
                        ⟨s, hsNew, by
                          by_cases hEq : s = D
                          · exact False.elim (hDseed (hEq ▸ hs))
                          · simpa [newSeedWitness, newSeeds, hEq] using hCmem⟩
                  | negClass E =>
                      have hnegOldE : Ty.semDenotes ct (.negClass E) oldW := holdAtom (.negClass E) hmemA
                      have hEmemList : E ∈ negAtoms :=
                        (summarizeInterAtoms_neg_mem_iff
                          (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).2 hmemA
                      exact (freshSeedsObj_denotes_neg_iff
                        (ct := ct) (C := E) newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf).2 <|
                        by
                          intro hanc
                          rcases hanc with ⟨s, hs, hEanc⟩
                          by_cases hEq : s = D
                          · subst hEq
                            have hEmro : E ∈ mroD := by
                              simpa [newSeedWitness, newSeeds] using hEanc
                            exact hnegClear E hEmemList hEmro
                          · have hsOld : s ∈ seeds := by
                              simpa [newSeeds, hEq] using hs
                            have hEancOld : E ∈ (seedWitness s hsOld).mro := by
                              simpa [newSeedWitness, newSeeds, hEq] using hEanc
                            exact (freshSeedsObj_denotes_neg_iff
                              (ct := ct) (C := E) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1
                              hnegOldE ⟨s, hsOld, hEancOld⟩
                  | callable P R =>
                      exact False.elim <|
                        freshSeedsObj_not_denotes_callable
                          (ct := ct) (P := P) (R := R)
                          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
                          (holdAtom (.callable P R) hmemA)
                  | union T U =>
                      exact False.elim <|
                        interAtoms_union_not_mem S T U huf hmemA
                  | intersection T U =>
                      exact False.elim <|
                        interAtoms_intersection_not_mem S T U huf hmemA
                let newW :=
                  freshSeedsObj (ct := ct)
                    newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf
                have hclassNew :
                    Ty.semDenotes ct (.class_ D) newW :=
                  (freshSeedsObj_denotes_class_iff
                    (ct := ct) (C := D) newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf).2
                    ⟨D, by simp [newSeeds], by
                      simpa [newSeedWitness, newSeeds, findClass_name hfindD] using mro_self_mem hmroD⟩
                have hnegNew :
                    Ty.semDenotes ct (.negClass D) newW :=
                  hsem _ hdenNew
                exact False.elim (hnegNew hclassNew)
  | boundMethodFromCallables Psum Rsum hden hsub =>
      have hnotmem : D ∉ hwfct.boundMethodExists.mro := by
        simpa [boundMethodObj, Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor] using
          hsem _ hden
      exact .trans hsub <| .trans
        (.callableBoundMethod hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro)
        (.sealedClassNegClass
          (leafBuiltin_boundMethod hwfct)
          hwfct.boundMethodExists.hfind
          hwfct.boundMethodExists.hmro
          hnotmem)

theorem semSubtype_inter_class_of_neg_left
    (hsem : SemSubtype ct S (.union (.negClass B) U)) :
    SemSubtype ct (.intersection S (.class_ B)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hneg | hU
  · exact False.elim (hneg hden.2)
  · exact hU

theorem semSubtype_inter_class_of_neg_right
    (hsem : SemSubtype ct S (.union U (.negClass B))) :
    SemSubtype ct (.intersection S (.class_ B)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hU | hneg
  · exact hU
  · exact False.elim (hneg hden.2)

theorem semSubtype_inter_neg_of_class_left
    (hsem : SemSubtype ct S (.union (.class_ D) U)) :
    SemSubtype ct (.intersection S (.negClass D)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hclass | hU
  · exact False.elim (hden.2 hclass)
  · exact hU

theorem semSubtype_inter_neg_of_class_right
    (hsem : SemSubtype ct S (.union U (.class_ D))) :
    SemSubtype ct (.intersection S (.negClass D)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hU | hclass
  · exact hU
  · exact False.elim (hden.2 hclass)


theorem leaf_subtype_of_current_denotes
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some clsB)
    (hmroB : ComputeMro ct clsB bmro) :
    (U : Ty) → WellFormedTy ct U →
      Ty.semDenotes ct U (currentObjOf (ct := ct) B hfindB hmroB) →
      IsSubtype ct (.class_ B) U
  | .class_ D, _hwfU, hden =>
      .class_ hfindB hmroB <|
        (currentObjOf_denotes_class
          (ct := ct) (C := B) (D := D) hfindB hmroB).1 hden
  | .negClass D, _hwfU, hden =>
      .sealedClassNegClass hleaf hfindB hmroB <|
        (currentObjOf_denotes_neg_iff
          (ct := ct) (C := B) (D := D) hfindB hmroB).1 hden
  | .callable P R, _hwfU, hden =>
      False.elim <|
        currentObjOf_not_denotes_callable
          (ct := ct) (C := B) (P := P) (R := R) hfindB hmroB hden
  | .union U V, hwfU, hden =>
      match hden with
      | Or.inl hU =>
          .unionLeft <|
            leaf_subtype_of_current_denotes
              (ct := ct) (B := B) hleaf hfindB hmroB U hwfU.union_left hU
      | Or.inr hV =>
          .unionRight <|
            leaf_subtype_of_current_denotes
              (ct := ct) (B := B) hleaf hfindB hmroB V hwfU.union_right hV
  | .intersection U V, hwfU, hden =>
      .interIntro
        (leaf_subtype_of_current_denotes
          (ct := ct) (B := B) hleaf hfindB hmroB U hwfU.intersection_left hden.1)
        (leaf_subtype_of_current_denotes
          (ct := ct) (B := B) hleaf hfindB hmroB V hwfU.intersection_right hden.2)
  | .bottom, _hwfU, hden =>
      False.elim hden
termination_by U => U.size
decreasing_by
  all_goals
    simp [Ty.size]
    omega

theorem callable_subtype_of_boundMethod_denotes
    (hwfct : WellFormedClassTable ct) :
    (U : Ty) → WellFormedTy ct U →
      Ty.semDenotes ct U (boundMethodObj (ct := ct) hwfct P R) →
      IsSubtype ct (.callable P R) U
  | .class_ D, _hwfU, hden =>
      .trans
        (callable_to_class (ct := ct) (P := P) (R := R) hwfct)
        (.class_
          hwfct.boundMethodExists.hfind
          hwfct.boundMethodExists.hmro
          ((boundMethodObj_denotes_class_iff
            (ct := ct) (C := D) (P := P) (R := R) hwfct).1 hden))
  | .negClass D, _hwfU, hden =>
      .trans
        (.callableBoundMethod
          hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro)
        (.sealedClassNegClass
          (leafBuiltin_boundMethod hwfct)
          hwfct.boundMethodExists.hfind
          hwfct.boundMethodExists.hmro
          ((boundMethodObj_denotes_neg_iff
            (ct := ct) (C := D) (P := P) (R := R) hwfct).1 hden))
  | .callable P' R', _hwfU, hden =>
      .callable hden.1 hden.2
  | .union U V, hwfU, hden =>
      match hden with
      | Or.inl hU =>
          .unionLeft <|
            callable_subtype_of_boundMethod_denotes
              (ct := ct) (P := P) (R := R) hwfct U hwfU.union_left hU
      | Or.inr hV =>
          .unionRight <|
            callable_subtype_of_boundMethod_denotes
              (ct := ct) (P := P) (R := R) hwfct V hwfU.union_right hV
  | .intersection U V, hwfU, hden =>
      .interIntro
        (callable_subtype_of_boundMethod_denotes
          (ct := ct) (P := P) (R := R) hwfct U hwfU.intersection_left hden.1)
        (callable_subtype_of_boundMethod_denotes
          (ct := ct) (P := P) (R := R) hwfct V hwfU.intersection_right hden.2)
  | .bottom, _hwfU, hden =>
      False.elim hden
termination_by U => U.size
decreasing_by
  all_goals
    simp [Ty.size]
    omega

theorem complete_callable_any
    (hwfct : WellFormedClassTable ct)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct (.callable P R) U) :
    IsSubtype ct (.callable P R) U := by
  exact callable_subtype_of_boundMethod_denotes
    (ct := ct) (P := P) (R := R) hwfct U hwfU <|
      hsem _ (boundMethodObj_denotes_callable_self (ct := ct) (P := P) (R := R) hwfct)

theorem complete_leaf_class_any
    (_hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct (.class_ C))
    (hleaf : LeafBuiltin ct C)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct (.class_ C) U) :
    IsSubtype ct (.class_ C) U := by
  rcases hwfS.class_find with ⟨clsC, mroC, hfindC, hmroC⟩
  have hself : C ∈ mroC := by
    simpa [findClass_name hfindC] using mro_self_mem hmroC
  exact leaf_subtype_of_current_denotes
    (ct := ct) (B := C) hleaf hfindC hmroC U hwfU <|
      hsem _
        ((currentObjOf_denotes_class
          (ct := ct) (C := C) (D := C) hfindC hmroC).2 hself)

theorem semDenotes_callable_class_iff
    (hwfct : WellFormedClassTable ct)
    (hcall : Ty.semDenotes ct (.callable P R) obj) :
    Ty.semDenotes ct (.class_ D) obj ↔ D ∈ hwfct.boundMethodExists.mro := by
  cases obj with
  | ordinaryCurrent | ordinaryFresh =>
      cases hcall
  | boundMethod bm =>
      have hfindEq : some bm.cls = some hwfct.boundMethodExists.cls := by
        rw [← bm.hfind, hwfct.boundMethodExists.hfind]
      injection hfindEq with hcls
      have hmroBM : ComputeMro ct bm.cls hwfct.boundMethodExists.mro := by
        simpa [hcls] using hwfct.boundMethodExists.hmro
      have hmroEq : bm.mro = hwfct.boundMethodExists.mro :=
        determinism bm.hmro hmroBM
      constructor <;> intro h
      · simpa [Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor,
          hmroEq] using h
      · simpa [Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor,
          hmroEq] using h

theorem semDenotes_callable_neg_iff
    (hwfct : WellFormedClassTable ct)
    (hcall : Ty.semDenotes ct (.callable P R) obj) :
    Ty.semDenotes ct (.negClass D) obj ↔ D ∉ hwfct.boundMethodExists.mro := by
  constructor
  · intro hneg hmem
    exact hneg ((semDenotes_callable_class_iff
      (ct := ct) (P := P) (R := R) (D := D) hwfct hcall).2 hmem)
  · intro hnot
    exact fun hclass =>
      hnot ((semDenotes_callable_class_iff
        (ct := ct) (P := P) (R := R) (D := D) hwfct hcall).1 hclass)

theorem semSubtype_inter_neg_of_callable_left
    (hwfct : WellFormedClassTable ct)
    (hsem : SemSubtype ct S (.union (.callable P R) U)) :
    SemSubtype ct (.intersection S (.negClass boundMethodClass)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hcall | hU
  · have hself : boundMethodClass ∈ hwfct.boundMethodExists.mro := by
      simpa [findClass_name hwfct.boundMethodExists.hfind] using
        mro_self_mem hwfct.boundMethodExists.hmro
    have hclassBM : Ty.semDenotes ct (.class_ boundMethodClass) obj :=
      (semDenotes_callable_class_iff
        (ct := ct) (P := P) (R := R) (D := boundMethodClass) hwfct hcall).2 hself
    exact False.elim (hden.2 hclassBM)
  · exact hU

theorem semSubtype_inter_neg_of_callable_right
    (hwfct : WellFormedClassTable ct)
    (hsem : SemSubtype ct S (.union U (.callable P R))) :
    SemSubtype ct (.intersection S (.negClass boundMethodClass)) U := by
  intro obj hden
  rcases hsem obj hden.1 with hU | hcall
  · exact hU
  · have hself : boundMethodClass ∈ hwfct.boundMethodExists.mro := by
      simpa [findClass_name hwfct.boundMethodExists.hfind] using
        mro_self_mem hwfct.boundMethodExists.hmro
    have hclassBM : Ty.semDenotes ct (.class_ boundMethodClass) obj :=
      (semDenotes_callable_class_iff
        (ct := ct) (P := P) (R := R) (D := boundMethodClass) hwfct hcall).2 hself
    exact False.elim (hden.2 hclassBM)

theorem class_obj_not_denotes_callable_of_not_mem
    (hwfct : WellFormedClassTable ct)
    (hnotmem : C ∉ hwfct.boundMethodExists.mro) :
    ∀ {obj}, Ty.semDenotes ct (.class_ C) obj → ¬ Ty.semDenotes ct (.callable P R) obj := by
  intro obj hclass hcall
  exact hnotmem <|
    (semDenotes_callable_class_iff
      (ct := ct) (P := P) (R := R) (D := C) hwfct hcall).1 hclass

theorem class_obj_not_denotes_neg_of_mem
    (hfindC : findClass ct C = some clsC)
    (hmroC : ComputeMro ct clsC mroC)
    (hmem : D ∈ mroC) :
    ∀ {obj}, Ty.semDenotes ct (.class_ C) obj → ¬ Ty.semDenotes ct (.negClass D) obj := by
  intro obj hclass hneg
  exact hneg <|
    SemObject.hasAncestor_closed
      (obj := obj) hclass hfindC hmroC hmem

theorem callable_obj_not_denotes_class_of_not_mem
    (hwfct : WellFormedClassTable ct)
    (hnotmem : D ∉ hwfct.boundMethodExists.mro) :
    ∀ {obj}, Ty.semDenotes ct (.callable P R) obj → ¬ Ty.semDenotes ct (.class_ D) obj := by
  intro obj hcall hclass
  exact hnotmem <|
    (semDenotes_callable_class_iff
      (ct := ct) (P := P) (R := R) (D := D) hwfct hcall).1 hclass

theorem callable_obj_not_denotes_neg_of_mem
    (hwfct : WellFormedClassTable ct)
    (hmem : D ∈ hwfct.boundMethodExists.mro) :
    ∀ {obj}, Ty.semDenotes ct (.callable P R) obj → ¬ Ty.semDenotes ct (.negClass D) obj := by
  intro obj hcall hneg
  exact hneg <|
    (semDenotes_callable_class_iff
      (ct := ct) (P := P) (R := R) (D := D) hwfct hcall).2 hmem

theorem neg_obj_not_denotes_class_of_mem
    (hfindD : findClass ct D = some clsD)
    (hmroD : ComputeMro ct clsD mroD)
    (hmem : C ∈ mroD) :
    ∀ {obj}, Ty.semDenotes ct (.negClass C) obj → ¬ Ty.semDenotes ct (.class_ D) obj := by
  intro obj hneg hclass
  exact hneg <|
    SemObject.hasAncestor_closed
      (obj := obj) hclass hfindD hmroD hmem

theorem neg_obj_not_denotes_callable_of_mem
    (hwfct : WellFormedClassTable ct)
    (hmem : C ∈ hwfct.boundMethodExists.mro) :
    ∀ {obj}, Ty.semDenotes ct (.negClass C) obj → ¬ Ty.semDenotes ct (.callable P R) obj := by
  intro obj hneg hcall
  exact hneg <|
    (semDenotes_callable_class_iff
      (ct := ct) (P := P) (R := R) (D := C) hwfct hcall).2 hmem

theorem complete_via_leaf_class_retract
    (hwfct : WellFormedClassTable ct)
    (hwfClass : WellFormedTy ct (.class_ C))
    (hleaf : LeafBuiltin ct C)
    (hsub : IsSubtype ct S (.class_ C))
    (hrev : IsSubtype ct (.class_ C) S)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct S U) :
    IsSubtype ct S U := by
  have hsem' : SemSubtype ct (.class_ C) U :=
    SemSubtype.trans (semSubtype_sound hrev) hsem
  exact .trans hsub
    (complete_leaf_class_any (ct := ct) (C := C) hwfct hwfClass hleaf hwfU hsem')

theorem complete_via_callable_head
    (hwfct : WellFormedClassTable ct)
    (hden : Ty.semDenotes ct S (boundMethodObj (ct := ct) hwfct P R))
    (hsub : IsSubtype ct S (.callable P R))
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct S U) :
    IsSubtype ct S U := by
  exact .trans hsub
    (callable_subtype_of_boundMethod_denotes
      (ct := ct) (P := P) (R := R) hwfct U hwfU (hsem _ hden))

theorem complete_clean_empty_any
    (hsub : IsSubtype ct S .bottom) :
    IsSubtype ct S U := by
  exact .trans hsub .bottom

theorem complete_clean_currentFromLeaf_any
    (hwfct : WellFormedClassTable ct)
    (hleaf : LeafBuiltin ct cname)
    (hfind : findClass ct cname = some cls)
    (hmro : ComputeMro ct cls mro)
    (hsub : IsSubtype ct S (.class_ cname))
    (hrev : IsSubtype ct (.class_ cname) S)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct S U) :
    IsSubtype ct S U := by
  exact complete_via_leaf_class_retract
    (ct := ct) (S := S) (C := cname)
    hwfct (.class_ hfind hmro) hleaf hsub hrev hwfU hsem

theorem complete_clean_boundMethod_any
    (hwfct : WellFormedClassTable ct)
    (hden : Ty.semDenotes ct S (boundMethodObj (ct := ct) hwfct P R))
    (hsub : IsSubtype ct S (.callable P R))
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct S U) :
    IsSubtype ct S U := by
  exact complete_via_callable_head
    (ct := ct) (S := S) (P := P) (R := R) hwfct hden hsub hwfU hsem

theorem complete_callable_union
    (hwfct : WellFormedClassTable ct)
    (_hwfS : WellFormedTy ct (.callable P R))
    (hwfU : WellFormedTy ct (.union T U))
    (hsem : SemSubtype ct (.callable P R) (.union T U)) :
    IsSubtype ct (.callable P R) (.union T U) := by
  exact complete_callable_any (ct := ct) (P := P) (R := R) hwfct hwfU hsem

theorem complete_clean_case_or_fresh
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (hcase : CleanSourceCase (ct := ct) (S := S) hwfct hwfS)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct S U) :
    IsSubtype ct S U ∨
      ∃ seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden,
        hcase =
          CleanSourceCase.freshFromSeeds
            (ct := ct) (S := S) (hwfct := hwfct) (hwfS := hwfS)
            seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden := by
  cases hcase with
  | empty hsub =>
      exact Or.inl (complete_clean_empty_any (ct := ct) (S := S) hsub)
  | currentFromLeaf cname cls mro hleaf hfind hmro hden hsub hrev =>
      exact Or.inl <|
        complete_clean_currentFromLeaf_any
          (ct := ct) (S := S) (U := U) (cname := cname)
          hwfct hleaf hfind hmro hsub hrev hwfU hsem
  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seed_source hden =>
      exact Or.inr ⟨seeds, hseeds_ne, hseeds_nodup, seedWitness, seed_nonleaf, seed_source, hden, rfl⟩
  | boundMethodFromCallables Psum Rsum hden hsub =>
      exact Or.inl <|
        complete_clean_boundMethod_any
          (ct := ct) (S := S) (U := U) (P := Psum) (R := Rsum)
          hwfct hden hsub hwfU hsem

theorem fresh_not_denotes_unionAtomsFold_of_noUseful
    (hnoUseful : ∀ A, A ∈ atoms → usefulUnionArm A = false)
    (hnoUnion : ∀ T U, Ty.union T U ∉ atoms) :
    ¬ Ty.semDenotes ct
      (Ty.unionAtomsFold atoms)
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
  induction atoms with
  | nil =>
      simp [Ty.unionAtomsFold, Ty.semDenotes]
  | cons A As ih =>
      cases As with
      | nil =>
          have huseA : usefulUnionArm A = false := hnoUseful A (by simp)
          cases A with
          | bottom =>
              simp [usefulUnionArm] at huseA
          | class_ C =>
              simp [usefulUnionArm] at huseA
          | negClass C =>
              simp [usefulUnionArm] at huseA
          | callable P R =>
              intro hden
              exact freshSeedsObj_not_denotes_callable
                (ct := ct) (P := P) (R := R)
                seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf hden
          | union T U =>
              exact False.elim (hnoUnion T U (by simp))
          | intersection T U =>
              simp [usefulUnionArm] at huseA
      | cons B Bs =>
          intro hden
          rcases hden with hA | hAs
          · cases A with
            | bottom =>
                have : usefulUnionArm Ty.bottom = false := hnoUseful .bottom (by simp)
                simp [usefulUnionArm] at this
            | class_ C =>
                have : usefulUnionArm (.class_ C) = false := hnoUseful (.class_ C) (by simp)
                simp [usefulUnionArm] at this
            | negClass C =>
                have : usefulUnionArm (.negClass C) = false := hnoUseful (.negClass C) (by simp)
                simp [usefulUnionArm] at this
            | callable P R =>
                exact freshSeedsObj_not_denotes_callable
                  (ct := ct) (P := P) (R := R)
                  seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf hA
            | union T U =>
                exact False.elim (hnoUnion T U (by simp))
            | intersection T U =>
                have : usefulUnionArm (.intersection T U) = false :=
                  hnoUseful (.intersection T U) (by simp)
                simp [usefulUnionArm] at this
          · apply ih
            · intro X hX
              exact hnoUseful X (by simp [hX])
            · intro T U hmem
              exact hnoUnion T U (by simp [hmem])
            · exact hAs

structure CompleteArgs (ct : ClassTable) where
  T : Ty
  U : Ty
  hwfT : WellFormedTy ct T
  hwfU : WellFormedTy ct U
  hsem : SemSubtype ct T U


import FwPython.Static.Subtyping.Completeness.Infra.Witnesses

/-! ### Normalization and semantic bridge lemmas -/

theorem subtype_inter_union_normalize_left_to :
    IsSubtype ct
      (.intersection (.union S T) U)
      (.union (.intersection S U) (.intersection T U)) := by
  exact .trans subtype_inter_comm <|
    .trans subtype_inter_union_distrib <|
      .unionElim
        (.unionLeft subtype_inter_comm)
        (.unionRight subtype_inter_comm)

theorem subtype_inter_union_normalize_left_from :
    IsSubtype ct
      (.union (.intersection S U) (.intersection T U))
      (.intersection (.union S T) U) := by
  exact .trans
    (.unionElim
      (.unionLeft subtype_inter_comm)
      (.unionRight subtype_inter_comm))
    (.trans subtype_union_inter_distrib subtype_inter_comm)

theorem subtype_inter_union_normalize_right_to :
    IsSubtype ct
      (.intersection S (.union T U))
      (.union (.intersection S T) (.intersection S U)) :=
  subtype_inter_union_distrib

theorem subtype_inter_union_normalize_right_from :
    IsSubtype ct
      (.union (.intersection S T) (.intersection S U))
      (.intersection S (.union T U)) :=
  subtype_union_inter_distrib

theorem subtype_inter_union_normalize_left :
    IsSubtype ct (.intersection (.union S T) U) V ↔
      IsSubtype ct (.union (.intersection S U) (.intersection T U)) V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact .trans subtype_inter_union_normalize_left_from h
  · exact .trans subtype_inter_union_normalize_left_to h

theorem subtype_inter_union_normalize_right :
    IsSubtype ct (.intersection S (.union T U)) V ↔
      IsSubtype ct (.union (.intersection S T) (.intersection S U)) V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact .trans subtype_inter_union_normalize_right_from h
  · exact .trans subtype_inter_union_normalize_right_to h

theorem semSubtype_inter_union_normalize_left :
    SemSubtype ct (.intersection (.union S T) U) V ↔
      SemSubtype ct (.union (.intersection S U) (.intersection T U)) V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact SemSubtype.trans
      (semSubtype_sound subtype_inter_union_normalize_left_from) h
  · exact SemSubtype.trans
      (semSubtype_sound subtype_inter_union_normalize_left_to) h

theorem semSubtype_inter_union_normalize_right :
    SemSubtype ct (.intersection S (.union T U)) V ↔
      SemSubtype ct (.union (.intersection S T) (.intersection S U)) V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact SemSubtype.trans
      (semSubtype_sound subtype_inter_union_normalize_right_from) h
  · exact SemSubtype.trans
      (semSubtype_sound subtype_inter_union_normalize_right_to) h

theorem semSubtype_union_left_of_impossible_right
    (hsem : SemSubtype ct S (.union T U))
    (himp : ∀ obj, Ty.semDenotes ct S obj → ¬ Ty.semDenotes ct U obj) :
    SemSubtype ct S T := by
  intro obj hS
  rcases hsem obj hS with hT | hU
  · exact hT
  · exact False.elim (himp obj hS hU)

theorem semSubtype_union_right_of_impossible_left
    (hsem : SemSubtype ct S (.union T U))
    (himp : ∀ obj, Ty.semDenotes ct S obj → ¬ Ty.semDenotes ct T obj) :
    SemSubtype ct S U := by
  intro obj hS
  rcases hsem obj hS with hT | hU
  · exact False.elim (himp obj hS hT)
  · exact hU

theorem semSubtype_union_right_of_left_subtype
    (hsem : SemSubtype ct S (.union T U))
    (hsub : IsSubtype ct T U) :
    SemSubtype ct S U := by
  intro obj hS
  rcases hsem obj hS with hT | hU
  · exact semDenotes_at_obj_sound (ct := ct) (obj := obj) hsub hT
  · exact hU

theorem semSubtype_union_left_of_right_subtype
    (hsem : SemSubtype ct S (.union T U))
    (hsub : IsSubtype ct U T) :
    SemSubtype ct S T := by
  intro obj hS
  rcases hsem obj hS with hT | hU
  · exact hT
  · exact semDenotes_at_obj_sound (ct := ct) (obj := obj) hsub hU

theorem callable_to_class (hwfct : WellFormedClassTable ct) :
    IsSubtype ct (.callable P R) (.class_ boundMethodClass) :=
  .callableBoundMethod hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro

theorem callable_summary_intro (hwfct : WellFormedClassTable ct)
    (hden : Ty.semDenotes ct (.callable P R) (boundMethodObj (ct := ct) hwfct Psum Rsum)) :
    IsSubtype ct (.callable Psum Rsum) (.callable P R) :=
  .callable hden.1 hden.2

theorem negClass_union_of_inter_class_subtype
    (hsub : IsSubtype ct (.intersection S (.class_ B)) U) :
    IsSubtype ct S (.union (.negClass B) U) := by
  exact .trans subtype_inter_object' <|
    .trans
      (.interIntro
        (.interLeft .refl)
        (.trans (.interRight .refl) .objectClassUnionNegClass))
      <| .trans subtype_inter_union_distrib <|
          .unionElim
            (.unionRight hsub)
            (.unionLeft (.interRight .refl))

theorem negClass_of_inter_class_bottom
    (hsub : IsSubtype ct (.intersection S (.class_ B)) .bottom) :
    IsSubtype ct S (.negClass B) := by
  exact .trans (negClass_union_of_inter_class_subtype (ct := ct) (S := S) (B := B) hsub)
    subtype_union_bottom

theorem class_union_of_inter_neg_subtype
    (hsub : IsSubtype ct (.intersection S (.negClass D)) U) :
    IsSubtype ct S (.union (.class_ D) U) := by
  exact .trans subtype_inter_object' <|
    .trans
      (.interIntro
        (.interLeft .refl)
        (.trans (.interRight .refl) .objectClassUnionNegClass))
      <| .trans subtype_inter_union_distrib <|
          .unionElim
            (.unionLeft (.interRight .refl))
            (.unionRight hsub)

theorem class_of_inter_neg_bottom
    (hsub : IsSubtype ct (.intersection S (.negClass D)) .bottom) :
    IsSubtype ct S (.class_ D) := by
  exact .trans
    (class_union_of_inter_neg_subtype (ct := ct) (S := S) (D := D) hsub)
    subtype_union_bottom

theorem union_of_inter_class_neg_subtype
    (hclass : IsSubtype ct (.intersection S (.class_ B)) T)
    (hneg : IsSubtype ct (.intersection S (.negClass B)) U) :
    IsSubtype ct S (.union T U) := by
  exact .trans subtype_inter_object' <|
    .trans
      (.interIntro
        (.interLeft .refl)
        (.trans (.interRight .refl) .objectClassUnionNegClass))
      <| .trans subtype_inter_union_distrib <|
          .unionElim
            (.unionLeft hclass)
            (.unionRight hneg)

theorem leaf_inter_class_outside_bottom
    (hleaf : LeafBuiltin ct B)
    (hfindB : findClass ct B = some bcls)
    (hmroB : ComputeMro ct bcls bmro)
    (hnotmem : C ∉ bmro) :
    IsSubtype ct (.intersection (.class_ C) (.class_ B)) .bottom := by
  exact .trans
    (.interIntro
      (.interRight .refl)
      (.interLeft (leafBuiltinNegClass hleaf hfindB hmroB hnotmem)))
    .classSelfNegClassBottom

theorem negClass_bottom_of_objectSubtype (hwfct : WellFormedClassTable ct)
    (hsub : IsSubtype ct (.class_ objectClass) (.class_ C)) :
    IsSubtype ct (.negClass C) .bottom := by
  have hmem : C ∈ [objectClass] := by
    simpa [mro_of_object (ct := ct) hwfct] using
      class_subtype_mem_mro
        (ct := ct)
        (c := objectClass)
        (a := C)
        (cls := hwfct.objectExists.cls)
        (mro := [objectClass])
        hsub
        hwfct.objectExists.hfind
        (mro_of_object (ct := ct) hwfct)
  have hC : C = objectClass := by simpa using hmem
  subst hC
  exact .trans (.interIntro .objectTop .refl) .classSelfNegClassBottom

theorem leafBuiltin_find_mro
    (hwfct : WellFormedClassTable ct)
    (hleaf : LeafBuiltin ct B) :
    ∃ bcls bmro, findClass ct B = some bcls ∧ ComputeMro ct bcls bmro := by
  rcases (leafBuiltin_iff_builtinName (ct := ct) (C := B) hwfct).1 hleaf with rfl | rfl | rfl
  · exact ⟨hwfct.boolExists.cls, hwfct.boolExists.mro, hwfct.boolExists.hfind, hwfct.boolExists.hmro⟩
  · exact ⟨hwfct.noneExists.cls, hwfct.noneExists.mro, hwfct.noneExists.hfind, hwfct.noneExists.hmro⟩
  · exact ⟨hwfct.boundMethodExists.cls, hwfct.boundMethodExists.mro,
      hwfct.boundMethodExists.hfind, hwfct.boundMethodExists.hmro⟩

theorem leaf_conflict_bottom
    (hwfct : WellFormedClassTable ct)
    (hB : LeafBuiltin ct B)
    (hC : LeafBuiltin ct C)
    (hBC : B ≠ C) :
    IsSubtype ct (.intersection (.class_ B) (.class_ C)) .bottom := by
  obtain ⟨bcls, bmro, hfindB, hmroB⟩ := leafBuiltin_find_mro (ct := ct) (B := B) hwfct hB
  have hC_not_mem_B : C ∉ bmro := by
    intro hmem
    exact hBC (LeafBuiltin.sealed hC B bcls bmro hfindB hmroB hmem)
  exact .trans
    (.interIntro
      (.interLeft .refl)
      (.interRight (leafBuiltinNegClass hB hfindB hmroB hC_not_mem_B)))
    .classSelfNegClassBottom


theorem complete_class_class
    (_hwfct : WellFormedClassTable ct)
    (hwfC : WellFormedTy ct (.class_ C))
    (_hwfD : WellFormedTy ct (.class_ D))
    (hsem : SemSubtype ct (.class_ C) (.class_ D)) :
    IsSubtype ct (.class_ C) (.class_ D) := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfC.class_find
  have hsrc :
      Ty.semDenotes ct (.class_ C) (currentObjOf (ct := ct) C hfindC hmroC) :=
    (currentObjOf_denotes_class (ct := ct) (C := C) (D := C) hfindC hmroC).2
      (by simpa [findClass_name hfindC] using mro_self_mem hmroC)
  have hmem : D ∈ mroC :=
    (currentObjOf_denotes_class (ct := ct) (C := C) (D := D) hfindC hmroC).1 (hsem _ hsrc)
  exact .class_ hfindC hmroC hmem

theorem complete_class_neg
    (hwfct : WellFormedClassTable ct)
    (hwfC : WellFormedTy ct (.class_ C))
    (hwfD : WellFormedTy ct (.negClass D))
    (hsem : SemSubtype ct (.class_ C) (.negClass D)) :
    IsSubtype ct (.class_ C) (.negClass D) := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfC.class_find
  obtain ⟨clsD, mroD, hfindD, hmroD⟩ := hwfD.negClass_find
  have hcurC :
      Ty.semDenotes ct (.class_ C) (currentObjOf (ct := ct) C hfindC hmroC) :=
    (currentObjOf_denotes_class (ct := ct) (C := C) (D := C) hfindC hmroC).2
      (by simpa [findClass_name hfindC] using mro_self_mem hmroC)
  have hnotmemC : D ∉ mroC :=
    (currentObjOf_denotes_neg_iff (ct := ct) (C := C) (D := D) hfindC hmroC).1 (hsem _ hcurC)
  let _ : Decidable (LeafBuiltin ct C) := builtinLeafDecidable (ct := ct) (C := C) hwfct
  by_cases hleafC : LeafBuiltin ct C
  · exact .sealedClassNegClass hleafC hfindC hmroC hnotmemC
  · by_cases hCD : C = D
    · have hCmem : C ∈ mroC := by
        simpa [findClass_name hfindC] using mro_self_mem hmroC
      exact False.elim (hnotmemC (hCD ▸ hCmem))
    · let _ : Decidable (LeafBuiltin ct D) := builtinLeafDecidable (ct := ct) (C := D) hwfct
      by_cases hleafD : LeafBuiltin ct D
      · by_cases hCmemD : C ∈ mroD
        · have hcontra : False := by
            have hcurD :
                Ty.semDenotes ct (.class_ C) (currentObjOf (ct := ct) D hfindD hmroD) :=
              (currentObjOf_denotes_class (ct := ct) (C := D) (D := C) hfindD hmroD).2 hCmemD
            have hnegD :
                Ty.semDenotes ct (.negClass D) (currentObjOf (ct := ct) D hfindD hmroD) :=
              hsem _ hcurD
            have : D ∉ mroD :=
              (currentObjOf_denotes_neg_iff (ct := ct) (C := D) (D := D) hfindD hmroD).1 hnegD
            exact this <| by simpa [findClass_name hfindD] using mro_self_mem hmroD
          exact False.elim hcontra
        · exact leafBuiltinNegClass hleafD hfindD hmroD hCmemD
      · let pairWitness : ∀ s, s ∈ [C, D] → FreshSeedInfo ct s := fun s hs => by
            by_cases hsC : s = C
            · subst hsC
              exact ⟨clsC, mroC, hfindC, hmroC⟩
            · have hsD : s = D := by
                simp at hs
                rcases hs with h | h
                · exact False.elim (hsC h)
                · exact h
              subst hsD
              exact ⟨clsD, mroD, hfindD, hmroD⟩
        let pairNonleaf : ∀ s, s ∈ [C, D] → ¬ LeafBuiltin ct s := fun s hs => by
          simp at hs
          rcases hs with rfl | rfl
          · exact hleafC
          · exact hleafD
        have hCInPair : C ∈ [C, D] := by simp
        have hsrc :
            Ty.semDenotes ct (.class_ C)
              (freshSeedsObj (ct := ct)
                [C, D]
                (by simp)
                (by simp [hCD])
                pairWitness
                pairNonleaf) := by
          exact (freshSeedsObj_denotes_class_iff
            (ct := ct)
            (C := C)
            [C, D]
            (by simp)
            (by simp [hCD])
            pairWitness
            pairNonleaf).2 ⟨C, hCInPair, by
              dsimp [pairWitness]
              simp
              simpa [findClass_name hfindC] using mro_self_mem hmroC⟩
        have hneg :
            Ty.semDenotes ct (.negClass D)
              (freshSeedsObj (ct := ct)
                [C, D]
                (by simp)
                (by simp [hCD])
                pairWitness
                pairNonleaf) :=
          hsem _ hsrc
        have hDInPair : D ∈ [C, D] := by simp
        have hDmem : D ∈ (pairWitness D hDInPair).mro := by
          dsimp [pairWitness]
          have hDC : ¬ D = C := by
            intro h
            exact hCD h.symm
          simp [hDC]
          simpa [findClass_name hfindD] using mro_self_mem hmroD
        exact False.elim <| (freshSeedsObj_denotes_neg_iff
          (ct := ct)
          (C := D)
          [C, D]
          (by simp)
          (by simp [hCD])
          pairWitness
          pairNonleaf).1 hneg ⟨D, hDInPair, hDmem⟩

theorem complete_callable_class
    (hwfct : WellFormedClassTable ct)
    (_hwfS : WellFormedTy ct (.callable P R))
    (_hwfT : WellFormedTy ct (.class_ D))
    (hsem : SemSubtype ct (.callable P R) (.class_ D)) :
    IsSubtype ct (.callable P R) (.class_ D) := by
  have hmem : D ∈ hwfct.boundMethodExists.mro :=
    (boundMethodObj_denotes_class_iff (ct := ct) (C := D) (P := P) (R := R) hwfct).1
      (hsem _ (boundMethodObj_denotes_callable_self (ct := ct) (P := P) (R := R) hwfct))
  exact .trans
    (callable_to_class (ct := ct) (P := P) (R := R) hwfct)
    (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hmem)

theorem complete_callable_neg
    (hwfct : WellFormedClassTable ct)
    (_hwfS : WellFormedTy ct (.callable P R))
    (_hwfT : WellFormedTy ct (.negClass D))
    (hsem : SemSubtype ct (.callable P R) (.negClass D)) :
    IsSubtype ct (.callable P R) (.negClass D) := by
  have hnotmem : D ∉ hwfct.boundMethodExists.mro := by
    simpa [boundMethodObj, Ty.semDenotes, SemObject.hasAncestor, BoundMethodOrd.hasAncestor] using
      hsem _ (boundMethodObj_denotes_callable_self (ct := ct) (P := P) (R := R) hwfct)
  exact .trans
    (.callableBoundMethod hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro)
    (.sealedClassNegClass
      (leafBuiltin_boundMethod hwfct)
      hwfct.boundMethodExists.hfind
      hwfct.boundMethodExists.hmro
      hnotmem)

theorem complete_callable_callable
    (hwfct : WellFormedClassTable ct)
    (_hwfS : WellFormedTy ct (.callable P R))
    (_hwfT : WellFormedTy ct (.callable P' R'))
    (hsem : SemSubtype ct (.callable P R) (.callable P' R')) :
    IsSubtype ct (.callable P R) (.callable P' R') := by
  have hcall :
      Ty.semDenotes ct (.callable P' R') (boundMethodObj (ct := ct) hwfct P R) :=
    hsem _ (boundMethodObj_denotes_callable_self (ct := ct) (P := P) (R := R) hwfct)
  exact .callable hcall.1 hcall.2

theorem complete_neg_neg
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct (.negClass C))
    (hwfT : WellFormedTy ct (.negClass D))
    (hsem : SemSubtype ct (.negClass C) (.negClass D)) :
    IsSubtype ct (.negClass C) (.negClass D) := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfS.negClass_find
  obtain ⟨clsD, mroD, hfindD, hmroD⟩ := hwfT.negClass_find
  have hclass : SemSubtype ct (.class_ D) (.class_ C) := by
    intro obj hD
    by_cases hC : obj.hasAncestor C
    · exact hC
    · exact False.elim ((hsem obj hC) hD)
  have hsubDC : IsSubtype ct (.class_ D) (.class_ C) :=
    complete_class_class
      (ct := ct)
      (C := D)
      (D := C)
      hwfct
      (.class_ hfindD hmroD)
      (.class_ hfindC hmroC)
      hclass
  exact negClassAntitone hsubDC

theorem complete_neg_bottom
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct (.negClass C))
    (hsem : SemSubtype ct (.negClass C) .bottom) :
    IsSubtype ct (.negClass C) .bottom := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfS.negClass_find
  have hclass : SemSubtype ct (.class_ objectClass) (.class_ C) := by
    intro obj hobj
    by_cases hC : obj.hasAncestor C
    · exact hC
    · exact False.elim (hsem obj hC)
  have hsubObj : IsSubtype ct (.class_ objectClass) (.class_ C) :=
    complete_class_class
      (ct := ct)
      (C := objectClass)
      (D := C)
      hwfct
      (wellFormed_object_type (ct := ct) hwfct)
      (.class_ hfindC hmroC)
      hclass
  exact negClass_bottom_of_objectSubtype (ct := ct) (C := C) hwfct hsubObj

theorem not_semSubtype_class_callable
    (hwfS : WellFormedTy ct (.class_ C)) :
    ¬ SemSubtype ct (.class_ C) (.callable P R) := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfS.class_find
  intro hsem
  have hsrc :
      Ty.semDenotes ct (.class_ C) (currentObjOf (ct := ct) C hfindC hmroC) :=
    (currentObjOf_denotes_class (ct := ct) (C := C) (D := C) hfindC hmroC).2
      (by simpa [findClass_name hfindC] using mro_self_mem hmroC)
  exact currentObjOf_not_denotes_callable (ct := ct) (C := C) hfindC hmroC (hsem _ hsrc)

theorem not_semSubtype_class_bottom
    (hwfS : WellFormedTy ct (.class_ C)) :
    ¬ SemSubtype ct (.class_ C) .bottom := by
  obtain ⟨clsC, mroC, hfindC, hmroC⟩ := hwfS.class_find
  intro hsem
  have hsrc :
      Ty.semDenotes ct (.class_ C) (currentObjOf (ct := ct) C hfindC hmroC) :=
    (currentObjOf_denotes_class (ct := ct) (C := C) (D := C) hfindC hmroC).2
      (by simpa [findClass_name hfindC] using mro_self_mem hmroC)
  exact hsem _ hsrc

theorem not_semSubtype_callable_bottom
    (hwfct : WellFormedClassTable ct) :
    ¬ SemSubtype ct (.callable P R) .bottom := by
  intro hsem
  exact hsem _ (boundMethodObj_denotes_callable_self (ct := ct) (P := P) (R := R) hwfct)

theorem not_semSubtype_neg_class_nonobject
    (hwfct : WellFormedClassTable ct)
    (hC : C ≠ objectClass)
    (hD : D ≠ objectClass) :
    ¬ SemSubtype ct (.negClass C) (.class_ D) := by
  intro hsem
  have hsrc :=
    object_current_denotes_neg_nonobject (ct := ct) (C := C) hwfct hC
  exact object_current_not_denotes_class_nonobject (ct := ct) (C := D) hwfct hD (hsem _ hsrc)

theorem not_semSubtype_neg_callable_nonobject
    (hwfct : WellFormedClassTable ct)
    (hC : C ≠ objectClass) :
    ¬ SemSubtype ct (.negClass C) (.callable P R) := by
  intro hsem
  have hsrc :=
    object_current_denotes_neg_nonobject (ct := ct) (C := C) hwfct hC
  exact object_current_not_denotes_callable (ct := ct) (P := P) (R := R) hwfct (hsem _ hsrc)

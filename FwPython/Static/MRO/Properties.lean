import FwPython.Static.MRO.Compute
import FwPython.Common.MRO.Properties

/-! # MRO meta-theory

Static-only meta-theory (acyclicity, antisymmetry, monotonicity) on top
of the shared MRO membership theorems in `Common.MRO.Properties`. -/

theorem mro_head_eq
    {ct : ClassTable} {c : Class} {mro : List Identifier}
    (hmro : ComputeMro ct c mro) :
    mro.head? = some c.name := by
  cases hmro <;> simp

theorem mro_acyclic
    {ct : ClassTable} {c : Class} {mro : List Identifier}
    (hfc : findClass ct c.name = some c)
    (hmro : ComputeMro ct c mro) :
    c.name ∉ c.resolvedBases ∧
      ∀ {d dcls dmro}, findClass ct d = some dcls → ComputeMro ct dcls dmro →
        d ∈ mro → c.name ∈ dmro → d = c.name := by
  have key := ComputeMro.rec
    (motive_1 := fun ct bases parentMros _ =>
      ∀ pm, pm ∈ parentMros →
        ∃ bname bcls,
          findClass ct bname = some bcls ∧
          bname ∈ bases ∧
          ComputeMro ct bcls pm ∧
          bname ∉ bcls.resolvedBases ∧
          (∀ {d dcls dmro}, findClass ct d = some dcls → ComputeMro ct dcls dmro →
            d ∈ pm → bname ∈ dmro → d = bname))
    (motive_2 := fun ct c mro _ =>
      findClass ct c.name = some c →
      c.name ∉ c.resolvedBases ∧
        ∀ {d dcls dmro}, findClass ct d = some dcls → ComputeMro ct dcls dmro →
          d ∈ mro → c.name ∈ dmro → d = c.name)
    (fun {ct} pm hpmem => absurd hpmem List.not_mem_nil)
    (fun hfind hmro _ ih_mro ih_rest pm hpmem => by
      rcases List.mem_cons.mp hpmem with rfl | hpmem
      · exact ⟨_, _, findClass_self hfind, by simp [findClass_name hfind], hmro,
          (ih_mro (findClass_self hfind)).1,
          (ih_mro (findClass_self hfind)).2⟩
      · obtain ⟨bname, bcls, hfindB, hbmem, hmroB, hnoSelfB, hantiB⟩ := ih_rest pm hpmem
        exact ⟨bname, bcls, hfindB, List.mem_cons_of_mem _ hbmem, hmroB, hnoSelfB, hantiB⟩)
    (fun hnil hfc => by
      refine ⟨?_, ?_⟩
      · simp [hnil]
      · intro d dcls dmro hfd _ hmem _
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        exact hmem)
    (fun {bases} {ct} {parentMros} {mergedSuffix} {c}
         hbases hne hall hmerge ih_parents hfc => by
      let hstep : ComputeMro ct c (c.name :: mergedSuffix) := .step hbases hne hall hmerge
      have hnoSelfBase : c.name ∉ bases := by
        intro hself
        obtain ⟨ccls, cmro, hfindC, hmroC, hpmem⟩ := allParentMros_mem hall hself
        obtain ⟨bname, bcls, hfindB, _, hmroB, hnoSelfB, _⟩ := ih_parents cmro hpmem
        have hbhead := mro_head_eq hmroB
        have hchead := mro_head_eq hmroC
        rw [hchead] at hbhead
        injection hbhead with hname
        have hbname : bname = c.name := by
          rw [← findClass_name hfindB, ← findClass_name hfindC]
          exact hname.symm
        have hbcls : bcls = c := by
          rw [hbname] at hfindB
          rw [hfc] at hfindB
          injection hfindB with hEq
          exact hEq.symm
        subst hbcls
        exact hnoSelfB <| by simpa [hbases, hbname] using hself
      refine ⟨by simpa [hbases] using hnoSelfBase, ?_⟩
      intro d dcls dmro hfd hmd hmem hc_in_d
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact rfl
      · obtain ⟨l, hl, hd_in_l⟩ := c3Merge_sound hmerge d hmem
        rcases List.mem_append.mp hl with hl_pm | hl_bases
        · obtain ⟨bname, bcls, hfindB, hb_in_bases, hmroB, _, hantiB⟩ := ih_parents l hl_pm
          have hb_in_mro : bname ∈ c.name :: mergedSuffix := by
            exact List.mem_cons_of_mem _ <|
              c3Merge_complete hmerge bases (List.mem_append_right _ (List.Mem.head _)) bname hb_in_bases
          have hc_in_l : c.name ∈ l := by
            exact mro_mem_trans ct bcls dcls l dmro c.name
              (findClass_self hfindB) hmroB (findClass_self hfd) hmd
              (by simpa [findClass_name hfd] using hd_in_l) hc_in_d
          have hcb : c.name = bname := hantiB hfc hstep hc_in_l hb_in_mro
          exact False.elim <| hnoSelfBase <| by
            simpa [hcb] using hb_in_bases
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl_bases
          have hd_in_bases : d ∈ bases := by simpa [hl_bases] using hd_in_l
          obtain ⟨dcls', dmro', hfindD, hmroD, hpmem⟩ := allParentMros_mem hall hd_in_bases
          have hdcls : dcls' = dcls := by
            rw [hfd] at hfindD
            injection hfindD with hEq
            exact hEq.symm
          subst dcls'
          have hdmro : dmro' = dmro := determinism hmroD hmd
          obtain ⟨bname, bcls, hfindB, hb_in_bases, hmroB, _, hantiB⟩ := ih_parents dmro' hpmem
          have hb_in_mro : bname ∈ c.name :: mergedSuffix := by
            exact List.mem_cons_of_mem _ <|
              c3Merge_complete hmerge bases (List.mem_append_right _ (List.Mem.head _)) bname hb_in_bases
          have hc_in_dmro' : c.name ∈ dmro' := by simpa [hdmro] using hc_in_d
          have hcb : c.name = bname := hantiB hfc hstep hc_in_dmro' hb_in_mro
          exact False.elim <| hnoSelfBase <| by
            simpa [hcb] using hb_in_bases)
    hmro
  exact key hfc

theorem mro_member_antisymm
    {ct : ClassTable} {C D : Identifier}
    {clsC clsD : Class} {mroC mroD : List Identifier}
    (hfindC : findClass ct C = some clsC)
    (hmroC : ComputeMro ct clsC mroC)
    (hfindD : findClass ct D = some clsD)
    (hmroD : ComputeMro ct clsD mroD)
    (hD_in_C : D ∈ mroC)
    (hC_in_D : C ∈ mroD) :
    C = D :=
  (((mro_acyclic (findClass_self hfindC) hmroC).2 hfindD hmroD hD_in_C
      (by simpa [findClass_name hfindC] using hC_in_D)).trans
    (findClass_name hfindC)).symm

/-! ## MRO monotonicity -/

/-- A class precedes its direct parents in its own MRO. -/
theorem mro_self_precedes_parent
    {ct : ClassTable} {c : Class} {mro : List Identifier} {b : Identifier}
    (hmro : ComputeMro ct c mro)
    (hb : b ∈ c.resolvedBases) :
    appearsBefore c.name b mro = true := by
  cases hmro with
  | root hnil =>
    have hb' : b ∈ ([] : List Identifier) := hnil ▸ hb
    exact absurd hb' List.not_mem_nil
  | @step bases _ parentMros mergedSuffix _ hbases hne hall hmerge =>
    have hb' : b ∈ bases := hbases ▸ hb
    unfold appearsBefore
    rw [if_pos rfl]
    exact containsIdentifier_true_of_mem <|
      c3Merge_complete hmerge _ (List.mem_append_right _ (List.Mem.head _)) b hb'

/-- If A precedes B in some ancestor's MRO, then A precedes B in C's MRO. -/
theorem mro_order_propagation
    {ct : ClassTable} {c : Class} {mro_c : List Identifier}
    (hmro_c : ComputeMro ct c mro_c)
    (hfc : findClass ct c.name = some c)
    {acls : Class} {mro_a : List Identifier}
    (hfa : findClass ct acls.name = some acls)
    (hmro_a : ComputeMro ct acls mro_a)
    (ha_in_mro : acls.name ∈ mro_c)
    {x y : Identifier}
    (hab : appearsBefore x y mro_a = true) :
    appearsBefore x y mro_c = true :=
  appearsBefore_sublist (mro_sublist ct c acls mro_c mro_a hfc hmro_c hfa hmro_a ha_in_mro) hab

/-- If A precedes B in C's direct parent list, then A precedes B in C's MRO. -/
theorem mro_preserves_base_order
    {ct : ClassTable} {c : Class} {mro : List Identifier}
    {a b : Identifier}
    (hmro : ComputeMro ct c mro)
    (hab : appearsBefore a b c.resolvedBases = true) :
    appearsBefore a b mro = true := by
  cases hmro with
  | root hnil =>
    have hab' : appearsBefore a b ([] : List Identifier) = true := hnil ▸ hab
    simp [appearsBefore] at hab'
  | @step bases _ parentMros mergedSuffix _ hbases hne hall hmerge =>
    have hab' : appearsBefore a b bases = true := hbases ▸ hab
    have hbases_mem : bases ∈ parentMros ++ [bases] :=
      List.mem_append_right _ (List.Mem.head _)
    have hab'' := c3Merge_order_preserving hmerge bases hbases_mem a b hab'
    by_cases hca : c.name = a
    · unfold appearsBefore; rw [if_pos hca]
      exact containsIdentifier_true_of_mem <|
        c3Merge_complete hmerge bases hbases_mem b (appearsBefore_right_mem hab')
    · rw [appearsBefore_cons_ne hca]; exact hab''

/-- If B is a direct parent of A and A is in C's MRO, then A precedes B in C's MRO. -/
theorem mro_parent_precedes
    {ct : ClassTable} {c : Class} {mro_c : List Identifier}
    {a : Identifier} {acls : Class} {mro_a : List Identifier} {b : Identifier}
    (hmro_c : ComputeMro ct c mro_c)
    (hfc : findClass ct c.name = some c)
    (hfa : findClass ct a = some acls)
    (hmro_a : ComputeMro ct acls mro_a)
    (ha_in_mro : a ∈ mro_c)
    (hb_parent : b ∈ acls.resolvedBases) :
    appearsBefore a b mro_c = true := by
  have hab : appearsBefore a b mro_a = true := by
    have := mro_self_precedes_parent hmro_a hb_parent
    simpa [findClass_name hfa] using this
  have ha_in_mro' : acls.name ∈ mro_c := by
    simpa [findClass_name hfa] using ha_in_mro
  exact mro_order_propagation hmro_c hfc (findClass_self hfa) hmro_a ha_in_mro' hab

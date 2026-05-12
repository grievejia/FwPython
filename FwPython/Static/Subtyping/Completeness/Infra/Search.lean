import FwPython.Static.Subtyping.Completeness.Infra.Cases

/-! ### Main constructive completeness search -/

def completeArgsMeasure : CompleteArgs ct → Nat × Nat
  | ⟨T, U, _, _, _⟩ => (U.size, T.size)

theorem semSubtype_complete_aux
    (hwfct : WellFormedClassTable ct) :
    (p : CompleteArgs ct) → IsSubtype ct p.T p.U := by
  let go :
      (p : CompleteArgs ct) → IsSubtype ct p.T p.U :=
    WellFounded.fix
      (r := InvImage WellFoundedRelation.rel completeArgsMeasure)
      (C := fun p => IsSubtype ct p.T p.U)
      (hwf := InvImage.wf completeArgsMeasure (WellFoundedRelation.wf (α := Nat × Nat)))
      (fun p ih => by
        rcases p with ⟨T, U, hwfT, hwfU, hsem⟩
        let recurse :=
          fun (T' U' : Ty) (hwfT' : WellFormedTy ct T') (hwfU' : WellFormedTy ct U')
              (hsem' : SemSubtype ct T' U')
              (hlt : WellFoundedRelation.rel
                (completeArgsMeasure ⟨T', U', hwfT', hwfU', hsem'⟩)
                (completeArgsMeasure ⟨T, U, hwfT, hwfU, hsem⟩)) =>
            ih ⟨T', U', hwfT', hwfU', hsem'⟩ hlt
        let solveFreshUnion :=
          fun {S U₀ V₀ : Ty}
              (hwfS : WellFormedTy ct S)
              (hS : S = T)
              (seeds : List Identifier)
              (hseeds_ne : seeds ≠ [])
              (hseeds_nodup : seeds.Nodup)
              (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
              (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
              (seed_source : ∀ s, s ∈ seeds → s = objectClass ∨ Ty.class_ s ∈ S.interAtoms)
              (hdenS : Ty.semDenotes ct S
                (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf))
              (hwfUnion : WellFormedTy ct (Ty.union U₀ V₀))
              (hUnionEq : Ty.union U₀ V₀ = U)
              (hsemUnion : SemSubtype ct S (Ty.union U₀ V₀)) => by
            let atoms := (Ty.union U₀ V₀).unionAtoms
            let flat := Ty.unionAtomsFold atoms
            let oldW :=
              freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
            have hflatWf : WellFormedTy ct flat := by
              refine unionAtomsFold_wellFormed (ct := ct) ?_
              intro A hA
              exact unionAtoms_member_wellFormed (ct := ct) (T := Ty.union U₀ V₀) hwfUnion hA
            have htoFlat : IsSubtype ct (Ty.union U₀ V₀) flat :=
              subtype_self_unionAtomsFold (ct := ct) (T := Ty.union U₀ V₀)
            have hfromFlat : IsSubtype ct flat (Ty.union U₀ V₀) :=
              unionAtomsFold_subtype_self (ct := ct) (T := Ty.union U₀ V₀)
            have hsemFlat : SemSubtype ct S flat :=
              SemSubtype.trans hsemUnion (semSubtype_sound htoFlat)
            have hnoUnion : ∀ X Y, Ty.union X Y ∉ atoms := by
              intro X Y
              simpa [atoms] using unionAtoms_union_not_mem (Ty.union U₀ V₀) X Y
            cases hpick : pickUsefulUnionArm atoms with
            | none =>
                have hnoUseful := pickUsefulUnionArm_spec_none hpick
                exact False.elim <|
                  fresh_not_denotes_unionAtomsFold_of_noUseful
                    (ct := ct)
                    (atoms := atoms)
                    (seeds := seeds)
                    (hseeds_ne := hseeds_ne)
                    (hseeds_nodup := hseeds_nodup)
                    (seedWitness := seedWitness)
                    (seed_nonleaf := seed_nonleaf)
                    hnoUseful hnoUnion (hsemFlat _ hdenS)
            | some pair =>
                rcases pair with ⟨A, rest⟩
                rcases pickUsefulUnionArm_spec_some hpick with
                  ⟨hmemA, huseA, hrestSubset, hcover⟩
                have hreorderTo : IsSubtype ct flat (Ty.unionAtomsFold (A :: rest)) := by
                  exact unionAtomsFold_subtype_of_subset (ct := ct) (atoms₁ := atoms) (atoms₂ := A :: rest)
                    (fun X hX =>
                      match hcover X hX with
                      | Or.inl hEq => by simp [hEq]
                      | Or.inr hXin => by simp [hXin])
                have hreorderFrom : IsSubtype ct (Ty.unionAtomsFold (A :: rest)) flat := by
                  exact unionAtomsFold_subtype_of_subset (ct := ct) (atoms₁ := A :: rest) (atoms₂ := atoms)
                    (fun X hX =>
                      match List.mem_cons.mp hX with
                      | Or.inl hEq => by simpa [hEq] using hmemA
                      | Or.inr hXin => hrestSubset X hXin)
                let R := Ty.unionAtomsFold rest
                have hrest_ne : rest ≠ [] := by
                  have hlen : rest.length + 1 = atoms.length :=
                    pickUsefulUnionArm_length hpick
                  obtain ⟨a, as, hUeq⟩ : ∃ a as, U₀.unionAtoms = a :: as := by
                    cases hUatoms : U₀.unionAtoms with
                    | nil =>
                        cases (Ty.unionAtoms_ne_nil U₀) hUatoms
                    | cons a as =>
                        exact ⟨a, as, rfl⟩
                  obtain ⟨b, bs, hVeq⟩ : ∃ b bs, V₀.unionAtoms = b :: bs := by
                    cases hVatoms : V₀.unionAtoms with
                    | nil =>
                        cases (Ty.unionAtoms_ne_nil V₀) hVatoms
                    | cons b bs =>
                        exact ⟨b, bs, rfl⟩
                  have hatoms_len : 1 < atoms.length := by
                    simp [atoms, Ty.unionAtoms, hUeq, hVeq]
                    omega
                  cases rest with
                  | nil =>
                      simp at hlen
                      omega
                  | cons B Bs =>
                      simp
                have hRwf : WellFormedTy ct R := by
                  refine unionAtomsFold_wellFormed (ct := ct) ?_
                  intro X hX
                  exact unionAtoms_member_wellFormed (ct := ct) (T := Ty.union U₀ V₀) hwfUnion (hrestSubset X hX)
                have hRlt : R.size < (Ty.union U₀ V₀).size := by
                  have hltFlat :
                      R.size < flat.size := by
                    exact pickUsefulUnionArm_rest_size_lt hpick hrest_ne
                  have hflatSize : flat.size = (Ty.union U₀ V₀).size := by
                    simp [flat, atoms, unionAtomsFold_size_eq_self]
                  rw [← hflatSize]
                  exact hltFlat
                have hpickedToUnion : IsSubtype ct (Ty.unionAtomsFold (A :: rest)) (Ty.union A R) := by
                  cases rest with
                  | nil =>
                      cases hrest_ne rfl
                  | cons B Bs =>
                      exact .refl
                have hunionToPicked : IsSubtype ct (Ty.union A R) (Ty.unionAtomsFold (A :: rest)) := by
                  cases rest with
                  | nil =>
                      cases hrest_ne rfl
                  | cons B Bs =>
                      exact .refl
                have hsemAR : SemSubtype ct S (Ty.union A R) :=
                  SemSubtype.trans (SemSubtype.trans hsemFlat (semSubtype_sound hreorderTo))
                    (semSubtype_sound hpickedToUnion)
                have hfinish :
                    IsSubtype ct S (Ty.union A R) →
                    IsSubtype ct S (Ty.union U₀ V₀) := by
                  intro hsub
                  exact .trans hsub <| .trans hunionToPicked <| .trans hreorderFrom hfromFlat
                have hwfA : WellFormedTy ct A :=
                  unionAtoms_member_wellFormed (ct := ct) (T := Ty.union U₀ V₀) hwfUnion hmemA
                have hARSize : (Ty.union A R).size = (Ty.union U₀ V₀).size := by
                  have hsum : tySizeSum rest + A.size = tySizeSum atoms :=
                    pickUsefulUnionArm_sizeSum hpick
                  have hlen : rest.length + 1 = atoms.length :=
                    pickUsefulUnionArm_length hpick
                  have hsizeRest : R.size = tySizeSum rest + rest.length - 1 :=
                    unionAtomsFold_size_formula hrest_ne
                  have hatoms_ne : atoms ≠ [] := by
                    intro hnil
                    have h := Ty.unionAtoms_ne_nil (Ty.union U₀ V₀)
                    exact h (by simpa [atoms] using hnil)
                  have hsizeAtoms : flat.size = tySizeSum atoms + atoms.length - 1 :=
                    unionAtomsFold_size_formula hatoms_ne
                  have hflatEq : flat.size = (Ty.union U₀ V₀).size :=
                    unionAtomsFold_size_eq_self (T := Ty.union U₀ V₀)
                  have hflatUnion : (Ty.union A R).size = flat.size := by
                    have hsum' : A.size + tySizeSum rest = tySizeSum atoms := by
                      simpa [Nat.add_comm] using hsum
                    have hge : 1 ≤ tySizeSum rest + rest.length := by
                      cases rest with
                      | nil =>
                          cases hrest_ne rfl
                      | cons B Bs =>
                          have hBsize : 1 ≤ B.size := by
                            cases B <;> simp [Ty.size] <;> omega
                          simp [tySizeSum]
                          omega
                    calc
                      (Ty.union A R).size
                          = 1 + A.size + R.size := by
                              simp [Ty.size]
                      _ = 1 + A.size + (tySizeSum rest + rest.length - 1) := by
                            rw [hsizeRest]
                      _ = A.size + (1 + (tySizeSum rest + rest.length - 1)) := by
                            omega
                      _ = A.size + ((tySizeSum rest + rest.length - 1) + 1) := by
                            omega
                      _ = A.size + (tySizeSum rest + rest.length) := by
                            rw [Nat.sub_add_cancel hge]
                      _ = A.size + tySizeSum rest + rest.length := by
                            omega
                      _ = tySizeSum atoms + atoms.length - 1 := by
                            rw [hsum']
                            omega
                      _ = flat.size := by
                            symm
                            exact hsizeAtoms
                  exact hflatUnion.trans hflatEq
                cases A with
                | bottom =>
                    have hsemR : SemSubtype ct S R := by
                      intro obj hobj
                      rcases hsemAR obj hobj with hbot | hR
                      · cases hbot
                      · exact hR
                    exact hfinish <|
                      .unionRight
                        (recurse S R hwfS hRwf hsemR <|
                          by
                            simpa [hS, hUnionEq, completeArgsMeasure] using
                              (Prod.Lex.left S.size S.size hRlt :
                                Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                                  (R.size, S.size) ((Ty.union U₀ V₀).size, S.size)))
                | class_ D =>
                    by_cases hDobj : D = objectClass
                    · subst hDobj
                      exact hfinish (.unionLeft .objectTop)
                    · have hwfNegD : WellFormedTy ct (Ty.negClass D) := by
                        exact WellFormedTy.neg_of_class hwfA
                      have hsemR : SemSubtype ct (Ty.intersection S (Ty.negClass D)) R :=
                        semSubtype_inter_neg_of_class_left (ct := ct) (S := S) (D := D) (U := R) hsemAR
                      have hsubR :=
                        recurse (Ty.intersection S (Ty.negClass D)) R
                          (WellFormedTy.intersection hwfS hwfNegD) hRwf hsemR <|
                          by
                            simpa [hS, hUnionEq, completeArgsMeasure] using
                              (Prod.Lex.left (Ty.intersection S (Ty.negClass D)).size S.size hRlt :
                                Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                                  (R.size, (Ty.intersection S (Ty.negClass D)).size)
                                  ((Ty.union U₀ V₀).size, S.size))
                      exact hfinish <|
                        class_union_of_inter_neg_subtype (ct := ct) (S := S) (D := D) hsubR
                | negClass B =>
                    have hwfClassB : WellFormedTy ct (Ty.class_ B) :=
                      WellFormedTy.class_of_neg hwfA
                    have hsemR : SemSubtype ct (Ty.intersection S (Ty.class_ B)) R :=
                      semSubtype_inter_class_of_neg_left (ct := ct) (S := S) (B := B) (U := R) hsemAR
                    have hsubR :=
                      recurse (Ty.intersection S (Ty.class_ B)) R
                        (WellFormedTy.intersection hwfS hwfClassB) hRwf hsemR <|
                        by
                          simpa [hS, hUnionEq, completeArgsMeasure] using
                            (Prod.Lex.left (Ty.intersection S (Ty.class_ B)).size S.size hRlt :
                              Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                                (R.size, (Ty.intersection S (Ty.class_ B)).size)
                                ((Ty.union U₀ V₀).size, S.size))
                    exact hfinish <|
                      negClass_union_of_inter_class_subtype (ct := ct) (S := S) (B := B) hsubR
                | intersection A₁ A₂ =>
                    have hsemL : SemSubtype ct S (Ty.union A₁ R) := by
                      intro obj hobj
                      rcases hsemAR obj hobj with hA | hR
                      · exact Or.inl hA.1
                      · exact Or.inr hR
                    have hsemR' : SemSubtype ct S (Ty.union A₂ R) := by
                      intro obj hobj
                      rcases hsemAR obj hobj with hA | hR
                      · exact Or.inl hA.2
                      · exact Or.inr hR
                    have hwfL : WellFormedTy ct (Ty.union A₁ R) :=
                      .union hwfA.intersection_left hRwf
                    have hwfR' : WellFormedTy ct (Ty.union A₂ R) :=
                      .union hwfA.intersection_right hRwf
                    have hsubL :=
                      recurse S (Ty.union A₁ R) hwfS hwfL hsemL <|
                        by
                          have hlt : (Ty.union A₁ R).size < (Ty.union U₀ V₀).size := by
                            rw [← hARSize]
                            simp [Ty.size]
                            omega
                          simpa [hS, hUnionEq, completeArgsMeasure] using
                            (Prod.Lex.left S.size S.size hlt :
                              Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                                ((Ty.union A₁ R).size, S.size) ((Ty.union U₀ V₀).size, S.size))
                    have hsubR' :=
                      recurse S (Ty.union A₂ R) hwfS hwfR' hsemR' <|
                        by
                          have hlt : (Ty.union A₂ R).size < (Ty.union U₀ V₀).size := by
                            rw [← hARSize]
                            simp [Ty.size]
                            omega
                          simpa [hS, hUnionEq, completeArgsMeasure] using
                            (Prod.Lex.left S.size S.size hlt :
                              Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                                ((Ty.union A₂ R).size, S.size) ((Ty.union U₀ V₀).size, S.size))
                    exact hfinish <|
                      .trans
                        (.interIntro
                          (.trans hsubL subtype_union_comm)
                          (.trans hsubR' subtype_union_comm))
                        (.trans subtype_inter_union_distrib' subtype_union_comm)
                | callable _ _ | union _ _ =>
                    cases huseA
        cases T with
        | bottom =>
            exact .bottom
        | union T₁ T₂ =>
            let split := splitNonUnionFree (T := Ty.union T₁ T₂) (by simp [Ty.unionFree])
            let hwfL := splitNonUnionFree_wf_left hwfT (by simp [Ty.unionFree])
            let hwfR := splitNonUnionFree_wf_right hwfT (by simp [Ty.unionFree])
            have hsubL : IsSubtype ct split.left (Ty.union T₁ T₂) := by
              exact .trans (.unionLeft .refl) split.fromUnion
            have hsubR : IsSubtype ct split.right (Ty.union T₁ T₂) := by
              exact .trans (.unionRight .refl) split.fromUnion
            have hsemL : SemSubtype ct split.left U :=
              SemSubtype.trans (semSubtype_sound hsubL) hsem
            have hsemR : SemSubtype ct split.right U :=
              SemSubtype.trans (semSubtype_sound hsubR) hsem
            exact .trans split.toUnion <|
              .unionElim
                (recurse split.left U hwfL hwfU hsemL <|
                  by
                    simpa [completeArgsMeasure] using
                      (Prod.Lex.right U.size split.left_lt :
                        Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                          (U.size, split.left.size) (U.size, (Ty.union T₁ T₂).size)))
                (recurse split.right U hwfR hwfU hsemR <|
                  by
                    simpa [completeArgsMeasure] using
                      (Prod.Lex.right U.size split.right_lt :
                        Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                          (U.size, split.right.size) (U.size, (Ty.union T₁ T₂).size)))
        | class_ C =>
            by_cases huf : (Ty.class_ C).unionFree
            · cases U with
              | bottom =>
                  exact complete_clean_bottom (ct := ct) (S := .class_ C) hwfct hwfT huf hsem
              | class_ D =>
                  by_cases hD : D = objectClass
                  · subst hD
                    exact .objectTop
                  · exact complete_clean_class_nonobject
                      (ct := ct) (S := .class_ C) (D := D)
                      hwfct hwfT huf hwfU hD hsem
              | negClass D =>
                  exact complete_clean_neg
                    (ct := ct) (S := .class_ C) (D := D)
                    hwfct hwfT huf hwfU hsem
              | callable P R =>
                  exact complete_clean_callable
                    (ct := ct) (S := .class_ C) (P := P) (R := R)
                    hwfct hwfT huf hsem
              | union U V =>
                  let hcase := analyzeCleanSource (ct := ct) (S := .class_ C) hwfct hwfT huf
                  have hres := complete_clean_case_or_fresh
                    (ct := ct) (S := .class_ C) (U := .union U V)
                    hwfct hwfT hcase hwfU hsem
                  cases hres with
                  | inl hsub =>
                      exact hsub
                  | inr hfresh =>
                      rcases hfresh with
                        ⟨seeds, hseeds_ne, hseeds_nodup, seedWitness, seed_nonleaf, seed_source, hden, _⟩
                      exact solveFreshUnion (S := Ty.class_ C) (U₀ := U) (V₀ := V)
                        hwfT rfl seeds hseeds_ne hseeds_nodup
                        seedWitness seed_nonleaf seed_source hden
                        hwfU rfl hsem
              | intersection U V =>
                  exact .interIntro
                    (recurse (Ty.class_ C) U hwfT hwfU.intersection_left
                      (fun obj hT => (hsem obj hT).1) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.class_ C).size (Ty.class_ C).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (U.size, (Ty.class_ C).size) ((Ty.intersection U V).size, (Ty.class_ C).size)))
                    (recurse (Ty.class_ C) V hwfT hwfU.intersection_right
                      (fun obj hT => (hsem obj hT).2) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.class_ C).size (Ty.class_ C).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (V.size, (Ty.class_ C).size) ((Ty.intersection U V).size, (Ty.class_ C).size)))
            · exfalso
              exact huf (by simp [Ty.unionFree])
        | negClass C =>
            by_cases huf : (Ty.negClass C).unionFree
            · cases U with
              | bottom =>
                  exact complete_clean_bottom (ct := ct) (S := .negClass C) hwfct hwfT huf hsem
              | class_ D =>
                  by_cases hD : D = objectClass
                  · subst hD
                    exact .objectTop
                  · exact complete_clean_class_nonobject
                      (ct := ct) (S := .negClass C) (D := D)
                      hwfct hwfT huf hwfU hD hsem
              | negClass D =>
                  exact complete_clean_neg
                    (ct := ct) (S := .negClass C) (D := D)
                    hwfct hwfT huf hwfU hsem
              | callable P R =>
                  exact complete_clean_callable
                    (ct := ct) (S := .negClass C) (P := P) (R := R)
                    hwfct hwfT huf hsem
              | union U V =>
                  by_cases hC : C = objectClass
                  · subst hC
                    have hsemBot : SemSubtype ct (.negClass objectClass) .bottom := by
                      intro obj hneg
                      cases obj with
                      | ordinaryCurrent cur =>
                          exact hneg cur.object_mem
                      | ordinaryFresh fr =>
                          exact hneg fr.object_mem
                      | boundMethod bm =>
                          exact hneg bm.object_mem
                    exact .trans
                      (complete_neg_bottom
                        (ct := ct) (C := objectClass)
                        hwfct hwfT hsemBot)
                      .bottom
                  · let hcase := analyzeCleanSource (ct := ct) (S := .negClass C) hwfct hwfT huf
                    have hres := complete_clean_case_or_fresh
                      (ct := ct) (S := .negClass C) (U := .union U V)
                      hwfct hwfT hcase hwfU hsem
                    cases hres with
                    | inl hsub =>
                        exact hsub
                    | inr hfresh =>
                        rcases hfresh with
                          ⟨seeds, hseeds_ne, hseeds_nodup, seedWitness, seed_nonleaf, seed_source, hden, _⟩
                        exact solveFreshUnion (S := Ty.negClass C) (U₀ := U) (V₀ := V)
                          hwfT rfl seeds hseeds_ne hseeds_nodup
                          seedWitness seed_nonleaf seed_source hden
                          hwfU rfl hsem
              | intersection U V =>
                  exact .interIntro
                    (recurse (Ty.negClass C) U hwfT hwfU.intersection_left
                      (fun obj hT => (hsem obj hT).1) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.negClass C).size (Ty.negClass C).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (U.size, (Ty.negClass C).size) ((Ty.intersection U V).size, (Ty.negClass C).size)))
                    (recurse (Ty.negClass C) V hwfT hwfU.intersection_right
                      (fun obj hT => (hsem obj hT).2) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.negClass C).size (Ty.negClass C).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (V.size, (Ty.negClass C).size) ((Ty.intersection U V).size, (Ty.negClass C).size)))
            · exfalso
              exact huf (by simp [Ty.unionFree])
        | callable P R =>
            by_cases huf : (Ty.callable P R).unionFree
            · cases U with
              | bottom =>
                  exact complete_clean_bottom (ct := ct) (S := .callable P R) hwfct hwfT huf hsem
              | class_ D =>
                  by_cases hD : D = objectClass
                  · subst hD
                    exact .objectTop
                  · exact complete_clean_class_nonobject
                      (ct := ct) (S := .callable P R) (D := D)
                      hwfct hwfT huf hwfU hD hsem
              | negClass D =>
                  exact complete_clean_neg
                    (ct := ct) (S := .callable P R) (D := D)
                    hwfct hwfT huf hwfU hsem
              | callable P' R' =>
                  exact complete_clean_callable
                    (ct := ct) (S := .callable P R) (P := P') (R := R')
                    hwfct hwfT huf hsem
              | union U V =>
                  exact complete_callable_union
                    (ct := ct) (P := P) (R := R) (T := U) (U := V)
                    hwfct hwfT hwfU hsem
              | intersection U V =>
                  exact .interIntro
                    (recurse (Ty.callable P R) U hwfT hwfU.intersection_left
                      (fun obj hT => (hsem obj hT).1) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.callable P R).size (Ty.callable P R).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (U.size, (Ty.callable P R).size) ((Ty.intersection U V).size, (Ty.callable P R).size)))
                    (recurse (Ty.callable P R) V hwfT hwfU.intersection_right
                      (fun obj hT => (hsem obj hT).2) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.callable P R).size (Ty.callable P R).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (V.size, (Ty.callable P R).size) ((Ty.intersection U V).size, (Ty.callable P R).size)))
            · exfalso
              exact huf (by simp [Ty.unionFree])
        | intersection T₁ T₂ =>
            by_cases huf : (Ty.intersection T₁ T₂).unionFree
            · cases U with
              | bottom =>
                  exact complete_clean_bottom
                    (ct := ct) (S := .intersection T₁ T₂) hwfct hwfT huf hsem
              | class_ D =>
                  by_cases hD : D = objectClass
                  · subst hD
                    exact .objectTop
                  · exact complete_clean_class_nonobject
                      (ct := ct) (S := .intersection T₁ T₂) (D := D)
                      hwfct hwfT huf hwfU hD hsem
              | negClass D =>
                  exact complete_clean_neg
                    (ct := ct) (S := .intersection T₁ T₂) (D := D)
                    hwfct hwfT huf hwfU hsem
              | callable P R =>
                  exact complete_clean_callable
                    (ct := ct) (S := .intersection T₁ T₂) (P := P) (R := R)
                    hwfct hwfT huf hsem
              | union U V =>
                  let hcase := analyzeCleanSource (ct := ct) (S := .intersection T₁ T₂) hwfct hwfT huf
                  have hres := complete_clean_case_or_fresh
                    (ct := ct) (S := .intersection T₁ T₂) (U := .union U V)
                    hwfct hwfT hcase hwfU hsem
                  cases hres with
                  | inl hsub =>
                      exact hsub
                  | inr hfresh =>
                      rcases hfresh with
                        ⟨seeds, hseeds_ne, hseeds_nodup, seedWitness, seed_nonleaf, seed_source, hden, _⟩
                      exact solveFreshUnion (S := Ty.intersection T₁ T₂) (U₀ := U) (V₀ := V)
                        hwfT rfl seeds hseeds_ne hseeds_nodup
                        seedWitness seed_nonleaf seed_source hden
                        hwfU rfl hsem
              | intersection U V =>
                  exact .interIntro
                    (recurse (Ty.intersection T₁ T₂) U hwfT hwfU.intersection_left
                      (fun obj hT => (hsem obj hT).1) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.intersection T₁ T₂).size (Ty.intersection T₁ T₂).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (U.size, (Ty.intersection T₁ T₂).size)
                              ((Ty.intersection U V).size, (Ty.intersection T₁ T₂).size)))
                    (recurse (Ty.intersection T₁ T₂) V hwfT hwfU.intersection_right
                      (fun obj hT => (hsem obj hT).2) <|
                      by
                        simpa [completeArgsMeasure] using
                          (Prod.Lex.left (Ty.intersection T₁ T₂).size (Ty.intersection T₁ T₂).size (by simp [Ty.size]; omega) :
                            Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                              (V.size, (Ty.intersection T₁ T₂).size)
                              ((Ty.intersection U V).size, (Ty.intersection T₁ T₂).size)))
            · let split := splitNonUnionFree (T := Ty.intersection T₁ T₂) huf
              let hwfL := splitNonUnionFree_wf_left hwfT huf
              let hwfR := splitNonUnionFree_wf_right hwfT huf
              have hsubL : IsSubtype ct split.left (Ty.intersection T₁ T₂) := by
                exact .trans (.unionLeft .refl) split.fromUnion
              have hsubR : IsSubtype ct split.right (Ty.intersection T₁ T₂) := by
                exact .trans (.unionRight .refl) split.fromUnion
              have hsemL : SemSubtype ct split.left U :=
                SemSubtype.trans (semSubtype_sound hsubL) hsem
              have hsemR : SemSubtype ct split.right U :=
                SemSubtype.trans (semSubtype_sound hsubR) hsem
              exact .trans split.toUnion <|
                .unionElim
                  (recurse split.left U hwfL hwfU hsemL <|
                    by
                      simpa [completeArgsMeasure] using
                        (Prod.Lex.right U.size split.left_lt :
                          Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                            (U.size, split.left.size) (U.size, (Ty.intersection T₁ T₂).size)))
                  (recurse split.right U hwfR hwfU hsemR <|
                    by
                      simpa [completeArgsMeasure] using
                        (Prod.Lex.right U.size split.right_lt :
                          Prod.Lex (fun a₁ a₂ ↦ a₁ < a₂) (fun a₁ a₂ ↦ a₁ < a₂)
                            (U.size, split.right.size) (U.size, (Ty.intersection T₁ T₂).size))))
  exact go

theorem semSubtype_complete
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U)
    (hsem : SemSubtype ct T U) :
    IsSubtype ct T U :=
  semSubtype_complete_aux (ct := ct) hwfct ⟨T, U, hwfT, hwfU, hsem⟩

theorem isSubtype_iff_semSubtype
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    IsSubtype ct T U ↔ SemSubtype ct T U := by
  constructor
  · intro hsub
    exact semSubtype_sound hsub
  · intro hsem
    exact semSubtype_complete (ct := ct) hwfct hwfT hwfU hsem

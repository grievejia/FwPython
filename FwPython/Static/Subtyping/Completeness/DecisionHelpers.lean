import FwPython.Static.Subtyping.Completeness.Infra

/-! ## Constructive decision procedure -/

private structure LeafConflictWitness (ct : ClassTable) (atoms : List Ty) where
  B : Identifier
  C : Identifier
  hne : B ≠ C
  hleafB : LeafBuiltin ct B
  hleafC : LeafBuiltin ct C
  hmemB : .class_ B ∈ atoms
  hmemC : .class_ C ∈ atoms

private def LeafConflictWitness.cons (atom : Ty)
    (w : LeafConflictWitness ct atoms) :
    LeafConflictWitness ct (atom :: atoms) :=
  { w with
    hmemB := List.mem_cons_of_mem _ w.hmemB
    hmemC := List.mem_cons_of_mem _ w.hmemC }

private structure SeedNegConflictWitness
    (ct : ClassTable)
    (seeds : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (negs : List Identifier) where
  s : Identifier
  hs : s ∈ seeds
  E : Identifier
  hmem : E ∈ negs
  hIn : E ∈ (seedWitness s hs).mro

private structure SeedClassHitWitness
    (ct : ClassTable)
    (seeds : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (D : Identifier) where
  s : Identifier
  hs : s ∈ seeds
  hmem : D ∈ (seedWitness s hs).mro

private inductive SeedNegConflictOrClear
    (ct : ClassTable)
    (seeds negs : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s) : Type where
  | conflict :
      SeedNegConflictWitness ct seeds seedWitness negs →
      SeedNegConflictOrClear ct seeds negs seedWitness
  | clear :
      (∀ s hs E, E ∈ negs → E ∉ (seedWitness s hs).mro) →
      SeedNegConflictOrClear ct seeds negs seedWitness

private inductive SeedClassHitOrClear
    (ct : ClassTable)
    (seeds : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (D : Identifier) : Type where
  | hit :
      SeedClassHitWitness ct seeds seedWitness D →
      SeedClassHitOrClear ct seeds seedWitness D
  | clear :
      (∀ s hs, D ∉ (seedWitness s hs).mro) →
      SeedClassHitOrClear ct seeds seedWitness D

inductive SeedSourceWitness (S : Ty) (s : Identifier) : Type where
  | object : s = objectClass → SeedSourceWitness S s
  | source : .class_ s ∈ S.interAtoms → SeedSourceWitness S s

private def summarizeInterAtoms_leafConflict_witness'
    (hwfct : WellFormedClassTable ct)
    {atoms : List Ty}
    (hconf : (summarizeInterAtoms hwfct atoms).leafConflict = true) :
    LeafConflictWitness ct atoms :=
  match atoms with
  | [] => by
      simp [summarizeInterAtoms, emptyCleanSourceSummary] at hconf
  | atom :: atoms => by
      cases atom with
      | class_ E =>
          cases hdec : builtinLeafDecidable (C := E) hwfct with
          | isTrue hleafE =>
              let s := summarizeInterAtoms hwfct atoms
              have hupd : (updateDistinct E s.leafClassAtom s.leafConflict).2 = true := by
                simpa [summarizeInterAtoms, s, hdec] using hconf
              cases hsconf : s.leafConflict with
              | true =>
                  let w := summarizeInterAtoms_leafConflict_witness'
                    (hwfct := hwfct) (atoms := atoms)
                    (by simpa [s] using hsconf)
                  exact w.cons _
              | false =>
                  cases hcurr : s.leafClassAtom with
                  | none =>
                      simp [updateDistinct, s, hsconf, hcurr] at hupd
                  | some C =>
                      have hcurr' : (summarizeInterAtoms hwfct atoms).leafClassAtom = some C := by
                        simpa [s] using hcurr
                      have hne : E ≠ C := by
                        by_cases hEq : E = C
                        · subst hEq
                          simp [updateDistinct, s, hsconf, hcurr] at hupd
                        · exact hEq
                      have hleafInfo := summarizeInterAtoms_leafAtom_mem (hwfct := hwfct) hcurr'
                      exact
                        { B := E
                          C := C
                          hne := hne
                          hleafB := hleafE
                          hleafC := hleafInfo.2
                          hmemB := by simp
                          hmemC := List.mem_cons_of_mem _ hleafInfo.1 }
          | isFalse _ =>
              exact (summarizeInterAtoms_leafConflict_witness'
                (hwfct := hwfct) (atoms := atoms)
                (by simpa [summarizeInterAtoms, hdec] using hconf)).cons _
      | bottom | negClass | union | intersection | callable =>
          exact (summarizeInterAtoms_leafConflict_witness'
            (hwfct := hwfct) (atoms := atoms)
            (by simpa [summarizeInterAtoms] using hconf)).cons _

private def seeds_neg_conflict_or_clear'
    (seeds : List Identifier)
    (negs : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s) :
    SeedNegConflictOrClear ct seeds negs seedWitness :=
  match seeds with
  | [] =>
      .clear (by intro s hs; cases hs)
  | s :: ss =>
      match hfirst : firstInside negs (seedWitness s (by simp)).mro with
      | some E =>
          let hsome := firstInside_some hfirst
          .conflict
            { s := s
              hs := by simp
              E := E
              hmem := hsome.1
              hIn := by simpa using hsome.2 }
      | none =>
          let tailWitness : ∀ s, s ∈ ss → FreshSeedInfo ct s :=
            fun s hs => seedWitness s (by simp [hs])
          match seeds_neg_conflict_or_clear' (ct := ct) ss negs tailWitness with
          | .conflict hconf =>
              .conflict
                { s := hconf.s
                  hs := by simp [hconf.hs]
                  E := hconf.E
                  hmem := hconf.hmem
                  hIn := hconf.hIn }
          | .clear hclear =>
              .clear <| by
                intro s' hs' E hEmem
                rcases List.mem_cons.mp hs' with rfl | hs'
                · exact firstInside_none hfirst E hEmem
                · exact hclear s' hs' E hEmem

private def seeds_class_hit_or_clear'
    (seeds : List Identifier)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (D : Identifier) :
    SeedClassHitOrClear ct seeds seedWitness D :=
  match seeds with
  | [] =>
      .clear (by intro s hs; cases hs)
  | s :: ss =>
      let hsHead : s ∈ s :: ss := by simp
      if hhead : D ∈ (seedWitness s hsHead).mro then
        .hit
          { s := s
            hs := by simp
            hmem := hhead }
      else
        let tailWitness : ∀ s, s ∈ ss → FreshSeedInfo ct s :=
          fun s hs => seedWitness s (by simp [hs])
        match seeds_class_hit_or_clear' (ct := ct) ss tailWitness D with
        | .hit htail =>
            .hit
              { s := htail.s
                hs := by simp [htail.hs]
                hmem := htail.hmem }
        | .clear htail =>
            .clear <| by
              intro s' hs'
              rcases List.mem_cons.mp hs' with rfl | hs'
              · exact hhead
              · exact htail s' hs'

def leafBuiltinLookup
    (hwfct : WellFormedClassTable ct)
    (hleaf : LeafBuiltin ct B) :
    ClassLookupWitness ct B := by
  by_cases hbool : B = boolClass
  · subst hbool
    exact hwfct.boolExists
  · by_cases hnone : B = noneClass
    · subst hnone
      exact hwfct.noneExists
    · by_cases hbm : B = boundMethodClass
      · subst hbm
        exact hwfct.boundMethodExists
      · have hfalse : False := by
          have hbuiltin := (leafBuiltin_iff_builtinName (ct := ct) (C := B) hwfct).1 hleaf
          rcases hbuiltin with h | h | h
          · exact hbool h
          · exact hnone h
          · exact hbm h
        exact False.elim hfalse

inductive DecisionCleanSourceCase
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S) : Type where
  | empty :
      IsSubtype ct S .bottom →
      DecisionCleanSourceCase hwfct hwfS
  | currentFromLeaf
      (cname : Identifier)
      (w : ClassLookupWitness ct cname)
      (hleaf : LeafBuiltin ct cname)
      (hden : Ty.semDenotes ct S (currentObjOf (ct := ct) cname w.hfind w.hmro))
      (hsub : IsSubtype ct S (.class_ cname))
      (hrev : IsSubtype ct (.class_ cname) S) :
      DecisionCleanSourceCase hwfct hwfS
  | freshFromSeeds
      (seeds : List Identifier)
      (hseeds_ne : seeds ≠ [])
      (hseeds_nodup : seeds.Nodup)
      (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
      (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
      (seedSource : ∀ s, s ∈ seeds → SeedSourceWitness S s)
      (hden : Ty.semDenotes ct S
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
      DecisionCleanSourceCase hwfct hwfS
  | boundMethodFromCallables
      (Psum Rsum : Ty)
      (hwfPsum : WellFormedTy ct Psum)
      (hwfRsum : WellFormedTy ct Rsum)
      (hPsumSize : Psum.size ≤ S.size)
      (hRsumSize : Rsum.size ≤ S.size)
      (hden : Ty.semDenotes ct S (boundMethodObj (ct := ct) hwfct Psum Rsum))
      (hsub : IsSubtype ct S (.callable Psum Rsum)) :
      DecisionCleanSourceCase hwfct hwfS

def mkDecisionCurrentFromLeaf
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hbot : (summarizeInterAtoms hwfct S.interAtoms).hasBottom = false)
    (hcall : (summarizeInterAtoms hwfct S.interAtoms).callableAtoms = [])
    (w : ClassLookupWitness ct B)
    (hleaf : LeafBuiltin ct B)
    (hsub : IsSubtype ct S (.class_ B))
    (hclass : ∀ D, .class_ D ∈ S.interAtoms → D ∈ w.mro)
    (hneg : ∀ E, .negClass E ∈ S.interAtoms → E ∉ w.mro) :
    DecisionCleanSourceCase (ct := ct) (S := S) hwfct hwfS := by
  have hden :
      Ty.semDenotes ct S (currentObjOf (ct := ct) B w.hfind w.hmro) := by
    refine semDenotes_source_of_atoms (ct := ct) (S := S)
      (obj := currentObjOf (ct := ct) B w.hfind w.hmro) huf ?_
    intro A hmemA
    cases A with
    | bottom =>
        exact False.elim <| no_bottom_atom_of_false
          (hwfct := hwfct) (atoms := S.interAtoms) hbot hmemA
    | class_ D =>
        exact (currentObjOf_denotes_class
          (ct := ct) (C := B) (D := D) w.hfind w.hmro).2
          (hclass D hmemA)
    | negClass E =>
        exact (currentObjOf_denotes_neg_iff
          (ct := ct) (C := B) (D := E) w.hfind w.hmro).2
          (hneg E hmemA)
    | callable P R =>
        exact False.elim <| no_callable_atom_of_nil
          (hwfct := hwfct) (atoms := S.interAtoms)
          (P := P) (R := R) hcall hmemA
    | union T U =>
        exact False.elim (interAtoms_union_not_mem S T U huf hmemA)
    | intersection T U =>
        exact False.elim (interAtoms_intersection_not_mem S T U huf hmemA)
  have hrev :
      IsSubtype ct (.class_ B) S := by
    refine subtype_source_of_atoms (ct := ct) (T := .class_ B)
      (S := S) huf ?_
    intro A hmemA
    cases A with
    | bottom =>
        exact False.elim <| no_bottom_atom_of_false
          (hwfct := hwfct) (atoms := S.interAtoms) hbot hmemA
    | class_ D =>
        exact .class_ w.hfind w.hmro (hclass D hmemA)
    | negClass E =>
        exact .sealedClassNegClass hleaf w.hfind w.hmro (hneg E hmemA)
    | callable P R =>
        exact False.elim <| no_callable_atom_of_nil
          (hwfct := hwfct) (atoms := S.interAtoms)
          (P := P) (R := R) hcall hmemA
    | union T U =>
        exact False.elim (interAtoms_union_not_mem S T U huf hmemA)
    | intersection T U =>
        exact False.elim (interAtoms_intersection_not_mem S T U huf hmemA)
  exact .currentFromLeaf B w hleaf hden hsub hrev

def mkDecisionFreshFromSeeds
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hbot : (summarizeInterAtoms hwfct S.interAtoms).hasBottom = false)
    (hcall : (summarizeInterAtoms hwfct S.interAtoms).callableAtoms = [])
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (seedSource : ∀ s, s ∈ seeds → SeedSourceWitness S s)
    (hclassDenotes : ∀ D, .class_ D ∈ S.interAtoms →
      Ty.semDenotes ct (.class_ D)
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf))
    (hnegDenotes : ∀ E, .negClass E ∈ S.interAtoms →
      Ty.semDenotes ct (.negClass E)
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
    DecisionCleanSourceCase (ct := ct) (S := S) hwfct hwfS := by
  have hden :
      Ty.semDenotes ct S
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
    refine semDenotes_source_of_atoms (ct := ct) (S := S)
      (obj := freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) huf ?_
    intro A hmemA
    cases A with
    | bottom =>
        exact False.elim <| no_bottom_atom_of_false
          (hwfct := hwfct) (atoms := S.interAtoms) hbot hmemA
    | class_ D =>
        exact hclassDenotes D hmemA
    | negClass E =>
        exact hnegDenotes E hmemA
    | callable P R =>
        exact False.elim <| no_callable_atom_of_nil
          (hwfct := hwfct) (atoms := S.interAtoms)
          (P := P) (R := R) hcall hmemA
    | union T U =>
        exact False.elim (interAtoms_union_not_mem S T U huf hmemA)
    | intersection T U =>
        exact False.elim (interAtoms_intersection_not_mem S T U huf hmemA)
  exact .freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden

def mkDecisionBoundMethodFromCallables
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hbot : (summarizeInterAtoms hwfct S.interAtoms).hasBottom = false)
    (Psum Rsum : Ty)
    (hwfPsum : WellFormedTy ct Psum)
    (hwfRsum : WellFormedTy ct Rsum)
    (hPsumSize : Psum.size ≤ S.size)
    (hRsumSize : Rsum.size ≤ S.size)
    (hsub : IsSubtype ct S (.callable Psum Rsum))
    (hclass : ∀ D, .class_ D ∈ S.interAtoms → D ∈ hwfct.boundMethodExists.mro)
    (hneg : ∀ E, .negClass E ∈ S.interAtoms → E ∉ hwfct.boundMethodExists.mro)
    (hcallDenotes : ∀ P R, .callable P R ∈ S.interAtoms →
      Ty.semDenotes ct (.callable P R) (boundMethodObj (ct := ct) hwfct Psum Rsum)) :
    DecisionCleanSourceCase (ct := ct) (S := S) hwfct hwfS := by
  have hden :
      Ty.semDenotes ct S (boundMethodObj (ct := ct) hwfct Psum Rsum) := by
    refine semDenotes_source_of_atoms (ct := ct) (S := S)
      (obj := boundMethodObj (ct := ct) hwfct Psum Rsum) huf ?_
    intro A hmemA
    cases A with
    | bottom =>
        exact False.elim <| no_bottom_atom_of_false
          (hwfct := hwfct) (atoms := S.interAtoms) hbot hmemA
    | class_ D =>
        exact (boundMethodObj_denotes_class_iff
          (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).2
          (hclass D hmemA)
    | negClass E =>
        exact (boundMethodObj_denotes_neg_iff
          (ct := ct) (C := E) (P := Psum) (R := Rsum) hwfct).2
          (hneg E hmemA)
    | callable P R =>
        exact hcallDenotes P R hmemA
    | union T U =>
        exact False.elim (interAtoms_union_not_mem S T U huf hmemA)
    | intersection T U =>
        exact False.elim (interAtoms_intersection_not_mem S T U huf hmemA)
  exact .boundMethodFromCallables Psum Rsum hwfPsum hwfRsum hPsumSize hRsumSize hden hsub

def analyzeDecisionCleanSource
    (hwfct : WellFormedClassTable ct)
    (hwfS : WellFormedTy ct S)
    (huf : S.unionFree) :
    DecisionCleanSourceCase (ct := ct) (S := S) hwfct hwfS := by
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
          let w := summarizeInterAtoms_leafConflict_witness' (ct := ct) (atoms := atoms) hwfct hleafconf'
          exact .empty <| .trans
            (.interIntro (hproj w.hmemB) (hproj w.hmemC))
            (leaf_conflict_bottom
              (ct := ct) (B := w.B) (C := w.C) hwfct w.hleafB w.hleafC w.hne)
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
                          let hleafInfo := summarizeInterAtoms_leafAtom_mem
                            (ct := ct) (B := B) (atoms := atoms) hwfct hleafAtom'
                          let wB := leafBuiltinLookup (ct := ct) (B := B) hwfct hleafInfo.2
                          cases hnonleafOff : firstOutside summary.nonleafClassAtoms wB.mro with
                          | some C =>
                              let hCsome := firstOutside_some hnonleafOff
                              let hCinfo := summarizeInterAtoms_nonleaf_atom_mem
                                (ct := ct) (C := C) (atoms := atoms) hwfct
                                (by simpa [hsummary] using hCsome.1)
                              exact .empty <| .trans
                                (.interIntro (hproj hCinfo.1) (hproj hleafInfo.1))
                                (leaf_inter_class_outside_bottom
                                  (ct := ct) (B := B) (C := C) hleafInfo.2 wB.hfind wB.hmro hCsome.2)
                          | none =>
                              have hnonleafClear :
                                  ∀ C, C ∈ summary.nonleafClassAtoms → C ∈ wB.mro :=
                                firstOutside_none hnonleafOff
                              cases hnegOff : firstInside summary.negAtoms wB.mro with
                              | some E =>
                                  let hEsome := firstInside_some hnegOff
                                  have hmemE : .negClass E ∈ atoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                      (by simpa [hsummary] using hEsome.1)
                                  exact .empty <| .trans
                                    (.interIntro (hproj hleafInfo.1) (hproj hmemE))
                                    (classNegClassBottom
                                      (.class_ wB.hfind wB.hmro hEsome.2))
                              | none =>
                                  have hnegClear :
                                      ∀ E, E ∈ summary.negAtoms → E ∉ wB.mro :=
                                    firstInside_none hnegOff
                                  have hclassMem : ∀ D, .class_ D ∈ atoms → D ∈ wB.mro := by
                                    intro D hmemD
                                    cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                    | isTrue hleafD =>
                                        have hDB := leafAtom_eq_of_mem
                                          (ct := ct) (B := B) (D := D) (atoms := atoms)
                                          hwfct hleafconf' hleafAtom' hleafD hmemD
                                        subst D
                                        simpa [findClass_name wB.hfind] using mro_self_mem wB.hmro
                                    | isFalse hnonleafD =>
                                        have hDmemList : D ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms :=
                                          (summarizeInterAtoms_nonleaf_mem_iff
                                            (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                        exact hnonleafClear D (by simpa [hsummary] using hDmemList)
                                  have hnegNotMem : ∀ E, .negClass E ∈ atoms → E ∉ wB.mro := by
                                    intro E hmemE
                                    have hEmemList : E ∈ (summarizeInterAtoms hwfct atoms).negAtoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
                                    exact hnegClear E (by simpa [hsummary] using hEmemList)
                                  exact mkDecisionCurrentFromLeaf
                                    (ct := ct) (S := S) hwfct hwfS huf hbot' hcall' wB hleafInfo.2
                                    (hproj hleafInfo.1)
                                    (by simpa [hatoms] using hclassMem)
                                    (by simpa [hatoms] using hnegNotMem)
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
                                let seedSource : ∀ s, s ∈ [objectClass] → SeedSourceWitness S s := fun s hs => by
                                  simp at hs
                                  subst hs
                                  exact .object rfl
                                have hclassDenotes : ∀ D, .class_ D ∈ atoms →
                                    Ty.semDenotes ct (.class_ D)
                                      (freshSeedsObj (ct := ct)
                                        [objectClass] (by simp) (by simp) seedWitness seed_nonleaf) := by
                                  intro D hmemD
                                  cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                  | isTrue hleafD =>
                                      exact False.elim <|
                                        no_leaf_atom_of_none
                                          (hwfct := hwfct) (atoms := atoms) (D := D)
                                          hleafconf' hleafAtom' hleafD hmemD
                                  | isFalse hnonleafD =>
                                      have hDmemList : D ∈ (summarizeInterAtoms hwfct atoms).nonleafClassAtoms :=
                                        (summarizeInterAtoms_nonleaf_mem_iff
                                          (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                      rw [hseeds'] at hDmemList
                                      cases hDmemList
                                have hnegDenotes : ∀ E, .negClass E ∈ atoms →
                                    Ty.semDenotes ct (.negClass E)
                                      (freshSeedsObj (ct := ct)
                                        [objectClass] (by simp) (by simp) seedWitness seed_nonleaf) := by
                                  intro E hmemE
                                  have hEmemList : E ∈ (summarizeInterAtoms hwfct atoms).negAtoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
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
                                exact mkDecisionFreshFromSeeds
                                  (ct := ct) (S := S) hwfct hwfS huf hbot' hcall'
                                  [objectClass] (by simp) (by simp) seedWitness seed_nonleaf seedSource
                                  hclassDenotes hnegDenotes
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
                                simpa [seeds, hsummary] using
                                  cleanSourceSeedWitness
                                    (ct := ct) (S := S) hwfct hwfS huf s hs
                              let seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s := fun s hs => by
                                simpa [seeds, hsummary] using
                                  cleanSourceSeed_nonleaf
                                    (ct := ct) (S := S) (s := s) hwfct hs
                              let seedSource : ∀ s, s ∈ seeds → SeedSourceWitness S s := fun s hs =>
                                .source <|
                                  (summarizeInterAtoms_nonleaf_atom_mem
                                    (ct := ct) (C := s) (atoms := atoms) hwfct
                                    (by simpa [seeds, hsummary] using hs)).1
                              cases seeds_neg_conflict_or_clear' (ct := ct) seeds summary.negAtoms seedWitness with
                              | conflict hconf =>
                                  let hseedInfo := summarizeInterAtoms_nonleaf_atom_mem
                                    (ct := ct) (C := hconf.s) (atoms := atoms) hwfct
                                    (by simpa [seeds, hsummary] using hconf.hs)
                                  have hmemE : .negClass hconf.E ∈ atoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := hconf.E)).1
                                      (by simpa [hsummary] using hconf.hmem)
                                  let info := seedWitness hconf.s hconf.hs
                                  exact .empty <| .trans
                                    (.interIntro (hproj hseedInfo.1) (hproj hmemE))
                                    (classNegClassBottom
                                      (.class_ info.hfind info.hmro hconf.hIn))
                              | clear hclear =>
                                  have hclassDenotes : ∀ D, .class_ D ∈ atoms →
                                      Ty.semDenotes ct (.class_ D)
                                        (freshSeedsObj (ct := ct)
                                          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
                                    intro D hmemD
                                    cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                    | isTrue hleafD =>
                                        exact False.elim <|
                                          no_leaf_atom_of_none
                                            (hwfct := hwfct) (atoms := atoms) (D := D)
                                            hleafconf' hleafAtom' hleafD hmemD
                                    | isFalse hnonleafD =>
                                        have hDmemSeeds : D ∈ seeds :=
                                          (summarizeInterAtoms_nonleaf_mem_iff
                                            (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                        have hself : D ∈ (seedWitness D hDmemSeeds).mro := by
                                          simpa [findClass_name (seedWitness D hDmemSeeds).hfind] using
                                            mro_self_mem (seedWitness D hDmemSeeds).hmro
                                        exact (freshSeedsObj_denotes_class_iff
                                          (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup
                                          seedWitness seed_nonleaf).2
                                          ⟨D, hDmemSeeds, hself⟩
                                  have hnegDenotes : ∀ E, .negClass E ∈ atoms →
                                      Ty.semDenotes ct (.negClass E)
                                        (freshSeedsObj (ct := ct)
                                          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) := by
                                    intro E hmemE
                                    have hEmemList : E ∈ summary.negAtoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
                                    exact (freshSeedsObj_denotes_neg_iff
                                      (ct := ct) (C := E) seeds hseeds_ne hseeds_nodup
                                      seedWitness seed_nonleaf).2 <| by
                                        intro hex
                                        rcases hex with ⟨s, hs, hEin⟩
                                        exact hclear s hs E hEmemList hEin
                                  exact mkDecisionFreshFromSeeds
                                    (ct := ct) (S := S) hwfct hwfS huf hbot' hcall'
                                    seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource
                                    hclassDenotes hnegDenotes
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
                  have hwfPsum : WellFormedTy ct Psum := by
                    refine callableParamsUnion_wellFormed (ct := ct) (callAtoms := summary.callableAtoms) ?_
                    intro pr hpr
                    have hmemPr : callableAtomTy pr ∈ atoms :=
                      (summarizeInterAtoms_callable_mem_iff
                        (hwfct := hwfct) (atoms := atoms) (pr := pr)).1 <|
                        by simpa [hsummary] using hpr
                    exact (hwfAtom hmemPr).callable_param
                  have hwfRsum : WellFormedTy ct Rsum := by
                    refine callableReturnsInter_wellFormed
                      (ct := ct) (callAtoms := summary.callableAtoms) hwfct ?_
                    intro pr hpr
                    have hmemPr : callableAtomTy pr ∈ atoms :=
                      (summarizeInterAtoms_callable_mem_iff
                        (hwfct := hwfct) (atoms := atoms) (pr := pr)).1 <|
                        by simpa [hsummary] using hpr
                    exact (hwfAtom hmemPr).callable_return
                  have hsizes := callableSummary_sizes_le_source (ct := ct) hwfct S
                  have hPsumSize : Psum.size ≤ S.size := by simpa [Psum, hsummary] using hsizes.1
                  have hRsumSize : Rsum.size ≤ S.size := by simpa [Rsum, hsummary] using hsizes.2
                  have hcallDenotes : ∀ P R, .callable P R ∈ atoms →
                      Ty.semDenotes ct (.callable P R)
                        (boundMethodObj (ct := ct) hwfct Psum Rsum) := by
                    intro P R hmemA
                    have hpair : (P, R) ∈ summary.callableAtoms :=
                      (summarizeInterAtoms_callable_mem_iff
                        (hwfct := hwfct) (atoms := atoms) (pr := (P, R))).2 hmemA
                    simpa [Psum, Rsum] using
                      boundMethodObj_denotes_callable_of_mem
                        (ct := ct) (pr := (P, R))
                        (callAtoms := summary.callableAtoms) hwfct hpair
                  cases hleafAtom : summary.leafClassAtom with
                      | some B =>
                          have hleafAtom' :
                              (summarizeInterAtoms hwfct atoms).leafClassAtom = some B := by
                            simpa [hsummary] using hleafAtom
                          let hleafInfo := summarizeInterAtoms_leafAtom_mem
                            (ct := ct) (B := B) (atoms := atoms) hwfct hleafAtom'
                          by_cases hBmem : B ∈ hwfct.boundMethodExists.mro
                          · cases hnonleafOff : firstOutside summary.nonleafClassAtoms hwfct.boundMethodExists.mro with
                            | some D =>
                                let hDsome := firstOutside_some hnonleafOff
                                let hDinfo := summarizeInterAtoms_nonleaf_atom_mem
                                  (ct := ct) (C := D) (atoms := atoms) hwfct
                                  (by simpa [hsummary] using hDsome.1)
                                exact .empty <| .trans
                                  (.interIntro (hproj hDinfo.1) hcallSub)
                                  (leaf_class_callable_bottom
                                    (ct := ct) (C := D) (P := Psum) (R := Rsum)
                                    (leafBuiltin_boundMethod hwfct)
                                    hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro
                                    hDsome.2)
                            | none =>
                                have hnonleafClear :
                                    ∀ D, D ∈ summary.nonleafClassAtoms → D ∈ hwfct.boundMethodExists.mro :=
                                  firstOutside_none hnonleafOff
                                cases hnegOff : firstInside summary.negAtoms hwfct.boundMethodExists.mro with
                                | some E =>
                                    let hEsome := firstInside_some hnegOff
                                    have hmemE : .negClass E ∈ atoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                        (by simpa [hsummary] using hEsome.1)
                                    have hclassE : IsSubtype ct S (.class_ E) := by
                                      exact .trans hcallSub <| .trans
                                        (callable_to_class (ct := ct) (P := Psum) (R := Rsum) hwfct)
                                        (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hEsome.2)
                                    exact .empty <| .trans
                                      (.interIntro hclassE (hproj hmemE))
                                      .classSelfNegClassBottom
                                | none =>
                                    have hnegClear :
                                        ∀ E, E ∈ summary.negAtoms → E ∉ hwfct.boundMethodExists.mro :=
                                      firstInside_none hnegOff
                                    have hclassMem : ∀ D, .class_ D ∈ atoms → D ∈ hwfct.boundMethodExists.mro := by
                                      intro D hmemD
                                      cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                      | isTrue hleafD =>
                                          have hDB := leafAtom_eq_of_mem
                                            (ct := ct) (B := B) (D := D) (atoms := atoms)
                                            hwfct hleafconf' hleafAtom' hleafD hmemD
                                          subst D
                                          exact hBmem
                                      | isFalse hnonleafD =>
                                          have hDmemList : D ∈ summary.nonleafClassAtoms :=
                                            (summarizeInterAtoms_nonleaf_mem_iff
                                              (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                          exact hnonleafClear D hDmemList
                                    have hnegNotMem : ∀ E, .negClass E ∈ atoms → E ∉ hwfct.boundMethodExists.mro := by
                                      intro E hmemE
                                      have hEmemList : E ∈ summary.negAtoms :=
                                        (summarizeInterAtoms_neg_mem_iff
                                          (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
                                      exact hnegClear E hEmemList
                                    exact mkDecisionBoundMethodFromCallables
                                      (ct := ct) (S := S) hwfct hwfS huf hbot'
                                      Psum Rsum hwfPsum hwfRsum hPsumSize hRsumSize hcallSub
                                      (by simpa [hatoms] using hclassMem)
                                      (by simpa [hatoms] using hnegNotMem)
                                      (by simpa [hatoms] using hcallDenotes)
                          · exact .empty <| .trans
                              (.interIntro (hproj hleafInfo.1) hcallSub)
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
                              let hDsome := firstOutside_some hnonleafOff
                              let hDinfo := summarizeInterAtoms_nonleaf_atom_mem
                                (ct := ct) (C := D) (atoms := atoms) hwfct
                                (by simpa [hsummary] using hDsome.1)
                              exact .empty <| .trans
                                (.interIntro (hproj hDinfo.1) hcallSub)
                                (leaf_class_callable_bottom
                                  (ct := ct) (C := D) (P := Psum) (R := Rsum)
                                  (leafBuiltin_boundMethod hwfct)
                                  hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro
                                  hDsome.2)
                          | none =>
                              have hnonleafClear :
                                  ∀ D, D ∈ summary.nonleafClassAtoms → D ∈ hwfct.boundMethodExists.mro :=
                                firstOutside_none hnonleafOff
                              cases hnegOff : firstInside summary.negAtoms hwfct.boundMethodExists.mro with
                              | some E =>
                                  let hEsome := firstInside_some hnegOff
                                  have hmemE : .negClass E ∈ atoms :=
                                    (summarizeInterAtoms_neg_mem_iff
                                      (hwfct := hwfct) (atoms := atoms) (C := E)).1
                                      (by simpa [hsummary] using hEsome.1)
                                  have hclassE : IsSubtype ct S (.class_ E) := by
                                    exact .trans hcallSub <| .trans
                                      (callable_to_class (ct := ct) (P := Psum) (R := Rsum) hwfct)
                                      (.class_ hwfct.boundMethodExists.hfind hwfct.boundMethodExists.hmro hEsome.2)
                                  exact .empty <| .trans
                                    (.interIntro hclassE (hproj hmemE))
                                    .classSelfNegClassBottom
                              | none =>
                                  have hnegClear :
                                      ∀ E, E ∈ summary.negAtoms → E ∉ hwfct.boundMethodExists.mro :=
                                    firstInside_none hnegOff
                                  have hclassMem : ∀ D, .class_ D ∈ atoms → D ∈ hwfct.boundMethodExists.mro := by
                                    intro D hmemD
                                    cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
                                    | isTrue hleafD =>
                                        exact False.elim <|
                                          no_leaf_atom_of_none
                                            (hwfct := hwfct) (atoms := atoms) (D := D)
                                            hleafconf' hleafAtom' hleafD hmemD
                                    | isFalse hnonleafD =>
                                        have hDmemList : D ∈ summary.nonleafClassAtoms :=
                                          (summarizeInterAtoms_nonleaf_mem_iff
                                            (ct := ct) (C := D) (atoms := atoms) hwfct hnonleafD).2 hmemD
                                        exact hnonleafClear D hDmemList
                                  have hnegNotMem : ∀ E, .negClass E ∈ atoms → E ∉ hwfct.boundMethodExists.mro := by
                                    intro E hmemE
                                    have hEmemList : E ∈ summary.negAtoms :=
                                      (summarizeInterAtoms_neg_mem_iff
                                        (hwfct := hwfct) (atoms := atoms) (C := E)).2 hmemE
                                    exact hnegClear E hEmemList
                                  exact mkDecisionBoundMethodFromCallables
                                    (ct := ct) (S := S) hwfct hwfS huf hbot'
                                    Psum Rsum hwfPsum hwfRsum hPsumSize hRsumSize hcallSub
                                    (by simpa [hatoms] using hclassMem)
                                    (by simpa [hatoms] using hnegNotMem)
                                    (by simpa [hatoms] using hcallDenotes)

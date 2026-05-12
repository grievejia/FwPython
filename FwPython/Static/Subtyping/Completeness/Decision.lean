import FwPython.Static.Subtyping.Completeness.DecisionHelpers

private inductive SubtypeDecision (ct : ClassTable) (T U : Ty) : Type where
  | yes : IsSubtype ct T U → SubtypeDecision ct T U
  | no :
      (obj : SemObject ct) →
      Ty.semDenotes ct T obj →
      ¬ Ty.semDenotes ct U obj →
      SubtypeDecision ct T U

namespace SubtypeDecision

theorem no_notSemSubtype
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    ¬ SemSubtype ct T U := by
  intro hsem
  exact hnotU (hsem obj hT)

theorem no_notIsSubtype
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    ¬ IsSubtype ct T U := by
  intro hsub
  exact no_notSemSubtype obj hT hnotU (semSubtype_sound hsub)

def toDecidableIsSubtype : SubtypeDecision ct T U → Decidable (IsSubtype ct T U)
  | .yes hsub => isTrue hsub
  | .no obj hT hnotU => isFalse <| no_notIsSubtype obj hT hnotU

def ofRetract
    (hsub : IsSubtype ct S A)
    (hrev : IsSubtype ct A S) :
    SubtypeDecision ct A U → SubtypeDecision ct S U
  | .yes hAU =>
      .yes (.trans hsub hAU)
  | .no obj hA hnotU =>
      .no obj ((semSubtype_sound hrev) obj hA) hnotU

def no_ofSourceSubtype
    (hAS : IsSubtype ct A S)
    (obj : SemObject ct)
    (hA : Ty.semDenotes ct A obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct S U :=
  .no obj ((semSubtype_sound hAS) obj hA) hnotU

def no_union_left
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct (.union T V) U :=
  no_ofSourceSubtype (.unionLeft IsSubtype.refl) obj hT hnotU

def no_union_right
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct (.union V T) U :=
  no_ofSourceSubtype (.unionRight IsSubtype.refl) obj hT hnotU

def no_intersection_left
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct T (.intersection U V) :=
  .no obj hT (fun hden => hnotU hden.1)

def no_intersection_right
    (obj : SemObject ct)
    (hT : Ty.semDenotes ct T obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct T (.intersection V U) :=
  .no obj hT (fun hden => hnotU hden.2)

def no_negClass_union_of_inter_class
    (obj : SemObject ct)
    (hSR : Ty.semDenotes ct (.intersection S (.class_ B)) obj)
    (hnotR : ¬ Ty.semDenotes ct R obj) :
    SubtypeDecision ct S (.union (.negClass B) R) :=
  .no obj hSR.1 (fun hden => hden.elim (fun hneg => hneg hSR.2) hnotR)

def no_class_union_of_inter_neg
    (obj : SemObject ct)
    (hSR : Ty.semDenotes ct (.intersection S (.negClass D)) obj)
    (hnotR : ¬ Ty.semDenotes ct R obj) :
    SubtypeDecision ct S (.union (.class_ D) R) :=
  .no obj hSR.1 (fun hden => hden.elim hSR.2 hnotR)

def no_union_intersection_left
    (obj : SemObject ct)
    (hS : Ty.semDenotes ct S obj)
    (hnot : ¬ Ty.semDenotes ct (.union A₁ R) obj) :
    SubtypeDecision ct S (.union (.intersection A₁ A₂) R) :=
  .no obj hS <| fun hden =>
    hden.elim (fun hint => hnot (Or.inl hint.1)) (fun hR => hnot (Or.inr hR))

def no_union_intersection_right
    (obj : SemObject ct)
    (hS : Ty.semDenotes ct S obj)
    (hnot : ¬ Ty.semDenotes ct (.union A₂ R) obj) :
    SubtypeDecision ct S (.union (.intersection A₁ A₂) R) :=
  .no obj hS <| fun hden =>
    hden.elim (fun hint => hnot (Or.inl hint.2)) (fun hR => hnot (Or.inr hR))

def no_split_left
    (split : SourceUnionSplit T)
    (obj : SemObject ct)
    (hleft : Ty.semDenotes ct split.left obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct T U :=
  no_ofSourceSubtype
    (.trans (.unionLeft IsSubtype.refl) split.fromUnion)
    obj hleft hnotU

def no_split_right
    (split : SourceUnionSplit T)
    (obj : SemObject ct)
    (hright : Ty.semDenotes ct split.right obj)
    (hnotU : ¬ Ty.semDenotes ct U obj) :
    SubtypeDecision ct T U :=
  no_ofSourceSubtype
    (.trans (.unionRight IsSubtype.refl) split.fromUnion)
    obj hright hnotU

end SubtypeDecision

private theorem subtype_union_intersection_combine
    (h₁ : IsSubtype ct S (.union A₁ R))
    (h₂ : IsSubtype ct S (.union A₂ R)) :
    IsSubtype ct S (.union (.intersection A₁ A₂) R) := by
  exact .trans
    (.interIntro
      (.trans h₁ subtype_union_comm)
      (.trans h₂ subtype_union_comm))
    (.trans subtype_inter_union_distrib' subtype_union_comm)

private theorem negObject_subtype_any
    (hwfct : WellFormedClassTable ct) :
    IsSubtype ct (.negClass objectClass) U := by
  exact .trans
    (negClass_bottom_of_objectSubtype
      (ct := ct) (C := objectClass) hwfct IsSubtype.refl)
    .bottom

private def decideCurrentDenotes
    (hfind : findClass ct C = some cls)
    (hmro : ComputeMro ct cls mro) :
    (U : Ty) → Decidable (Ty.semDenotes ct U (currentObjOf (ct := ct) C hfind hmro))
  | .bottom =>
      isFalse (by simp [Ty.semDenotes])
  | .class_ D =>
      match inferInstanceAs (Decidable (D ∈ mro)) with
      | isTrue hmem =>
          isTrue ((currentObjOf_denotes_class
            (ct := ct) (C := C) (D := D) hfind hmro).2 hmem)
      | isFalse hnot =>
          isFalse (by
            intro hden
            exact hnot ((currentObjOf_denotes_class
              (ct := ct) (C := C) (D := D) hfind hmro).1 hden))
  | .negClass D =>
      match inferInstanceAs (Decidable (D ∈ mro)) with
      | isTrue hmem =>
          isFalse (by
            intro hden
            exact ((currentObjOf_denotes_neg_iff
              (ct := ct) (C := C) (D := D) hfind hmro).1 hden) hmem)
      | isFalse hnot =>
          isTrue ((currentObjOf_denotes_neg_iff
            (ct := ct) (C := C) (D := D) hfind hmro).2 hnot)
  | .callable P R =>
      isFalse (currentObjOf_not_denotes_callable
        (ct := ct) (C := C) (P := P) (R := R) hfind hmro)
  | .union U V =>
      match decideCurrentDenotes hfind hmro U, decideCurrentDenotes hfind hmro V with
      | isTrue hU, _ => isTrue (Or.inl hU)
      | _, isTrue hV => isTrue (Or.inr hV)
      | isFalse hU, isFalse hV =>
          isFalse (by
            intro hden
            rcases hden with hU' | hV'
            · exact hU hU'
            · exact hV hV')
  | .intersection U V =>
      match decideCurrentDenotes hfind hmro U, decideCurrentDenotes hfind hmro V with
      | isTrue hU, isTrue hV => isTrue ⟨hU, hV⟩
      | isFalse hU, _ =>
          isFalse (by
            intro hden
            exact hU hden.1)
      | _, isFalse hV =>
          isFalse (by
            intro hden
            exact hV hden.2)

private def findWitnessList
    (ts : List α)
    (P : α → Prop)
    (decP : ∀ t, Decidable (P t)) :
    Option {t : α // P t} :=
  match ts with
  | [] => none
  | t :: ts =>
      match decP t with
      | isTrue hP => some ⟨t, hP⟩
      | isFalse _ => findWitnessList ts P decP

private theorem findWitnessList_eq_none_imp_forall_not
    (ts : List α)
    (P : α → Prop)
    (decP : ∀ t, Decidable (P t))
    (hnone : findWitnessList ts P decP = none) :
    ∀ t, t ∈ ts → ¬ P t := by
  induction ts with
  | nil =>
      intro t ht
      cases ht
  | cons t ts ih =>
      unfold findWitnessList at hnone
      cases hdec : decP t with
      | isTrue hP =>
          simp [hdec] at hnone
      | isFalse hP =>
          simp [hdec] at hnone
          intro t' ht'
          rcases List.mem_cons.mp ht' with rfl | ht'
          · exact hP
          · exact ih hnone t' ht'

private def findSeedWitness
    {seeds : List Identifier}
    (P : {s // s ∈ seeds} → Prop)
    (decP : ∀ t, Decidable (P t)) :
    Option {t : {s // s ∈ seeds} // P t} :=
  findWitnessList seeds.attach P decP

private theorem findSeedWitness_eq_none_imp_forall_not
    {seeds : List Identifier}
    (P : {s // s ∈ seeds} → Prop)
    (decP : ∀ t, Decidable (P t))
    (hnone : findSeedWitness (seeds := seeds) P decP = none) :
    ∀ t, ¬ P t := by
  have hgo : ∀ t, t ∈ seeds.attach → ¬ P t := by
    simpa [findSeedWitness] using
      findWitnessList_eq_none_imp_forall_not seeds.attach P decP hnone
  intro t
  exact hgo t (by simp)

private theorem boundMethodObj_denotes_callable_iff
    (hwfct : WellFormedClassTable ct) :
    Ty.semDenotes ct (.callable P' R')
      (boundMethodObj (ct := ct) hwfct Psum Rsum) ↔
      IsSubtype ct P' Psum ∧ IsSubtype ct Rsum R' := by
  simp [boundMethodObj, Ty.semDenotes]

private theorem fresh_to_current_denotes
    (hwfct : WellFormedClassTable ct)
    (huf : S.unionFree)
    (wD : ClassLookupWitness ct D)
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (holdAtom : ∀ A, A ∈ S.interAtoms →
      Ty.semDenotes ct A
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf))
    (hnegClear :
      ∀ E, E ∈ (summarizeInterAtoms hwfct S.interAtoms).negAtoms → E ∉ wD.mro)
    (hseedAll : ∀ s, s ∈ seeds → s ∈ wD.mro) :
    Ty.semDenotes ct S (currentObjOf (ct := ct) D wD.hfind wD.hmro) := by
  have hclassMem : ∀ C, .class_ C ∈ S.interAtoms → C ∈ wD.mro := by
    intro C hmemC
    have holdC :
        Ty.semDenotes ct (.class_ C)
          (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) :=
      holdAtom (.class_ C) hmemC
    rcases (freshSeedsObj_denotes_class_iff
      (ct := ct) (C := C) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1 holdC with
      ⟨s, hs, hCmem⟩
    let info := seedWitness s hs
    have hsIn : s ∈ wD.mro := hseedAll s hs
    have hsIn' : info.cls.name ∈ wD.mro := by
      simpa [findClass_name info.hfind] using hsIn
    have hfindDname : findClass ct wD.cls.name = some wD.cls := by
      simpa [findClass_name wD.hfind] using wD.hfind
    have hfindInfo : findClass ct info.cls.name = some info.cls := by
      simpa [findClass_name info.hfind] using info.hfind
    exact mro_mem_trans ct wD.cls info.cls wD.mro info.mro C
      hfindDname wD.hmro hfindInfo info.hmro hsIn' hCmem
  refine semDenotes_source_of_atoms
    (ct := ct) (S := S)
    (obj := currentObjOf (ct := ct) D wD.hfind wD.hmro) huf ?_
  intro A hmemA
  cases A with
  | bottom =>
      exact False.elim (holdAtom .bottom hmemA)
  | class_ C =>
      exact (currentObjOf_denotes_class
        (ct := ct) (C := D) (D := C) wD.hfind wD.hmro).2
        (hclassMem C hmemA)
  | negClass E =>
      have hEmemList :
          E ∈ (summarizeInterAtoms hwfct S.interAtoms).negAtoms :=
        (summarizeInterAtoms_neg_mem_iff
          (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).2 hmemA
      exact (currentObjOf_denotes_neg_iff
        (ct := ct) (C := D) (D := E) wD.hfind wD.hmro).2
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

private theorem fresh_extend_denotes
    (hwfct : WellFormedClassTable ct)
    (huf : S.unionFree)
    (wD : ClassLookupWitness ct D)
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (holdAtom : ∀ A, A ∈ S.interAtoms →
      Ty.semDenotes ct A
        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf))
    (hnegClear :
      ∀ E, E ∈ (summarizeInterAtoms hwfct S.interAtoms).negAtoms → E ∉ wD.mro)
    (hDseed : D ∉ seeds)
    (hnonleafD : ¬ LeafBuiltin ct D) :
    Ty.semDenotes ct S
      (freshSeedsObj (ct := ct)
        (D :: seeds)
        (by simp)
        (by simp [hDseed, hseeds_nodup])
        (fun s hs => by
          by_cases hEq : s = D
          · subst hEq
            exact ⟨wD.cls, wD.mro, wD.hfind, wD.hmro⟩
          · exact seedWitness s (by simpa [hEq] using hs))
        (fun s hs => by
          by_cases hEq : s = D
          · subst hEq
            exact hnonleafD
          · exact seed_nonleaf s (by simpa [hEq] using hs))) := by
  let newSeeds : List Identifier := D :: seeds
  let newSeedWitness : ∀ s, s ∈ newSeeds → FreshSeedInfo ct s := fun s hs => by
    by_cases hEq : s = D
    · subst hEq
      exact ⟨wD.cls, wD.mro, wD.hfind, wD.hmro⟩
    · exact seedWitness s (by simpa [newSeeds, hEq] using hs)
  let newSeedNonleaf : ∀ s, s ∈ newSeeds → ¬ LeafBuiltin ct s := fun s hs => by
    by_cases hEq : s = D
    · subst hEq
      exact hnonleafD
    · exact seed_nonleaf s (by simpa [newSeeds, hEq] using hs)
  have hnew_ne : newSeeds ≠ [] := by
    simp [newSeeds]
  have hnew_nodup : newSeeds.Nodup := by
    simp [newSeeds, hDseed, hseeds_nodup]
  refine semDenotes_source_of_atoms
    (ct := ct) (S := S)
    (obj := freshSeedsObj (ct := ct)
      newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf) huf ?_
  intro A hmemA
  cases A with
  | bottom =>
      exact False.elim (holdAtom .bottom hmemA)
  | class_ C =>
      have holdC :
          Ty.semDenotes ct (.class_ C)
            (freshSeedsObj (ct := ct)
              seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) :=
        holdAtom (.class_ C) hmemA
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
      have hnegOldE :
          Ty.semDenotes ct (.negClass E)
            (freshSeedsObj (ct := ct)
              seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf) :=
        holdAtom (.negClass E) hmemA
      have hEmemList :
          E ∈ (summarizeInterAtoms hwfct S.interAtoms).negAtoms :=
        (summarizeInterAtoms_neg_mem_iff
          (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).2 hmemA
      exact (freshSeedsObj_denotes_neg_iff
        (ct := ct) (C := E) newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf).2 <|
          by
          intro hanc
          rcases hanc with ⟨s, hs, hEanc⟩
          by_cases hEq : s = D
          · subst hEq
            have hEmro : E ∈ wD.mro := by
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

private inductive DecisionGoal (ct : ClassTable) : Type where
  | subtype :
      (T U : Ty) →
      WellFormedTy ct T →
      WellFormedTy ct U →
      DecisionGoal ct
  | boundMethodDenotes :
      (budget : Nat) →
      (Psum Rsum U : Ty) →
      WellFormedTy ct Psum →
      WellFormedTy ct Rsum →
      WellFormedTy ct U →
      Psum.size ≤ budget →
      Rsum.size ≤ budget →
      DecisionGoal ct

private def DecisionGoal.Result
    (hwfct : WellFormedClassTable ct) :
    DecisionGoal ct → Type
  | .subtype T U _ _ =>
      SubtypeDecision ct T U
  | .boundMethodDenotes _ Psum Rsum U _ _ _ _ _ =>
      Decidable (Ty.semDenotes ct U (boundMethodObj (ct := ct) hwfct Psum Rsum))

private abbrev GoalMeasure := Nat × (Nat × Nat)

private def goalMeasure : DecisionGoal ct → GoalMeasure
  | .subtype T U _ _ =>
      (T.size + U.size, (U.size, 1))
  | .boundMethodDenotes budget _ _ U _ _ _ _ _ =>
      (budget + U.size, (U.size, 0))

private theorem goalMeasure_rel_first
    {a₁ a₂ b₁ b₂ c₁ c₂ : Nat}
    (h : a₁ < a₂) :
    WellFoundedRelation.rel (α := GoalMeasure)
      (a₁, (b₁, c₁))
      (a₂, (b₂, c₂)) :=
  Prod.Lex.left _ _ h

private theorem goalMeasure_rel_second
    {a b₁ b₂ c₁ c₂ : Nat}
    (h : b₁ < b₂) :
    WellFoundedRelation.rel (α := GoalMeasure)
      (a, (b₁, c₁))
      (a, (b₂, c₂)) :=
  Prod.Lex.right a (Prod.Lex.left _ _ h)

private theorem goalMeasure_rel_third
    {a b c₁ c₂ : Nat}
    (h : c₁ < c₂) :
    WellFoundedRelation.rel (α := GoalMeasure)
      (a, (b, c₁))
      (a, (b, c₂)) :=
  Prod.Lex.right a (Prod.Lex.right b h)

private def freshClassDecision
    (hwfct : WellFormedClassTable ct)
    (_hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (D : Identifier)
    (hD : D ≠ objectClass)
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (seedSource : ∀ s, s ∈ seeds → SeedSourceWitness S s)
    (hdenS : Ty.semDenotes ct S
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
    SubtypeDecision ct S (.class_ D) := by
  let oldW :=
    freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
  let hit := findSeedWitness (seeds := seeds)
    (fun t : {s // s ∈ seeds} => D ∈ (seedWitness t.1 t.2).mro)
    (fun t => inferInstanceAs (Decidable (D ∈ (seedWitness t.1 t.2).mro)))
  cases hhit : hit with
  | none =>
      have hall :
          ∀ t : {s // s ∈ seeds}, ¬ D ∈ (seedWitness t.1 t.2).mro :=
        findSeedWitness_eq_none_imp_forall_not
          (seeds := seeds)
          (P := fun t : {s // s ∈ seeds} => D ∈ (seedWitness t.1 t.2).mro)
          (decP := fun t => inferInstanceAs (Decidable (D ∈ (seedWitness t.1 t.2).mro)))
          hhit
      have hnotU : ¬ Ty.semDenotes ct (.class_ D) oldW := by
        intro hclass
        rcases (freshSeedsObj_denotes_class_iff
          (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf).1 hclass with
          ⟨s, hs, hmemD⟩
        exact hall ⟨s, hs⟩ hmemD
      exact .no oldW hdenS hnotU
  | some val =>
      rcases val with ⟨⟨s, hs⟩, hmemD⟩
      cases seedSource s hs with
      | object hsObj =>
          subst s
          have hmroObj :
              (seedWitness objectClass hs).mro = [objectClass] :=
            freshSeedInfo_object_mro
              (ct := ct) hwfct (seedWitness objectClass hs)
          have : D = objectClass := by
            simpa [hmroObj] using hmemD
          exact False.elim (hD this)
      | source hmemS =>
          let info := seedWitness s hs
          exact .yes <|
            .trans
              (interAtoms_projection (ct := ct) (T := S) (A := .class_ s) huf hmemS)
              (.class_ info.hfind info.hmro hmemD)

private def freshCallableDecision
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (hdenS : Ty.semDenotes ct S
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
    SubtypeDecision ct S (.callable P R) :=
  .no _ hdenS <|
    freshSeedsObj_not_denotes_callable (ct := ct) (P := P) (R := R)
      seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf

private def freshNegDecision
    (hwfct : WellFormedClassTable ct)
    (huf : S.unionFree)
    (hwfU : WellFormedTy ct (.negClass D))
    (seeds : List Identifier)
    (hseeds_ne : seeds ≠ [])
    (hseeds_nodup : seeds.Nodup)
    (seedWitness : ∀ s, s ∈ seeds → FreshSeedInfo ct s)
    (seed_nonleaf : ∀ s, s ∈ seeds → ¬ LeafBuiltin ct s)
    (seedSource : ∀ s, s ∈ seeds → SeedSourceWitness S s)
    (hdenS : Ty.semDenotes ct S
      (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)) :
    SubtypeDecision ct S (.negClass D) := by
  let oldW :=
    freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
  have holdAtom : ∀ A, A ∈ S.interAtoms → Ty.semDenotes ct A oldW := by
    intro A hmemA
    exact semDenotes_at_obj_sound
      (ct := ct)
      (obj := oldW)
      (interAtoms_projection (ct := ct) (T := S) (A := A) huf hmemA)
      hdenS
  let negAtoms := (summarizeInterAtoms hwfct S.interAtoms).negAtoms
  let wD := wfNegLookup hwfct hwfU
  cases hnegHit : firstInside negAtoms wD.mro with
  | some E =>
      rcases firstInside_some hnegHit with ⟨hEmemList, hEmem⟩
      have hmemE : .negClass E ∈ S.interAtoms :=
        (summarizeInterAtoms_neg_mem_iff
          (hwfct := hwfct) (atoms := S.interAtoms) (C := E)).1 hEmemList
      exact .yes <|
        .trans
          (interAtoms_projection (ct := ct) (T := S) (A := .negClass E) huf hmemE)
          (negClassAntitone
            (.class_ wD.hfind wD.hmro hEmem))
  | none =>
      have hnegClear :
          ∀ E, E ∈ negAtoms → E ∉ wD.mro :=
        firstInside_none hnegHit
      cases hdec : builtinLeafDecidable (ct := ct) (C := D) hwfct with
      | isTrue hleafD =>
          cases hseedOff : firstOutside seeds wD.mro with
          | some s =>
              rcases firstOutside_some hseedOff with ⟨hs, hsOut⟩
              cases seedSource s hs with
              | object hsObj =>
                  have hobj : objectClass ∈ wD.mro := mro_contains_object wD.hmro
                  have : s ∈ wD.mro := by
                    simpa [hsObj] using hobj
                  exact False.elim (hsOut this)
              | source hmemS =>
                  exact .yes <|
                    .trans
                      (interAtoms_projection (ct := ct) (T := S) (A := .class_ s) huf hmemS)
                      (leafBuiltinNegClass
                        (ct := ct) (B := D) (C := s)
                        hleafD wD.hfind wD.hmro hsOut)
          | none =>
              have hseedAll : ∀ s, s ∈ seeds → s ∈ wD.mro :=
                firstOutside_none hseedOff
              have hdenCur :
                  Ty.semDenotes ct S
                    (currentObjOf (ct := ct) D wD.hfind wD.hmro) :=
                fresh_to_current_denotes
                  (ct := ct) (S := S) (D := D)
                  hwfct huf wD
                  seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
                  holdAtom hnegClear hseedAll
              have hnotU :
                  ¬ Ty.semDenotes ct (.negClass D)
                    (currentObjOf (ct := ct) D wD.hfind wD.hmro) := by
                intro hneg
                have hself : D ∈ wD.mro := by
                  simpa [findClass_name wD.hfind] using mro_self_mem wD.hmro
                exact ((currentObjOf_denotes_neg_iff
                  (ct := ct) (C := D) (D := D) wD.hfind wD.hmro).1 hneg) hself
              exact .no (currentObjOf (ct := ct) D wD.hfind wD.hmro) hdenCur hnotU
      | isFalse hnonleafD =>
          by_cases hDseed : D ∈ seeds
          · have hnotU : ¬ Ty.semDenotes ct (.negClass D) oldW := by
              intro hnegOld
              have hself : D ∈ (seedWitness D hDseed).mro := by
                simpa [findClass_name (seedWitness D hDseed).hfind] using
                  mro_self_mem (seedWitness D hDseed).hmro
              exact (freshSeedsObj_denotes_neg_iff
                (ct := ct) (C := D) seeds hseeds_ne hseeds_nodup
                seedWitness seed_nonleaf).1 hnegOld ⟨D, hDseed, hself⟩
            exact .no oldW hdenS hnotU
          · let newSeeds : List Identifier := D :: seeds
            let newSeedWitness : ∀ s, s ∈ newSeeds → FreshSeedInfo ct s := fun s hs => by
              by_cases hEq : s = D
              · subst hEq
                exact ⟨wD.cls, wD.mro, wD.hfind, wD.hmro⟩
              · exact seedWitness s (by simpa [newSeeds, hEq] using hs)
            let newSeedNonleaf : ∀ s, s ∈ newSeeds → ¬ LeafBuiltin ct s := fun s hs => by
              by_cases hEq : s = D
              · subst hEq
                exact hnonleafD
              · exact seed_nonleaf s (by simpa [newSeeds, hEq] using hs)
            have hnew_ne : newSeeds ≠ [] := by
              simp [newSeeds]
            have hnew_nodup : newSeeds.Nodup := by
              simp [newSeeds, hDseed, hseeds_nodup]
            let newW :=
              freshSeedsObj (ct := ct)
                newSeeds hnew_ne hnew_nodup newSeedWitness newSeedNonleaf
            have hdenNew :
                Ty.semDenotes ct S newW := by
              refine semDenotes_source_of_atoms
                (ct := ct) (S := S) (obj := newW) huf ?_
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
                        have hEmro : E ∈ wD.mro := by
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
            have hnotU : ¬ Ty.semDenotes ct (.negClass D) newW := by
              intro hnegNew
              have hself :
                  D ∈ (newSeedWitness D (by simp [newSeeds])).mro := by
                simpa [newSeedWitness, newSeeds, findClass_name wD.hfind] using
                  mro_self_mem wD.hmro
              exact (freshSeedsObj_denotes_neg_iff
                (ct := ct) (C := D) newSeeds hnew_ne hnew_nodup
                newSeedWitness newSeedNonleaf).1 hnegNew
                ⟨D, by simp [newSeeds], hself⟩
            exact .no newW hdenNew hnotU

private def decideGoal
    (hwfct : WellFormedClassTable ct) :
    (goal : DecisionGoal ct) → DecisionGoal.Result hwfct goal := by
  let go :
      (goal : DecisionGoal ct) → DecisionGoal.Result hwfct goal :=
    WellFounded.fix
      (r := InvImage WellFoundedRelation.rel goalMeasure)
      (C := fun goal => DecisionGoal.Result hwfct goal)
      (hwf := InvImage.wf goalMeasure (WellFoundedRelation.wf (α := GoalMeasure)))
      (fun goal ih => by
        let recurse :=
          fun (goal' : DecisionGoal ct)
              (hlt : WellFoundedRelation.rel (goalMeasure goal') (goalMeasure goal)) =>
            ih goal' hlt
        cases goal with
        | boundMethodDenotes budget Psum Rsum U hwfPsum hwfRsum hwfU hPsumBudget hRsumBudget =>
            cases U with
            | bottom =>
                exact isFalse (by simp [Ty.semDenotes])
            | class_ D =>
                by_cases hD : D ∈ hwfct.boundMethodExists.mro
                ·
                    exact isTrue <|
                      (boundMethodObj_denotes_class_iff
                        (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).2 hD
                ·
                    exact isFalse <| by
                      intro hden
                      exact hD <|
                        (boundMethodObj_denotes_class_iff
                          (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).1 hden
            | negClass D =>
                by_cases hD : D ∈ hwfct.boundMethodExists.mro
                ·
                    exact isFalse <| by
                      intro hden
                      exact ((boundMethodObj_denotes_neg_iff
                        (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).1 hden) hD
                ·
                    exact isTrue <|
                      (boundMethodObj_denotes_neg_iff
                        (ct := ct) (C := D) (P := Psum) (R := Rsum) hwfct).2 hD
            | union U₁ U₂ =>
                let hdecL :=
                  recurse
                    (.boundMethodDenotes budget Psum Rsum U₁
                      hwfPsum hwfRsum hwfU.union_left hPsumBudget hRsumBudget)
                    (by
                      have hlt : budget + U₁.size < budget + (Ty.union U₁ U₂).size := by
                        have : U₁.size < (Ty.union U₁ U₂).size := by
                          simp [Ty.size]
                          omega
                        exact Nat.add_lt_add_left this budget
                      simpa [goalMeasure] using
                        (goalMeasure_rel_first
                          (a₁ := budget + U₁.size)
                          (a₂ := budget + (Ty.union U₁ U₂).size)
                          (b₁ := U₁.size) (b₂ := (Ty.union U₁ U₂).size)
                          (c₁ := 0) (c₂ := 0) hlt))
                match hdecL with
                | isTrue hL =>
                    exact isTrue (Or.inl hL)
                | isFalse hnotL =>
                    let hdecR :=
                      recurse
                        (.boundMethodDenotes budget Psum Rsum U₂
                          hwfPsum hwfRsum hwfU.union_right hPsumBudget hRsumBudget)
                        (by
                          have hlt : budget + U₂.size < budget + (Ty.union U₁ U₂).size := by
                            have : U₂.size < (Ty.union U₁ U₂).size := by
                              simp [Ty.size]
                              omega
                            exact Nat.add_lt_add_left this budget
                          simpa [goalMeasure] using
                            (goalMeasure_rel_first
                              (a₁ := budget + U₂.size)
                              (a₂ := budget + (Ty.union U₁ U₂).size)
                              (b₁ := U₂.size) (b₂ := (Ty.union U₁ U₂).size)
                              (c₁ := 0) (c₂ := 0) hlt))
                    match hdecR with
                    | isTrue hR =>
                        exact isTrue (Or.inr hR)
                    | isFalse hnotR =>
                        exact isFalse <| by
                          intro hden
                          rcases hden with hL | hR
                          · exact hnotL hL
                          · exact hnotR hR
            | intersection U₁ U₂ =>
                let hdecL :=
                  recurse
                    (.boundMethodDenotes budget Psum Rsum U₁
                      hwfPsum hwfRsum hwfU.intersection_left hPsumBudget hRsumBudget)
                    (by
                      have hlt : budget + U₁.size < budget + (Ty.intersection U₁ U₂).size := by
                        have : U₁.size < (Ty.intersection U₁ U₂).size := by
                          simp [Ty.size]
                          omega
                        exact Nat.add_lt_add_left this budget
                      simpa [goalMeasure] using
                        (goalMeasure_rel_first
                          (a₁ := budget + U₁.size)
                          (a₂ := budget + (Ty.intersection U₁ U₂).size)
                          (b₁ := U₁.size) (b₂ := (Ty.intersection U₁ U₂).size)
                          (c₁ := 0) (c₂ := 0) hlt))
                match hdecL with
                | isFalse hnotL =>
                    exact isFalse <| by
                      intro hden
                      exact hnotL hden.1
                | isTrue hL =>
                    let hdecR :=
                      recurse
                        (.boundMethodDenotes budget Psum Rsum U₂
                          hwfPsum hwfRsum hwfU.intersection_right hPsumBudget hRsumBudget)
                        (by
                          have hlt : budget + U₂.size < budget + (Ty.intersection U₁ U₂).size := by
                            have : U₂.size < (Ty.intersection U₁ U₂).size := by
                              simp [Ty.size]
                              omega
                            exact Nat.add_lt_add_left this budget
                          simpa [goalMeasure] using
                            (goalMeasure_rel_first
                              (a₁ := budget + U₂.size)
                              (a₂ := budget + (Ty.intersection U₁ U₂).size)
                              (b₁ := U₂.size) (b₂ := (Ty.intersection U₁ U₂).size)
                              (c₁ := 0) (c₂ := 0) hlt))
                    match hdecR with
                    | isTrue hR =>
                        exact isTrue ⟨hL, hR⟩
                    | isFalse hnotR =>
                        exact isFalse <| by
                          intro hden
                          exact hnotR hden.2
            | callable P' R' =>
                let hdecP :=
                  recurse
                    (.subtype P' Psum hwfU.callable_param hwfPsum)
                    (by
                      have hRpos : 1 ≤ R'.size := Ty.size_pos (T := R')
                      have hlt : P'.size + Psum.size < budget + (Ty.callable P' R').size := by
                        simp [Ty.size]
                        omega
                      simpa [goalMeasure] using
                        (goalMeasure_rel_first
                          (a₁ := P'.size + Psum.size)
                          (a₂ := budget + (Ty.callable P' R').size)
                          (b₁ := Psum.size) (b₂ := (Ty.callable P' R').size)
                          (c₁ := 1) (c₂ := 0) hlt))
                match hdecP with
                | .no obj hP hnotPsum =>
                    exact isFalse <| by
                      intro hden
                      have hpair :=
                        (boundMethodObj_denotes_callable_iff
                          (ct := ct) (P' := P') (R' := R')
                          (Psum := Psum) (Rsum := Rsum) hwfct).1 hden
                      exact SubtypeDecision.no_notIsSubtype obj hP hnotPsum hpair.1
                | .yes hPsub =>
                    let hdecR :=
                      recurse
                        (.subtype Rsum R' hwfRsum hwfU.callable_return)
                        (by
                          have hPpos : 1 ≤ P'.size := Ty.size_pos (T := P')
                          have hlt : Rsum.size + R'.size < budget + (Ty.callable P' R').size := by
                            simp [Ty.size]
                            omega
                          simpa [goalMeasure] using
                            (goalMeasure_rel_first
                              (a₁ := Rsum.size + R'.size)
                              (a₂ := budget + (Ty.callable P' R').size)
                              (b₁ := R'.size) (b₂ := (Ty.callable P' R').size)
                              (c₁ := 1) (c₂ := 0) hlt))
                    match hdecR with
                    | .yes hRsub =>
                        exact isTrue <|
                          (boundMethodObj_denotes_callable_iff
                            (ct := ct) (P' := P') (R' := R')
                            (Psum := Psum) (Rsum := Rsum) hwfct).2
                            ⟨hPsub, hRsub⟩
                    | .no obj hRsumDen hnotR' =>
                        exact isFalse <| by
                          intro hden
                          have hpair :=
                            (boundMethodObj_denotes_callable_iff
                              (ct := ct) (P' := P') (R' := R')
                              (Psum := Psum) (Rsum := Rsum) hwfct).1 hden
                          exact SubtypeDecision.no_notIsSubtype obj hRsumDen hnotR' hpair.2
        | subtype T U hwfT hwfU =>
            let recurseSubtype :=
              fun (T' U' : Ty) (hwfT' : WellFormedTy ct T') (hwfU' : WellFormedTy ct U')
                  (hlt : WellFoundedRelation.rel
                    (goalMeasure (.subtype T' U' hwfT' hwfU'))
                    (goalMeasure (.subtype T U hwfT hwfU))) =>
                recurse (.subtype T' U' hwfT' hwfU') hlt
            let recurseBoundMethod :=
              fun (budget : Nat) (Psum Rsum U' : Ty)
                  (hwfPsum : WellFormedTy ct Psum)
                  (hwfRsum : WellFormedTy ct Rsum)
                  (hwfU' : WellFormedTy ct U')
                  (hPsumBudget : Psum.size ≤ budget)
                  (hRsumBudget : Rsum.size ≤ budget)
                  (hlt : WellFoundedRelation.rel
                    (goalMeasure (.boundMethodDenotes budget Psum Rsum U'
                      hwfPsum hwfRsum hwfU' hPsumBudget hRsumBudget))
                    (goalMeasure (.subtype T U hwfT hwfU))) =>
                recurse (.boundMethodDenotes budget Psum Rsum U'
                  hwfPsum hwfRsum hwfU' hPsumBudget hRsumBudget) hlt
            let handlePostPeelCase :
                {S : Ty} →
                (hS : S = T) →
                (hwfS : WellFormedTy ct S) →
                (huf : S.unionFree) →
                DecisionCleanSourceCase (ct := ct) (S := S) hwfct hwfS →
                (∀ seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden,
                    SubtypeDecision ct S U) →
                SubtypeDecision ct S U := by
              intro S hS hwfS huf hcase freshHandler
              cases hcase with
              | empty hsub =>
                  exact .yes (.trans hsub .bottom)
              | currentFromLeaf cname w hleaf hden hsub _ =>
                  match decideCurrentDenotes (ct := ct) (C := cname) w.hfind w.hmro U with
                  | isTrue hdenU =>
                      exact .yes <|
                        .trans hsub <|
                          leaf_subtype_of_current_denotes
                            (ct := ct) (B := cname) hleaf w.hfind w.hmro U hwfU hdenU
                  | isFalse hnotU =>
                      exact .no (currentObjOf (ct := ct) cname w.hfind w.hmro) hden hnotU
              | boundMethodFromCallables Psum Rsum hwfPsum hwfRsum hPsumSize hRsumSize hden hsub =>
                  let hdec :=
                    recurseBoundMethod S.size Psum Rsum U
                      hwfPsum hwfRsum hwfU hPsumSize hRsumSize
                      (by
                        simpa [goalMeasure, hS] using
                          (goalMeasure_rel_third
                            (a := T.size + U.size)
                            (b := U.size)
                            (c₁ := 0) (c₂ := 1)
                            (by omega)))
                  match hdec with
                  | isTrue hdenU =>
                      exact .yes <|
                        .trans hsub <|
                          callable_subtype_of_boundMethod_denotes
                            (ct := ct) (P := Psum) (R := Rsum) hwfct U hwfU hdenU
                  | isFalse hnotU =>
                      exact .no (boundMethodObj (ct := ct) hwfct Psum Rsum) hden hnotU
              | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden =>
                  exact freshHandler seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden
            let decideClean :
                {S : Ty} →
                (hS : S = T) →
                (hwfS : WellFormedTy ct S) →
                S.unionFree →
                SubtypeDecision ct S U := by
              intro S hS hwfS huf
              cases U with
              | bottom =>
                  let hcase := analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf
                  cases hcase with
                  | empty hsub =>
                      exact .yes hsub
                  | currentFromLeaf cname w _ hden _ _ =>
                      exact .no (currentObjOf (ct := ct) cname w.hfind w.hmro) hden (by
                        intro hbot
                        exact hbot)
                  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf _ hden =>
                      exact .no
                        (freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf)
                        hden (by
                          intro hbot
                          exact hbot)
                  | boundMethodFromCallables Psum Rsum _ _ _ _ hden _ =>
                      exact .no
                        (boundMethodObj (ct := ct) hwfct Psum Rsum)
                        hden (by
                          intro hbot
                          exact hbot)
              | intersection U₁ U₂ =>
                  let hdecL :=
                    recurseSubtype S U₁ hwfS hwfU.intersection_left
                      (by
                        have hlt : S.size + U₁.size < T.size + (Ty.intersection U₁ U₂).size := by
                          have : U₁.size < (Ty.intersection U₁ U₂).size := by
                            simp [Ty.size]
                            omega
                          simpa [hS] using Nat.add_lt_add_left this S.size
                        simpa [goalMeasure] using
                          (goalMeasure_rel_first
                            (a₁ := S.size + U₁.size)
                            (a₂ := T.size + (Ty.intersection U₁ U₂).size)
                            (b₁ := U₁.size) (b₂ := (Ty.intersection U₁ U₂).size)
                            (c₁ := 1) (c₂ := 1) hlt))
                  match hdecL with
                  | .no obj hSden hnotL =>
                      exact SubtypeDecision.no_intersection_left obj hSden hnotL
                  | .yes hsubL =>
                      let hdecR :=
                        recurseSubtype S U₂ hwfS hwfU.intersection_right
                          (by
                            have hlt : S.size + U₂.size < T.size + (Ty.intersection U₁ U₂).size := by
                              have : U₂.size < (Ty.intersection U₁ U₂).size := by
                                simp [Ty.size]
                                omega
                              simpa [hS] using Nat.add_lt_add_left this S.size
                            simpa [goalMeasure] using
                              (goalMeasure_rel_first
                                (a₁ := S.size + U₂.size)
                                (a₂ := T.size + (Ty.intersection U₁ U₂).size)
                                (b₁ := U₂.size) (b₂ := (Ty.intersection U₁ U₂).size)
                                (c₁ := 1) (c₂ := 1) hlt))
                      match hdecR with
                      | .yes hsubR =>
                          exact .yes (.interIntro hsubL hsubR)
                      | .no obj hSden hnotR =>
                          exact SubtypeDecision.no_intersection_right obj hSden hnotR
              | class_ D =>
                  by_cases hDobj : D = objectClass
                  · subst hDobj
                    exact .yes .objectTop
                  · let hcase := analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf
                    exact handlePostPeelCase hS hwfS huf hcase
                      (fun seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden =>
                        freshClassDecision
                          (ct := ct) (S := S) (D := D)
                          hwfct hwfS huf hDobj
                          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden)
              | negClass D =>
                  let hcase := analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf
                  exact handlePostPeelCase hS hwfS huf hcase
                    (fun seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden =>
                      freshNegDecision
                        (ct := ct) (S := S) (D := D)
                        hwfct huf hwfU
                        seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden)
              | callable P R =>
                  let hcase := analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf
                  exact handlePostPeelCase hS hwfS huf hcase
                    (fun seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf _ hden =>
                      freshCallableDecision
                        (ct := ct) (S := S) (P := P) (R := R)
                        seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf hden)
              | union U₀ V₀ =>
                  let hcase := analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf
                  exact handlePostPeelCase hS hwfS huf hcase
                    (fun seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf _ hdenS => by
                      let atoms := (Ty.union U₀ V₀).unionAtoms
                      let flat := Ty.unionAtomsFold atoms
                      let oldW :=
                        freshSeedsObj (ct := ct) seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
                      have htoFlat : IsSubtype ct (Ty.union U₀ V₀) flat :=
                        subtype_self_unionAtomsFold (ct := ct) (T := Ty.union U₀ V₀)
                      have hfromFlat : IsSubtype ct flat (Ty.union U₀ V₀) :=
                        unionAtomsFold_subtype_self (ct := ct) (T := Ty.union U₀ V₀)
                      have hnoUnion : ∀ X Y, Ty.union X Y ∉ atoms := by
                        intro X Y
                        simpa [atoms] using unionAtoms_union_not_mem (Ty.union U₀ V₀) X Y
                      cases hpick : pickUsefulUnionArm atoms with
                      | none =>
                          have hnoUseful := pickUsefulUnionArm_spec_none hpick
                          have hnotFlat :
                              ¬ Ty.semDenotes ct flat oldW :=
                            fresh_not_denotes_unionAtomsFold_of_noUseful
                              (ct := ct)
                              (atoms := atoms)
                              (seeds := seeds)
                              (hseeds_ne := hseeds_ne)
                              (hseeds_nodup := hseeds_nodup)
                              (seedWitness := seedWitness)
                              (seed_nonleaf := seed_nonleaf)
                              hnoUseful hnoUnion
                          have hnotU :
                              ¬ Ty.semDenotes ct (Ty.union U₀ V₀) oldW := by
                            intro hdenU
                            exact hnotFlat <|
                              semDenotes_at_obj_sound
                                (ct := ct)
                                (obj := oldW)
                                htoFlat hdenU
                          exact .no oldW hdenS hnotU
                      | some pair =>
                          rcases pair with ⟨A, rest⟩
                          rcases pickUsefulUnionArm_spec_some hpick with
                            ⟨hmemA, huseA, hrestSubset, hcover⟩
                          have hreorderTo :
                              IsSubtype ct flat (Ty.unionAtomsFold (A :: rest)) := by
                            exact unionAtomsFold_subtype_of_subset
                              (ct := ct) (atoms₁ := atoms) (atoms₂ := A :: rest)
                              (fun X hX =>
                                match hcover X hX with
                                | Or.inl hEq => by simp [hEq]
                                | Or.inr hXin => by simp [hXin])
                          have hreorderFrom :
                              IsSubtype ct (Ty.unionAtomsFold (A :: rest)) flat := by
                            exact unionAtomsFold_subtype_of_subset
                              (ct := ct) (atoms₁ := A :: rest) (atoms₂ := atoms)
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
                            exact unionAtoms_member_wellFormed
                              (ct := ct) (T := Ty.union U₀ V₀) hwfU (hrestSubset X hX)
                          have hRlt : R.size < (Ty.union U₀ V₀).size := by
                            have hltFlat : R.size < flat.size := by
                              exact pickUsefulUnionArm_rest_size_lt hpick hrest_ne
                            have hflatSize : flat.size = (Ty.union U₀ V₀).size := by
                              simp [flat, atoms, unionAtomsFold_size_eq_self]
                            rw [← hflatSize]
                            exact hltFlat
                          have hpickedToUnion :
                              IsSubtype ct (Ty.unionAtomsFold (A :: rest)) (Ty.union A R) := by
                            cases rest with
                            | nil =>
                                cases hrest_ne rfl
                            | cons B Bs =>
                                exact .refl
                          have hunionToPicked :
                              IsSubtype ct (Ty.union A R) (Ty.unionAtomsFold (A :: rest)) := by
                            cases rest with
                            | nil =>
                                cases hrest_ne rfl
                            | cons B Bs =>
                                exact .refl
                          have horigToAR :
                              IsSubtype ct (Ty.union U₀ V₀) (Ty.union A R) := by
                            exact .trans htoFlat <| .trans hreorderTo hpickedToUnion
                          have hfinish :
                              IsSubtype ct S (Ty.union A R) →
                              IsSubtype ct S (Ty.union U₀ V₀) := by
                            intro hsub
                            exact .trans hsub <| .trans hunionToPicked <| .trans hreorderFrom hfromFlat
                          have hwfA : WellFormedTy ct A :=
                            unionAtoms_member_wellFormed
                              (ct := ct) (T := Ty.union U₀ V₀) hwfU hmemA
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
                                    have hBsize : 1 ≤ B.size := Ty.size_pos (T := B)
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
                          let liftNo :=
                            fun (obj : SemObject ct)
                                (hSden : Ty.semDenotes ct S obj)
                                (hnotAR : ¬ Ty.semDenotes ct (Ty.union A R) obj) =>
                              SubtypeDecision.no obj hSden <| by
                                intro hdenOrig
                                exact hnotAR ((semSubtype_sound horigToAR) obj hdenOrig)
                          cases A with
                          | bottom =>
                              let hdecR :=
                                recurseSubtype S R hwfS hRwf
                                  (by
                                    have hlt : S.size + R.size < T.size + (Ty.union U₀ V₀).size := by
                                      simpa [hS] using Nat.add_lt_add_left hRlt S.size
                                    simpa [goalMeasure] using
                                      (goalMeasure_rel_first
                                        (a₁ := S.size + R.size)
                                        (a₂ := T.size + (Ty.union U₀ V₀).size)
                                        (b₁ := R.size) (b₂ := (Ty.union U₀ V₀).size)
                                        (c₁ := 1) (c₂ := 1) hlt))
                              match hdecR with
                              | .yes hsubR =>
                                  exact .yes (hfinish (.unionRight hsubR))
                              | .no obj hSden hnotR =>
                                  exact liftNo obj hSden <| by
                                    intro hdenAR
                                    rcases hdenAR with hbot | hR
                                    · exact hbot
                                    · exact hnotR hR
                          | class_ D =>
                              by_cases hDobj : D = objectClass
                              · subst hDobj
                                exact .yes (hfinish (.unionLeft .objectTop))
                              · have hwfNegD : WellFormedTy ct (Ty.negClass D) :=
                                  WellFormedTy.neg_of_class hwfA
                                have hEqFirst :
                                    (Ty.intersection S (Ty.negClass D)).size + R.size =
                                      T.size + (Ty.union U₀ V₀).size := by
                                  have hAR :
                                      R.size + 2 = (Ty.union U₀ V₀).size := by
                                    have hARflat :
                                        R.size + 2 = (Ty.unionAtomsFold atoms).size := by
                                      simpa [R] using
                                        pickUsefulUnionArm_atomic_rest_size hpick hrest_ne
                                          (by simp [Ty.size])
                                    rw [hARflat, unionAtomsFold_size_eq_self (T := Ty.union U₀ V₀)]
                                  rw [hS]
                                  calc
                                    (Ty.intersection T (Ty.negClass D)).size + R.size
                                        = T.size + (R.size + 2) := by
                                            simp [Ty.size]
                                            omega
                                    _ = T.size + (Ty.union U₀ V₀).size := by
                                          rw [hAR]
                                let hdecR :=
                                  recurseSubtype (Ty.intersection S (Ty.negClass D)) R
                                    (WellFormedTy.intersection hwfS hwfNegD) hRwf
                                    (by
                                      simpa [goalMeasure, hEqFirst] using
                                        (goalMeasure_rel_second
                                          (a := T.size + (Ty.union U₀ V₀).size)
                                          (b₁ := R.size) (b₂ := (Ty.union U₀ V₀).size)
                                          (c₁ := 1) (c₂ := 1) hRlt))
                                match hdecR with
                                | .yes hsubR =>
                                    exact .yes <|
                                      hfinish <|
                                        class_union_of_inter_neg_subtype
                                          (ct := ct) (S := S) (D := D) hsubR
                                | .no obj hInt hnotR =>
                                    exact liftNo obj hInt.1 <| by
                                      intro hdenAR
                                      rcases hdenAR with hclass | hR
                                      · exact hInt.2 hclass
                                      · exact hnotR hR
                          | negClass B =>
                              have hwfClassB : WellFormedTy ct (Ty.class_ B) :=
                                WellFormedTy.class_of_neg hwfA
                              have hEqFirst :
                                  (Ty.intersection S (Ty.class_ B)).size + R.size =
                                    T.size + (Ty.union U₀ V₀).size := by
                                have hAR :
                                    R.size + 2 = (Ty.union U₀ V₀).size := by
                                  have hARflat :
                                      R.size + 2 = (Ty.unionAtomsFold atoms).size := by
                                    simpa [R] using
                                      pickUsefulUnionArm_atomic_rest_size hpick hrest_ne
                                        (by simp [Ty.size])
                                  rw [hARflat, unionAtomsFold_size_eq_self (T := Ty.union U₀ V₀)]
                                rw [hS]
                                calc
                                  (Ty.intersection T (Ty.class_ B)).size + R.size
                                      = T.size + (R.size + 2) := by
                                          simp [Ty.size]
                                          omega
                                  _ = T.size + (Ty.union U₀ V₀).size := by
                                        rw [hAR]
                              let hdecR :=
                                recurseSubtype (Ty.intersection S (Ty.class_ B)) R
                                  (WellFormedTy.intersection hwfS hwfClassB) hRwf
                                  (by
                                    simpa [goalMeasure, hEqFirst] using
                                      (goalMeasure_rel_second
                                        (a := T.size + (Ty.union U₀ V₀).size)
                                        (b₁ := R.size) (b₂ := (Ty.union U₀ V₀).size)
                                        (c₁ := 1) (c₂ := 1) hRlt))
                              match hdecR with
                              | .yes hsubR =>
                                  exact .yes <|
                                    hfinish <|
                                      negClass_union_of_inter_class_subtype
                                        (ct := ct) (S := S) (B := B) hsubR
                              | .no obj hInt hnotR =>
                                  exact liftNo obj hInt.1 <| by
                                    intro hdenAR
                                    rcases hdenAR with hneg | hR
                                    · exact hneg hInt.2
                                    · exact hnotR hR
                          | intersection A₁ A₂ =>
                              let hdecL :=
                                recurseSubtype S (Ty.union A₁ R)
                                  hwfS (.union hwfA.intersection_left hRwf)
                                  (by
                                    have hlt :
                                        S.size + (Ty.union A₁ R).size <
                                          T.size + (Ty.union U₀ V₀).size := by
                                      rw [hS, ← hARSize]
                                      simp [Ty.size]
                                      omega
                                    simpa [goalMeasure] using
                                      (goalMeasure_rel_first
                                        (a₁ := S.size + (Ty.union A₁ R).size)
                                        (a₂ := T.size + (Ty.union U₀ V₀).size)
                                        (b₁ := (Ty.union A₁ R).size) (b₂ := (Ty.union U₀ V₀).size)
                                        (c₁ := 1) (c₂ := 1) hlt))
                              match hdecL with
                              | .no obj hSden hnotL =>
                                  exact liftNo obj hSden <| by
                                    intro hdenAR
                                    rcases hdenAR with hint | hR
                                    · exact hnotL (Or.inl hint.1)
                                    · exact hnotL (Or.inr hR)
                              | .yes hsubL =>
                                  let hdecR' :=
                                    recurseSubtype S (Ty.union A₂ R)
                                      hwfS (.union hwfA.intersection_right hRwf)
                                      (by
                                        have hlt :
                                            S.size + (Ty.union A₂ R).size <
                                              T.size + (Ty.union U₀ V₀).size := by
                                          rw [hS, ← hARSize]
                                          simp [Ty.size]
                                          omega
                                        simpa [goalMeasure] using
                                          (goalMeasure_rel_first
                                            (a₁ := S.size + (Ty.union A₂ R).size)
                                            (a₂ := T.size + (Ty.union U₀ V₀).size)
                                            (b₁ := (Ty.union A₂ R).size) (b₂ := (Ty.union U₀ V₀).size)
                                            (c₁ := 1) (c₂ := 1) hlt))
                                  match hdecR' with
                                  | .yes hsubR =>
                                      exact .yes <|
                                        hfinish <|
                                          subtype_union_intersection_combine
                                            (ct := ct) (S := S) (A₁ := A₁) (A₂ := A₂) (R := R)
                                            hsubL hsubR
                                  | .no obj hSden hnotR =>
                                      exact liftNo obj hSden <| by
                                        intro hdenAR
                                        rcases hdenAR with hint | hR
                                        · exact hnotR (Or.inl hint.2)
                                        · exact hnotR (Or.inr hR)
                          | callable _ _ =>
                              simp [usefulUnionArm] at huseA
                          | union X Y =>
                              exact False.elim (hnoUnion X Y hmemA))
            cases T with
            | bottom =>
                exact .yes .bottom
            | union T₁ T₂ =>
                let hdecL :=
                  recurseSubtype T₁ U hwfT.union_left hwfU
                    (by
                      have hlt : T₁.size + U.size < (Ty.union T₁ T₂).size + U.size := by
                        simp [Ty.size]
                        omega
                      simpa [goalMeasure] using
                        (goalMeasure_rel_first
                          (a₁ := T₁.size + U.size)
                          (a₂ := (Ty.union T₁ T₂).size + U.size)
                          (b₁ := U.size) (b₂ := U.size)
                          (c₁ := 1) (c₂ := 1) hlt))
                match hdecL with
                | .no obj hT₁ hnotU =>
                    exact SubtypeDecision.no_union_left obj hT₁ hnotU
                | .yes hsubL =>
                    let hdecR :=
                      recurseSubtype T₂ U hwfT.union_right hwfU
                        (by
                          have hlt : T₂.size + U.size < (Ty.union T₁ T₂).size + U.size := by
                            simp [Ty.size]
                            omega
                          simpa [goalMeasure] using
                            (goalMeasure_rel_first
                              (a₁ := T₂.size + U.size)
                              (a₂ := (Ty.union T₁ T₂).size + U.size)
                              (b₁ := U.size) (b₂ := U.size)
                              (c₁ := 1) (c₂ := 1) hlt))
                    match hdecR with
                    | .yes hsubR =>
                        exact .yes (.unionElim hsubL hsubR)
                    | .no obj hT₂ hnotU =>
                        exact SubtypeDecision.no_union_right obj hT₂ hnotU
            | class_ C =>
                have huf : (Ty.class_ C).unionFree := by
                  simp [Ty.unionFree]
                exact decideClean rfl hwfT huf
            | negClass C =>
                by_cases hObj : C = objectClass
                · subst hObj
                  exact .yes (negObject_subtype_any (ct := ct) (U := U) hwfct)
                · have huf : (Ty.negClass C).unionFree := by
                    simp [Ty.unionFree]
                  exact decideClean rfl hwfT huf
            | callable P R =>
                have huf : (Ty.callable P R).unionFree := by
                  simp [Ty.unionFree]
                exact decideClean rfl hwfT huf
            | intersection T₁ T₂ =>
                by_cases huf : (Ty.intersection T₁ T₂).unionFree
                · exact decideClean rfl hwfT huf
                · let split := splitNonUnionFree (T := Ty.intersection T₁ T₂) huf
                  let hwfL := splitNonUnionFree_wf_left hwfT huf
                  let hwfR := splitNonUnionFree_wf_right hwfT huf
                  let hdecL :=
                    recurseSubtype split.left U hwfL hwfU
                      (by
                        have hlt : split.left.size + U.size < (Ty.intersection T₁ T₂).size + U.size := by
                          exact Nat.add_lt_add_right split.left_lt U.size
                        simpa [goalMeasure] using
                          (goalMeasure_rel_first
                            (a₁ := split.left.size + U.size)
                            (a₂ := (Ty.intersection T₁ T₂).size + U.size)
                            (b₁ := U.size) (b₂ := U.size)
                            (c₁ := 1) (c₂ := 1) hlt))
                  match hdecL with
                  | .no obj hleft hnotU =>
                      exact SubtypeDecision.no_split_left split obj hleft hnotU
                  | .yes hsubL =>
                      let hdecR :=
                        recurseSubtype split.right U hwfR hwfU
                          (by
                            have hlt : split.right.size + U.size < (Ty.intersection T₁ T₂).size + U.size := by
                              exact Nat.add_lt_add_right split.right_lt U.size
                            simpa [goalMeasure] using
                              (goalMeasure_rel_first
                                (a₁ := split.right.size + U.size)
                                (a₂ := (Ty.intersection T₁ T₂).size + U.size)
                                (b₁ := U.size) (b₂ := U.size)
                                (c₁ := 1) (c₂ := 1) hlt))
                      match hdecR with
                      | .yes hsubR =>
                          exact .yes <|
                            .trans split.toUnion (.unionElim hsubL hsubR)
                      | .no obj hright hnotU =>
                          exact SubtypeDecision.no_split_right split obj hright hnotU)
  exact go

def isSubtype_decidable
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    Decidable (IsSubtype ct T U) :=
  SubtypeDecision.toDecidableIsSubtype <|
    decideGoal (ct := ct) hwfct (.subtype T U hwfT hwfU)

def semSubtype_decidable
    (hwfct : WellFormedClassTable ct)
    (hwfT : WellFormedTy ct T)
    (hwfU : WellFormedTy ct U) :
    Decidable (SemSubtype ct T U) := by
  haveI := isSubtype_decidable (ct := ct) (T := T) (U := U) hwfct hwfT hwfU
  exact decidable_of_iff (IsSubtype ct T U)
    (isSubtype_iff_semSubtype (ct := ct) (T := T) (U := U) hwfct hwfT hwfU)

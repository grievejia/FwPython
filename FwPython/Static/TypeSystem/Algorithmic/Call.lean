import FwPython.Static.TypeSystem.Algorithmic.Lookup
import FwPython.Static.Subtyping.Inversion
import FwPython.Static.Subtyping.Completeness.Decision

/-! ## Algorithmic callable summaries -/

structure CertifiedCallableSummaries (ct : ClassTable) (sourceTy : Ty) where
  elems : List (Ty × Ty)
  wf : ∀ pr, pr ∈ elems → WellFormedTy ct pr.1 ∧ WellFormedTy ct pr.2
  sound : ∀ pr, pr ∈ elems → IsSubtype ct sourceTy (.callable pr.1 pr.2)

def bottomCallableSummary (_hwfct : WellFormedClassTable ct) : Ty × Ty :=
  (.class_ objectClass, .bottom)

theorem bottomCallableSummary_refines_any_callable
    (hwfct : WellFormedClassTable ct) :
    IsSubtype ct
      (.callable (bottomCallableSummary hwfct).1 (bottomCallableSummary hwfct).2)
      (.callable P R) := by
  exact .callable .objectTop .bottom

def unionFreeCallableSummaryCandidates
    (hwfct : WellFormedClassTable ct) (S : Ty) (hwfS : WellFormedTy ct S)
    (huf : S.unionFree) :
    CertifiedCallableSummaries ct S :=
  match analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | .empty hsubBottom =>
      { elems := [bottomCallableSummary hwfct]
        wf := by
          intro pr hpr
          simp [bottomCallableSummary] at hpr
          rcases hpr with rfl
          exact ⟨wellFormed_object_type hwfct, .bottom⟩
        sound := by
          intro pr hpr
          simp [bottomCallableSummary] at hpr
          rcases hpr with rfl
          exact .trans hsubBottom .bottom }
  | .currentFromLeaf _ _ _ _ _ _ =>
      { elems := []
        wf := by intro pr hpr; cases hpr
        sound := by intro pr hpr; cases hpr }
  | .freshFromSeeds _ _ _ _ _ _ _ =>
      { elems := []
        wf := by intro pr hpr; cases hpr
        sound := by intro pr hpr; cases hpr }
  | .boundMethodFromCallables Psum Rsum hwfPsum hwfRsum _ _ _ hsub =>
      { elems := [(Psum, Rsum)]
        wf := by
          intro pr hpr
          simp at hpr
          rcases hpr with rfl
          exact ⟨hwfPsum, hwfRsum⟩
        sound := by
          intro pr hpr
          simp at hpr
          rcases hpr with rfl
          simpa using hsub }

theorem unionFreeCallableSummaryCandidates_complete
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (huf : S.unionFree)
    (hsubCallable : IsSubtype ct S (.callable P R)) :
    ∃ pr,
      pr ∈ (unionFreeCallableSummaryCandidates hwfct S hwfS huf).elems ∧
        IsSubtype ct (.callable pr.1 pr.2) (.callable P R) := by
  let hsem : SemSubtype ct S (.callable P R) := semSubtype_sound hsubCallable
  cases hcase : analyzeDecisionCleanSource (ct := ct) (S := S) hwfct hwfS huf with
  | empty hsubBottom =>
      refine ⟨bottomCallableSummary hwfct, ?_, bottomCallableSummary_refines_any_callable (ct := ct) hwfct⟩
      unfold unionFreeCallableSummaryCandidates
      rw [hcase]
      simp
  | currentFromLeaf cname w hleaf hden hsub hrev =>
      have hsem' : SemSubtype ct (.class_ cname) (.callable P R) :=
        SemSubtype.trans (semSubtype_sound hrev) hsem
      exact False.elim <|
        not_semSubtype_class_callable (ct := ct) (.class_ w.hfind w.hmro) hsem'
  | freshFromSeeds seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf seedSource hden =>
      exact False.elim <|
        freshSeedsObj_not_denotes_callable
          (ct := ct) (P := P) (R := R)
          seeds hseeds_ne hseeds_nodup seedWitness seed_nonleaf
          (hsem _ hden)
  | boundMethodFromCallables Psum Rsum hwfPsum hwfRsum _ _ hden hsub =>
      refine ⟨(Psum, Rsum), ?_, ?_⟩
      · unfold unionFreeCallableSummaryCandidates
        rw [hcase]
        simp
      · have href :
            IsSubtype ct (.callable Psum Rsum) (.callable P R) :=
          callable_summary_intro (ct := ct) (P := P) (R := R)
            (Psum := Psum) (Rsum := Rsum) hwfct (hsem _ hden)
        exact href

private theorem split_subtype_callable_inv
    (split : SourceUnionSplit S)
    (hsub : IsSubtype ct S (.callable P R)) :
    IsSubtype ct split.left (.callable P R) ∧
      IsSubtype ct split.right (.callable P R) := by
  have hunion :
      IsSubtype ct (.union split.left split.right) (.callable P R) :=
    .trans split.fromUnion hsub
  exact (subtype_union_iff (ct := ct) (T := split.left) (U := split.right) (V := .callable P R)).1 hunion

private def crossCallableSummaryPairs
    (left right : List (Ty × Ty)) : List (Ty × Ty) :=
  left.flatMap fun pr1 =>
    right.map fun pr2 =>
      (.intersection pr1.1 pr2.1, .union pr1.2 pr2.2)

private theorem mem_crossCallableSummaryPairs :
    pr ∈ crossCallableSummaryPairs left right ↔
      ∃ pr1, pr1 ∈ left ∧ ∃ pr2, pr2 ∈ right ∧
        pr = (.intersection pr1.1 pr2.1, .union pr1.2 pr2.2) := by
  constructor
  · intro hpr
    rw [crossCallableSummaryPairs] at hpr
    rw [List.mem_flatMap] at hpr
    rcases hpr with ⟨pr1, hpr1, hmem⟩
    rw [List.mem_map] at hmem
    rcases hmem with ⟨pr2, hpr2, hEq⟩
    exact ⟨pr1, hpr1, pr2, hpr2, hEq.symm⟩
  · rintro ⟨pr1, hpr1, pr2, hpr2, rfl⟩
    rw [crossCallableSummaryPairs]
    rw [List.mem_flatMap]
    refine ⟨pr1, hpr1, ?_⟩
    rw [List.mem_map]
    exact ⟨pr2, hpr2, rfl⟩

def callableSummaryCandidates
    (hwfct : WellFormedClassTable ct) (S : Ty) (hwfS : WellFormedTy ct S) :
    CertifiedCallableSummaries ct S :=
  if huf : S.unionFree then
    unionFreeCallableSummaryCandidates hwfct S hwfS huf
  else
    let split := splitNonUnionFree (T := S) huf
    let left :=
      callableSummaryCandidates hwfct split.left
        (splitNonUnionFree_wf_left (ct := ct) (T := S) hwfS huf)
    let right :=
      callableSummaryCandidates hwfct split.right
        (splitNonUnionFree_wf_right (ct := ct) (T := S) hwfS huf)
    { elems := crossCallableSummaryPairs left.elems right.elems
      wf := by
        intro pr hpr
        rcases (mem_crossCallableSummaryPairs.1 hpr) with ⟨pr1, hpr1, pr2, hpr2, rfl⟩
        obtain ⟨hwfP1, hwfR1⟩ := left.wf pr1 hpr1
        obtain ⟨hwfP2, hwfR2⟩ := right.wf pr2 hpr2
        exact ⟨.intersection hwfP1 hwfP2, .union hwfR1 hwfR2⟩
      sound := by
        intro pr hpr
        rcases (mem_crossCallableSummaryPairs.1 hpr) with ⟨pr1, hpr1, pr2, hpr2, rfl⟩
        have hleft :
            IsSubtype ct split.left (.callable pr1.1 pr1.2) :=
          left.sound pr1 hpr1
        have hright :
            IsSubtype ct split.right (.callable pr2.1 pr2.2) :=
          right.sound pr2 hpr2
        have hunion :
            IsSubtype ct
              (.union split.left split.right)
              (.union (.callable pr1.1 pr1.2) (.callable pr2.1 pr2.2)) :=
          .unionElim
            (.trans hleft (.unionLeft .refl))
            (.trans hright (.unionRight .refl))
        exact .trans split.toUnion <|
          .trans hunion <|
            subtype_union_callable_summary
              (ct := ct)
              (p1 := pr1.1) (r1 := pr1.2)
              (p2 := pr2.1) (r2 := pr2.2) }
termination_by S.size
decreasing_by
  all_goals
    simp_wf
    first
    | simpa using (splitNonUnionFree (T := S) huf).left_lt
    | simpa using (splitNonUnionFree (T := S) huf).right_lt

private def callableSummaryCandidates_complete_aux
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (hsubCallable : IsSubtype ct S (.callable P R)) :
    ∃ pr,
      pr ∈ (callableSummaryCandidates hwfct S hwfS).elems ∧
        IsSubtype ct (.callable pr.1 pr.2) (.callable P R) := by
  by_cases huf : S.unionFree
  · unfold callableSummaryCandidates
    rw [dif_pos huf]
    exact
      unionFreeCallableSummaryCandidates_complete
        (ct := ct) (S := S) (P := P) (R := R)
        hwfct hwfS huf hsubCallable
  · let split := splitNonUnionFree (T := S) huf
    let hwfL := splitNonUnionFree_wf_left (ct := ct) (T := S) hwfS huf
    let hwfR := splitNonUnionFree_wf_right (ct := ct) (T := S) hwfS huf
    have hsplit := split_subtype_callable_inv (ct := ct) (S := S) (P := P) (R := R) split hsubCallable
    obtain ⟨pr1, hpr1, href1⟩ :=
      callableSummaryCandidates_complete_aux
        (ct := ct) (S := split.left) (P := P) (R := R) hwfct hwfL hsplit.1
    obtain ⟨pr2, hpr2, href2⟩ :=
      callableSummaryCandidates_complete_aux
        (ct := ct) (S := split.right) (P := P) (R := R) hwfct hwfR hsplit.2
    have hinv1 :=
      callable_subtype_inv
        (ct := ct)
        (hBMFind := hwfct.boundMethodExists.hfind)
        (hBMMro := hwfct.boundMethodExists.hmro)
        href1
    have hinv2 :=
      callable_subtype_inv
        (ct := ct)
        (hBMFind := hwfct.boundMethodExists.hfind)
        (hBMMro := hwfct.boundMethodExists.hmro)
        href2
    refine ⟨(.intersection pr1.1 pr2.1, .union pr1.2 pr2.2), ?_, ?_⟩
    · have hmem :
          (.intersection pr1.1 pr2.1, .union pr1.2 pr2.2) ∈
            crossCallableSummaryPairs
              (callableSummaryCandidates hwfct split.left hwfL).elems
              (callableSummaryCandidates hwfct split.right hwfR).elems :=
        (mem_crossCallableSummaryPairs.2 ⟨pr1, hpr1, pr2, hpr2, rfl⟩)
      unfold callableSummaryCandidates
      rw [dif_neg huf]
      simpa [split, hwfL, hwfR] using hmem
    · exact .callable
        (.interIntro hinv1.1 hinv2.1)
        (.unionElim hinv1.2 hinv2.2)
termination_by S.size
decreasing_by
  all_goals
    simp_wf
    first
    | simpa using (splitNonUnionFree (T := S) huf).left_lt
    | simpa using (splitNonUnionFree (T := S) huf).right_lt

theorem callableSummaryCandidates_complete
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (hsubCallable : IsSubtype ct S (.callable P R)) :
    ∃ pr,
      pr ∈ (callableSummaryCandidates hwfct S hwfS).elems ∧
        IsSubtype ct (.callable pr.1 pr.2) (.callable P R) :=
  callableSummaryCandidates_complete_aux hwfct hwfS hsubCallable

def callableSummaryBasis
    (hwfct : WellFormedClassTable ct) (S : Ty) (hwfS : WellFormedTy ct S) :
    List (Ty × Ty) :=
  (callableSummaryCandidates hwfct S hwfS).elems

theorem callableSummaryBasis_member_subtype
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (hmem : pr ∈ callableSummaryBasis hwfct S hwfS) :
    IsSubtype ct S (.callable pr.1 pr.2) :=
  (callableSummaryCandidates hwfct S hwfS).sound pr hmem

theorem callableSummaryBasis_member_wellFormed
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (hmem : pr ∈ callableSummaryBasis hwfct S hwfS) :
    WellFormedTy ct pr.1 ∧ WellFormedTy ct pr.2 :=
  (callableSummaryCandidates hwfct S hwfS).wf pr hmem

theorem callableSummaryBasis_complete
    (hwfct : WellFormedClassTable ct) (hwfS : WellFormedTy ct S)
    (hsubCallable : IsSubtype ct S (.callable P R)) :
    ∃ pr,
      pr ∈ callableSummaryBasis hwfct S hwfS ∧
        IsSubtype ct (.callable pr.1 pr.2) (.callable P R) :=
  callableSummaryCandidates_complete hwfct hwfS hsubCallable

private def callResultsFromEntry
    (hwfct : WellFormedClassTable ct)
    (calleeTy : Ty) (hwfCallee : WellFormedTy ct calleeTy)
    (argBasis : List Ty)
    (hArgWf : ∀ A, A ∈ argBasis → WellFormedTy ct A)
    (entry : { pr // pr ∈ callableSummaryBasis hwfct calleeTy hwfCallee }) : List Ty := by
  let paramTy := entry.1.1
  let resultTy := entry.1.2
  let hwfParam :=
    (callableSummaryBasis_member_wellFormed
      (hwfct := hwfct) (S := calleeTy) (hwfS := hwfCallee) entry.2).1
  exact argBasis.attach.flatMap fun argEntry =>
    let argTy := argEntry.1
    let _ : Decidable (IsSubtype ct argTy paramTy) :=
      isSubtype_decidable (ct := ct) (T := argTy) (U := paramTy)
        hwfct (hArgWf argTy argEntry.2) hwfParam
    if hsub : IsSubtype ct argTy paramTy then [resultTy] else []

private theorem callResultsFromEntry_member_witness
    (hwfct : WellFormedClassTable ct)
    (entry : { pr // pr ∈ callableSummaryBasis hwfct calleeTy hwfCallee })
    (hmem : R ∈
      callResultsFromEntry hwfct calleeTy hwfCallee argBasis hArgWf entry) :
    ∃ A, A ∈ argBasis ∧ IsSubtype ct A entry.1.1 ∧ entry.1.2 = R := by
  unfold callResultsFromEntry at hmem
  simp at hmem
  rcases hmem with ⟨⟨A, hA, hsub⟩, hEq⟩
  exact ⟨A, hA, hsub, hEq.symm⟩

private theorem callResultsFromEntry_mem_of_accepts
    (hwfct : WellFormedClassTable ct)
    (entry : { pr // pr ∈ callableSummaryBasis hwfct calleeTy hwfCallee })
    (hA : A ∈ argBasis)
    (hsub : IsSubtype ct A entry.1.1) :
    entry.1.2 ∈
      callResultsFromEntry hwfct calleeTy hwfCallee argBasis hArgWf entry := by
  unfold callResultsFromEntry
  rw [List.mem_flatMap]
  refine ⟨⟨A, hA⟩, by simp, ?_⟩
  simp [hsub]

def callResultsFromTy
    (hwfct : WellFormedClassTable ct) (calleeTy : Ty)
    (hwfCallee : WellFormedTy ct calleeTy)
    (argBasis : List Ty)
    (hArgWf : ∀ A, A ∈ argBasis → WellFormedTy ct A) : List Ty :=
  (callableSummaryBasis hwfct calleeTy hwfCallee).attach.flatMap
    (callResultsFromEntry hwfct calleeTy hwfCallee argBasis hArgWf)

theorem callResultsFromTy_member_witness
    (hwfct : WellFormedClassTable ct)
    (hmem : R ∈ callResultsFromTy hwfct calleeTy hwfCallee argBasis hArgWf) :
    ∃ A P,
      A ∈ argBasis ∧
        (P, R) ∈ callableSummaryBasis hwfct calleeTy hwfCallee ∧
        IsSubtype ct A P := by
  unfold callResultsFromTy at hmem
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨entry, _, hmemEntry⟩
  rcases entry with ⟨⟨P, R'⟩, hentry⟩
  obtain ⟨A, hA, hsub, hEq⟩ :=
    callResultsFromEntry_member_witness
      (hwfct := hwfct) (calleeTy := calleeTy) (hwfCallee := hwfCallee)
      (argBasis := argBasis) (hArgWf := hArgWf)
      (entry := ⟨(P, R'), hentry⟩) hmemEntry
  cases hEq
  exact ⟨A, P, hA, hentry, hsub⟩

theorem callResultsFromTy_sound
    (hwfct : WellFormedClassTable ct)
    (hmem : R ∈ callResultsFromTy hwfct calleeTy hwfCallee argBasis hArgWf)
    (hcallee : HasType ct Γ callee calleeTy)
    (harg : ∀ A, A ∈ argBasis → HasType ct Γ arg A) :
    HasType ct Γ (.call callee arg) R := by
  obtain ⟨A, P, hA, hsummaryMem, hsubArg⟩ :=
    callResultsFromTy_member_witness
      (hwfct := hwfct) (calleeTy := calleeTy) (hwfCallee := hwfCallee)
      (argBasis := argBasis) (hArgWf := hArgWf) hmem
  have hsummarySubtype :
      IsSubtype ct calleeTy (.callable P R) :=
    callableSummaryBasis_member_subtype
      (hwfct := hwfct) (S := calleeTy) (hwfS := hwfCallee) hsummaryMem
  have hsummaryWf :
      WellFormedTy ct P ∧ WellFormedTy ct R :=
    callableSummaryBasis_member_wellFormed
      (hwfct := hwfct) (S := calleeTy) (hwfS := hwfCallee) hsummaryMem
  have hcalleeCallable :
      HasType ct Γ callee (.callable P R) :=
    .sub hcallee hsummarySubtype (.callable hsummaryWf.1 hsummaryWf.2)
  exact .call hcalleeCallable (harg A hA) hsubArg

theorem callResultsFromTy_complete
    (hwfct : WellFormedClassTable ct)
    (hsubCallable : IsSubtype ct calleeTy (.callable P R))
    (hA : A ∈ argBasis)
    (hsubArg : IsSubtype ct A P) :
    ∃ R',
      R' ∈ callResultsFromTy hwfct calleeTy hwfCallee argBasis hArgWf ∧
        IsSubtype ct R' R := by
  obtain ⟨pr, hpr, href⟩ :=
    callableSummaryBasis_complete
      (ct := ct) (S := calleeTy) (P := P) (R := R)
      hwfct hwfCallee hsubCallable
  have hinv :=
    callable_subtype_inv
      (ct := ct)
      (hBMFind := hwfct.boundMethodExists.hfind)
      (hBMMro := hwfct.boundMethodExists.hmro)
      href
  have hsubArg' : IsSubtype ct A pr.1 := .trans hsubArg hinv.1
  refine ⟨pr.2, ?_, hinv.2⟩
  unfold callResultsFromTy
  rw [List.mem_flatMap]
  refine ⟨⟨pr, hpr⟩, by simp, ?_⟩
  exact callResultsFromEntry_mem_of_accepts
    (hwfct := hwfct) (calleeTy := calleeTy) (hwfCallee := hwfCallee)
    (argBasis := argBasis) (hArgWf := hArgWf)
    (entry := ⟨pr, hpr⟩) hA hsubArg'

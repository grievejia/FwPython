import FwPython.Static.TypeSystem.TypingLemmas
import FwPython.Static.TypeSystem.Algorithmic.Lookup
import FwPython.Static.Subtyping.Completeness.Decision

/-! ## Algorithmic attribute enumeration -/

private theorem findMethodType_class_wellFormed
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    WellFormedTy ct (.class_ cname) := by
  obtain ⟨_, _, _, hfind, hmro, _, _, _⟩ := hfmt
  exact .class_ hfind hmro

private theorem findMethodType_callable_wellFormed
    (hwfct : WellFormedClassTable ct)
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    WellFormedTy ct (.callable paramTy returnTy) :=
  (findMethodType_wellFormed hwfct hfmt).elim .callable

private inductive AttrCase (ct : ClassTable) :
    Ty → Identifier → Ty → Type where
  | class_ :
      FindMethodType ct cname attrName paramTy returnTy →
      AttrCase ct (.class_ cname) attrName (.callable paramTy returnTy)
  | union :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrCase ct
        (.union (.class_ c1) (.class_ c2))
        attrName
        (.union (.callable p1 r1) (.callable p2 r2))
  | inter :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrCase ct
        (.intersection (.class_ c1) (.class_ c2))
        attrName
        (.intersection (.callable p1 r1) (.callable p2 r2))

private theorem AttrCase.receiver_wellFormed :
    AttrCase ct recvTy attrName resultTy → WellFormedTy ct recvTy
  | .class_ hfmt => findMethodType_class_wellFormed hfmt
  | .union hfmt1 hfmt2 =>
      .union (findMethodType_class_wellFormed hfmt1) (findMethodType_class_wellFormed hfmt2)
  | .inter hfmt1 hfmt2 =>
      .intersection (findMethodType_class_wellFormed hfmt1) (findMethodType_class_wellFormed hfmt2)

private theorem AttrCase.result_wellFormed (hwfct : WellFormedClassTable ct) :
    AttrCase ct recvTy attrName resultTy → WellFormedTy ct resultTy
  | .class_ hfmt => findMethodType_callable_wellFormed hwfct hfmt
  | .union hfmt1 hfmt2 =>
      .union (findMethodType_callable_wellFormed hwfct hfmt1)
        (findMethodType_callable_wellFormed hwfct hfmt2)
  | .inter hfmt1 hfmt2 =>
      .intersection (findMethodType_callable_wellFormed hwfct hfmt1)
        (findMethodType_callable_wellFormed hwfct hfmt2)

private def singleAttrReceiverViews
    (hwfct : WellFormedClassTable ct)
    (attr : Identifier) (c : Identifier) : List (Ty × Ty) :=
  match staticLookupMethodTy? hwfct c attr with
  | some (p, r) => [(.class_ c, .callable p r)]
  | none => []

private def pairAttrReceiverViews
    (hwfct : WellFormedClassTable ct)
    (attr : Identifier) (c1 c2 : Identifier) : List (Ty × Ty) :=
  match staticLookupMethodTy? hwfct c1 attr, staticLookupMethodTy? hwfct c2 attr with
  | some (p1, r1), some (p2, r2) =>
      [ ( .union (.class_ c1) (.class_ c2)
        , .union (.callable p1 r1) (.callable p2 r2))
      , ( .intersection (.class_ c1) (.class_ c2)
        , .intersection (.callable p1 r1) (.callable p2 r2)) ]
  | _, _ => []

def allAttrReceiverViews
    (hwfct : WellFormedClassTable ct)
    (attr : Identifier) : List (Ty × Ty) :=
  let names := classNameList ct
  names.flatMap (singleAttrReceiverViews hwfct attr) ++
    names.flatMap (fun c1 => names.flatMap (pairAttrReceiverViews hwfct attr c1))

private theorem singleAttrReceiverViews_mem_case
    (hwfct : WellFormedClassTable ct)
    (hmem : (viewTy, resultTy) ∈ singleAttrReceiverViews hwfct attr c) :
    Nonempty (AttrCase ct viewTy attr resultTy) := by
  unfold singleAttrReceiverViews at hmem
  cases hlookup : staticLookupMethodTy? hwfct c attr with
  | none =>
      simp [hlookup] at hmem
  | some pr =>
      rcases pr with ⟨p, r⟩
      simp [hlookup] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨.class_ ((staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup)⟩

private theorem pairAttrReceiverViews_mem_case
    (hwfct : WellFormedClassTable ct)
    (hmem : (viewTy, resultTy) ∈ pairAttrReceiverViews hwfct attr c1 c2) :
    Nonempty (AttrCase ct viewTy attr resultTy) := by
  unfold pairAttrReceiverViews at hmem
  cases hlookup1 : staticLookupMethodTy? hwfct c1 attr with
  | none =>
      simp [hlookup1] at hmem
  | some pr1 =>
      rcases pr1 with ⟨p1, r1⟩
      cases hlookup2 : staticLookupMethodTy? hwfct c2 attr with
      | none =>
          simp [hlookup1, hlookup2] at hmem
      | some pr2 =>
          rcases pr2 with ⟨p2, r2⟩
          simp [hlookup1, hlookup2] at hmem
          rcases hmem with hmem | hmem
          · rcases hmem with ⟨rfl, rfl⟩
            exact ⟨.union
              ((staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup1)
              ((staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup2)⟩
          · rcases hmem with ⟨rfl, rfl⟩
            exact ⟨.inter
              ((staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup1)
              ((staticLookupMethodTy?_some_iff_findMethodType hwfct).1 hlookup2)⟩

private theorem allAttrReceiverViews_member_case
    (hwfct : WellFormedClassTable ct)
    (hmem : (viewTy, resultTy) ∈ allAttrReceiverViews hwfct attr) :
    Nonempty (AttrCase ct viewTy attr resultTy) := by
  unfold allAttrReceiverViews at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · simp at hmem
    rcases hmem with ⟨c, _, hmem⟩
    exact singleAttrReceiverViews_mem_case hwfct hmem
  · simp at hmem
    rcases hmem with ⟨c1, _, c2, _, hmem⟩
    exact pairAttrReceiverViews_mem_case hwfct hmem

theorem allAttrReceiverViews_member_wellFormed
    (hwfct : WellFormedClassTable ct)
    (hmem : (viewTy, resultTy) ∈ allAttrReceiverViews hwfct attr) :
    WellFormedTy ct viewTy ∧ WellFormedTy ct resultTy := by
  obtain ⟨hcase⟩ := allAttrReceiverViews_member_case (hwfct := hwfct) hmem
  exact ⟨hcase.receiver_wellFormed, hcase.result_wellFormed hwfct⟩

private theorem allAttrReceiverViews_member_of_case
    (hwfct : WellFormedClassTable ct)
    (hcase : AttrCase ct viewTy attr resultTy) :
    (viewTy, resultTy) ∈ allAttrReceiverViews hwfct attr := by
  cases hcase with
  | class_ hfmt =>
      have hlookup := staticLookupMethodTy?_of_find hwfct hfmt
      obtain ⟨cls, _, _, hfind, _, _, _, _⟩ := hfmt
      refine List.mem_append.mpr (Or.inl ?_)
      simp [singleAttrReceiverViews]
      refine ⟨cls.name, findClass_some_mem_classNameList (findClass_self hfind), ?_⟩
      simp [findClass_name hfind, hlookup]
  | union hfmt1 hfmt2 | inter hfmt1 hfmt2 =>
      have hlookup1 := staticLookupMethodTy?_of_find hwfct hfmt1
      have hlookup2 := staticLookupMethodTy?_of_find hwfct hfmt2
      obtain ⟨cls1, _, _, hfind1, _, _, _, _⟩ := hfmt1
      obtain ⟨cls2, _, _, hfind2, _, _, _, _⟩ := hfmt2
      refine List.mem_append.mpr (Or.inr ?_)
      simp [pairAttrReceiverViews]
      refine ⟨cls1.name, findClass_some_mem_classNameList (findClass_self hfind1), cls2.name,
        findClass_some_mem_classNameList (findClass_self hfind2), ?_⟩
      simp [findClass_name hfind1, findClass_name hfind2, hlookup1, hlookup2]

theorem attrReceiverView_class_member
    (hwfct : WellFormedClassTable ct)
    (hfmt : FindMethodType ct c attr p r) :
    ((.class_ c), (.callable p r)) ∈ allAttrReceiverViews hwfct attr :=
  allAttrReceiverViews_member_of_case hwfct (.class_ hfmt)

theorem attrReceiverView_union_member
    (hwfct : WellFormedClassTable ct)
    (hfmt1 : FindMethodType ct c1 attr p1 r1)
    (hfmt2 : FindMethodType ct c2 attr p2 r2) :
    ((.union (.class_ c1) (.class_ c2)),
      (.union (.callable p1 r1) (.callable p2 r2))) ∈
      allAttrReceiverViews hwfct attr :=
  allAttrReceiverViews_member_of_case hwfct (.union hfmt1 hfmt2)

private def attrResultsFromEntry
    (hwfct : WellFormedClassTable ct)
    (sourceTy : Ty) (hwfSource : WellFormedTy ct sourceTy)
    (attr : Identifier)
    (entry : { pr // pr ∈ allAttrReceiverViews hwfct attr }) : List Ty := by
  let viewTy := entry.1.1
  let resultTy := entry.1.2
  let hwfView :=
    (allAttrReceiverViews_member_wellFormed
      (hwfct := hwfct) (attr := attr) entry.2).1
  let _ : Decidable (IsSubtype ct sourceTy viewTy) :=
    isSubtype_decidable (ct := ct) (T := sourceTy) (U := viewTy)
      hwfct hwfSource hwfView
  exact if hsub : IsSubtype ct sourceTy viewTy then [resultTy] else []

def attrResultsFromTy (hwfct : WellFormedClassTable ct)
    (sourceTy : Ty) (hwfSource : WellFormedTy ct sourceTy)
    (attr : Identifier) : List Ty :=
  (allAttrReceiverViews hwfct attr).attach.flatMap
    (attrResultsFromEntry hwfct sourceTy hwfSource attr)

private theorem attrResultsFromTy_member_witness
    (hwfct : WellFormedClassTable ct)
    (hmem : R ∈ attrResultsFromTy hwfct sourceTy hwfSource attr) :
    ∃ viewTy,
      (viewTy, R) ∈ allAttrReceiverViews hwfct attr ∧
        IsSubtype ct sourceTy viewTy := by
  unfold attrResultsFromTy at hmem
  simp [attrResultsFromEntry] at hmem
  rcases hmem with ⟨viewTy, hsub, hviewMem⟩
  exact ⟨viewTy, hviewMem, hsub⟩

private theorem hasType_attrAccess_of_case
    (hbase : HasType ct Γ base sourceTy)
    (hsub : IsSubtype ct sourceTy viewTy)
    (hcase : AttrCase ct viewTy attr R) :
    HasType ct Γ (.attrAccess base attr) R := by
  have hbaseView : HasType ct Γ base viewTy :=
    .sub hbase hsub hcase.receiver_wellFormed
  cases hcase with
  | class_ hfmt =>
      exact .attrAccess hbaseView hfmt
  | union hfmt1 hfmt2 =>
      exact .attrAccessUnion hbaseView hfmt1 hfmt2
  | inter hfmt1 hfmt2 =>
      exact HasType.attrAccessInter
        (.sub hbaseView (.interLeft .refl) (findMethodType_class_wellFormed hfmt1))
        (.sub hbaseView (.interRight .refl) (findMethodType_class_wellFormed hfmt2))
        hfmt1 hfmt2

theorem attrResultsFromTy_sound
    (hwfct : WellFormedClassTable ct)
    (hmem : R ∈ attrResultsFromTy hwfct sourceTy hwfSource attr)
    (hbase : HasType ct Γ base sourceTy) :
    HasType ct Γ (.attrAccess base attr) R := by
  obtain ⟨viewTy, hviewMem, hsub⟩ :=
    attrResultsFromTy_member_witness
      (hwfct := hwfct) (sourceTy := sourceTy) (hwfSource := hwfSource)
      (attr := attr) hmem
  obtain ⟨hcase⟩ := allAttrReceiverViews_member_case (hwfct := hwfct) hviewMem
  exact hasType_attrAccess_of_case hbase hsub hcase

theorem attrResultsFromTy_complete_of_member
    (hwfct : WellFormedClassTable ct)
    (hsub : IsSubtype ct sourceTy viewTy)
    (hviewMem : (viewTy, R) ∈ allAttrReceiverViews hwfct attr) :
    R ∈ attrResultsFromTy hwfct sourceTy hwfSource attr := by
  unfold attrResultsFromTy
  simp [attrResultsFromEntry]
  exact ⟨viewTy, hsub, hviewMem⟩

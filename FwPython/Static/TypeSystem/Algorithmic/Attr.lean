import FwPython.Static.TypeSystem.TypingLemmas
import FwPython.Static.TypeSystem.Algorithmic.Lookup
import FwPython.Static.Subtyping.Decision

/-! ## Algorithmic attribute enumeration -/

open FwPython.Static.Subtyping

variable {ct : ClassTable} {structural : WellFormedClassHierarchy ct}

/-- Successful method-type lookup establishes that the receiver class name is known. -/
private theorem findMethodType_class_wellFormed
    (hfmt : FindMethodType ct cname attrName paramTy returnTy) :
    WellFormedTy ct (.class_ cname) := by
  obtain ⟨_, _, _, hfind, _, _, _, _⟩ := hfmt
  exact WellFormedTy.class_of_lookup hfind

/-- Method declarations that justify an attribute result for a class, union, or intersection receiver. -/
private inductive AttrCase (ct : ClassTable) :
    Ty → Identifier → Ty → Prop where
  /-- The named receiver class supplies the method. -/
  | class_ :
      FindMethodType ct cname attrName paramTy returnTy →
      AttrCase ct (.class_ cname) attrName (.callable paramTy returnTy)
  /-- Either receiver class supplies its own method requirement. -/
  | union :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrCase ct
        (.union (.class_ c1) (.class_ c2))
        attrName
        (.union (.callable p1 r1) (.callable p2 r2))
  /-- The receiver satisfies both classes and both method requirements. -/
  | inter :
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      AttrCase ct
        (.intersection (.class_ c1) (.class_ c2))
        attrName
        (.intersection (.callable p1 r1) (.callable p2 r2))

/-- A valid receiver type, its attribute result, and the method declarations that justify it. -/
structure AttrReceiverView (ct : ClassTable) (attr : Identifier) where
  /-- The receiver type for which these method declarations apply. -/
  receiver : WellFormedType (ct.map ClassDecl.name)
  /-- The type of the bound method produced by attribute access. -/
  result : WellFormedType (ct.map ClassDecl.name)
  /-- Method lookup evidence for the class combination represented by the receiver. -/
  private selection : AttrCase ct receiver.raw attr result.raw

/-- A method declaration provides the valid receiver and function result together. -/
private def singleAttrReceiverViews
    (hwfct : WellTypedClassHierarchy ct) (attr c : Identifier) : List (AttrReceiverView ct attr) :=
  match (staticLookupMethodTy? hwfct c attr).attach with
  | some ⟨(_p, _r), found⟩ =>
      let selected := staticLookupMethodTy?_find hwfct found
      [{ receiver := (findMethodType_class_wellFormed selected).toType
         result := (findMethodType_wellFormed hwfct selected).toType
         selection := .class_ selected }]
  | none => []

/-- Two selected methods provide union and intersection receiver alternatives. -/
private def pairAttrReceiverViews
    (hwfct : WellTypedClassHierarchy ct) (attr c1 c2 : Identifier) : List (AttrReceiverView ct attr) :=
  match (staticLookupMethodTy? hwfct c1 attr).attach, (staticLookupMethodTy? hwfct c2 attr).attach with
  | some ⟨(_p1, _r1), found1⟩, some ⟨(_p2, _r2), found2⟩ =>
      let first := staticLookupMethodTy?_find hwfct found1
      let second := staticLookupMethodTy?_find hwfct found2
      let firstReceiver := (findMethodType_class_wellFormed first).toType
      let secondReceiver := (findMethodType_class_wellFormed second).toType
      let firstResult := (findMethodType_wellFormed hwfct first).toType
      let secondResult := (findMethodType_wellFormed hwfct second).toType
      [{ receiver := .union firstReceiver secondReceiver, result := .union firstResult secondResult,
         selection := .union first second },
       { receiver := .intersection firstReceiver secondReceiver, result := .intersection firstResult secondResult,
         selection := .inter first second }]
  | _, _ => []

/-- Receiver alternatives with their valid result types and method lookup evidence. -/
def attrReceiverViews (hwfct : WellTypedClassHierarchy ct) (attr : Identifier) :
    List (AttrReceiverView ct attr) :=
  let names := ct.map ClassDecl.name
  names.flatMap (singleAttrReceiverViews hwfct attr) ++
    names.flatMap (fun c1 => names.flatMap (pairAttrReceiverViews hwfct attr c1))

/-- A selected class method occurs in the packaged receiver enumeration. -/
theorem attrReceiverView_class_member
    (hwfct : WellTypedClassHierarchy ct) (hfmt : FindMethodType ct c attr p r) :
    ∃ view ∈ attrReceiverViews hwfct attr,
      view.receiver.raw = .class_ c ∧ view.result.raw = .callable p r := by
  have hlookup := staticLookupMethodTy?_of_find hwfct hfmt
  let view : AttrReceiverView ct attr :=
    ⟨(findMethodType_class_wellFormed hfmt).toType,
      (findMethodType_wellFormed hwfct hfmt).toType, .class_ hfmt⟩
  refine ⟨view, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ?_)), rfl, rfl⟩
  obtain ⟨cls, _, _, hfind, _, _, _, _⟩ := hfmt
  refine ⟨cls.name, findClass_name_known (findClass_self hfind), ?_⟩
  rw [findClass_name hfind]
  simp [singleAttrReceiverViews, Option.attach_eq_some _ ⟨_, hlookup⟩, view,
    WellFormedTy.toType]

/-- Two selected class methods supply a packaged union receiver and result. -/
theorem attrReceiverView_union_member
    (hwfct : WellTypedClassHierarchy ct)
    (hfmt1 : FindMethodType ct c1 attr p1 r1) (hfmt2 : FindMethodType ct c2 attr p2 r2) :
    ∃ view ∈ attrReceiverViews hwfct attr,
      view.receiver.raw = .union (.class_ c1) (.class_ c2) ∧
      view.result.raw = .union (.callable p1 r1) (.callable p2 r2) := by
  have hlookup1 := staticLookupMethodTy?_of_find hwfct hfmt1
  have hlookup2 := staticLookupMethodTy?_of_find hwfct hfmt2
  let view : AttrReceiverView ct attr :=
    ⟨.union (findMethodType_class_wellFormed hfmt1).toType (findMethodType_class_wellFormed hfmt2).toType,
      .union (findMethodType_wellFormed hwfct hfmt1).toType
        (findMethodType_wellFormed hwfct hfmt2).toType, .union hfmt1 hfmt2⟩
  refine ⟨view, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ?_)), rfl, rfl⟩
  obtain ⟨cls1, _, _, hfind1, _, _, _, _⟩ := hfmt1
  obtain ⟨cls2, _, _, hfind2, _, _, _, _⟩ := hfmt2
  refine ⟨cls1.name, findClass_name_known (findClass_self hfind1),
    List.mem_flatMap.mpr ⟨cls2.name, findClass_name_known (findClass_self hfind2), ?_⟩⟩
  rw [findClass_name hfind1, findClass_name hfind2]
  simp [pairAttrReceiverViews, Option.attach_eq_some _ ⟨_, hlookup1⟩,
    Option.attach_eq_some _ ⟨_, hlookup2⟩, view, WellFormedTy.toType, WellFormedType.union]

/-- Valid result types for receiver alternatives that contain the source type. -/
def attrResultsFromTy (hwfct : WellTypedClassHierarchy ct)
    (source : WellFormedType (ct.map ClassDecl.name)) (attr : Identifier) :
    List (WellFormedType (ct.map ClassDecl.name)) :=
  (attrReceiverViews hwfct attr).flatMap fun view =>
    letI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy source view.receiver
    if IsSubtype hwfct.toWellFormedClassHierarchy source.raw view.receiver.raw then [view.result] else []

/-- A receiver subtype and a method-selection case give a type for the attribute access. -/
private theorem hasType_attrAccess_of_case
    (hbase : HasType structural Γ base sourceTy)
    (hsub : IsSubtype structural sourceTy viewTy)
    (hcase : AttrCase ct viewTy attr R) :
    HasType structural Γ (.attrAccess base attr) R := by
  have hbaseView : HasType structural Γ base viewTy :=
    .sub hbase hsub
  cases hcase with
  | class_ hfmt =>
      exact .attrAccess hbaseView hfmt
  | union hfmt1 hfmt2 =>
      exact .attrAccessUnion hbaseView hfmt1 hfmt2
  | inter hfmt1 hfmt2 =>
      exact HasType.attrAccessInter
        (.sub hbaseView (.interLeft (.refl (findMethodType_class_wellFormed hfmt1)) (findMethodType_class_wellFormed hfmt2)))
        (.sub hbaseView (.interRight (.refl (findMethodType_class_wellFormed hfmt2)) (findMethodType_class_wellFormed hfmt1)))
        hfmt1 hfmt2

/-- Each selected method result is a declarative type of the attribute expression. -/
theorem attrResultsFromTy_sound
    (hwfct : WellTypedClassHierarchy ct)
    (source : WellFormedType (ct.map ClassDecl.name))
    (hmem : result ∈ attrResultsFromTy hwfct source attr)
    (hbase : HasType hwfct.toWellFormedClassHierarchy Γ base source.raw) :
    HasType hwfct.toWellFormedClassHierarchy Γ (.attrAccess base attr) result.raw := by
  obtain ⟨view, _, selected⟩ := List.mem_flatMap.mp hmem
  haveI := WellFormedType.subtypeDecidable hwfct.toWellFormedClassHierarchy source view.receiver
  split at selected
  · rename_i included
    cases List.mem_singleton.mp selected
    exact hasType_attrAccess_of_case hbase included view.selection
  · cases selected

/-- An accepted packaged receiver view supplies its result directly. -/
theorem attrResultsFromTy_complete_of_member
    (hwfct : WellTypedClassHierarchy ct)
    (source : WellFormedType (ct.map ClassDecl.name))
    (hsub : IsSubtype hwfct.toWellFormedClassHierarchy source.raw view.receiver.raw)
    (member : view ∈ attrReceiverViews hwfct attr) :
    view.result ∈ attrResultsFromTy hwfct source attr := by
  exact List.mem_flatMap.mpr ⟨view, member, by simp [hsub]⟩

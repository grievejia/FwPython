import FwPython.Common.Identifier
import FwPython.Common.Forall2

/-! # Class-table data model parameterized over the annotation and body types. -/

/-- Method declaration parameterized over annotation and body types. -/
structure MethodDecl (Ty : Type) (Expr : Type) where
  name : Identifier
  receiverParam : Identifier
  param : Identifier
  paramTy : Ty
  returnTy : Ty
  body : Expr
  deriving DecidableEq, Repr

/-- Class declaration parameterized over the method type. -/
structure ClassDecl (Method : Type) where
  name : Identifier
  baseClasses : List Identifier
  methods : List Method
  deriving DecidableEq, Repr

abbrev ClassTableDecl (Method : Type) := List (ClassDecl Method)

structure ProgramDecl (Class : Type) (Expr : Type) where
  classes : List Class
  main : Expr
  deriving DecidableEq, Repr

/-- Generic name lookup over association lists represented as lists. -/
def findByName (getName : α → Identifier) : List α → Identifier → Option α
  | [], _ => none
  | x :: xs, name =>
      if getName x = name then
        some x
      else
        findByName getName xs name

/-- Mapping entries preserves first-match lookup when the map preserves their names. -/
theorem findByName_map_eq
    (mapEntry : α → β)
    (targetName : β → Identifier)
    (sourceName : α → Identifier)
    (preservesName : ∀ entry, targetName (mapEntry entry) = sourceName entry)
    (entries : List α) (name : Identifier) :
    findByName targetName (entries.map mapEntry) name =
      (findByName sourceName entries name).map mapEntry := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      by_cases sameName : sourceName first = name
      · simp [findByName, sameName, preservesName]
      · simpa [findByName, sameName, preservesName] using ih

/-- Generic class lookup for class tables built from `ClassDecl`. -/
def findClass {Method : Type} (ct : ClassTableDecl Method) (cname : Identifier) :
    Option (ClassDecl Method) :=
  findByName ClassDecl.name ct cname

/-- Look in the added classes only if the original table contains no matching name. -/
theorem findClass_append {Method : Type} (original added : ClassTableDecl Method)
    (name : Identifier) :
    findClass (original ++ added) name =
      match findClass original name with
      | some declaration => some declaration
      | none => findClass added name := by
  induction original with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append, findClass, findByName] at ih ⊢
    split <;> simp_all

/-- Appending classes preserves a successful lookup in the original table. -/
theorem findClass_append_preserved {Method : Type} (original added : ClassTableDecl Method)
    (name : Identifier) (entry : ClassDecl Method) (lookup : findClass original name = some entry) :
    findClass (original ++ added) name = some entry := by
  rw [findClass_append, lookup]

/-- Generic method lookup for method lists built from `MethodDecl`. -/
abbrev findMethodInList {Ty : Type} {Expr : Type}
    (ms : List (MethodDecl Ty Expr)) (mname : Identifier) :
    Option (MethodDecl Ty Expr) :=
  findByName MethodDecl.name ms mname

theorem findByName_mem
    (h : findByName getName xs key = some x) :
    x ∈ xs := by
  induction xs with
  | nil => simp [findByName] at h
  | cons y ys ih => simp [findByName] at h; split at h <;> simp_all

theorem findByName_name
    (h : findByName getName xs key = some x) :
    getName x = key := by
  induction xs with
  | nil => simp [findByName] at h
  | cons y ys ih => simp [findByName] at h; split at h <;> simp_all

/-- A successful class lookup places the requested name in the table's name list. -/
theorem findClass_name_known (lookup : findClass table name = some declaration) :
    name ∈ table.map ClassDecl.name :=
  List.mem_map.mpr ⟨declaration, findByName_mem lookup, findByName_name lookup⟩

theorem findByName_eq_none_iff :
    findByName getName xs key = none ↔
      ∀ x, x ∈ xs → getName x ≠ key := by
  induction xs with
  | nil => simp [findByName]
  | cons y ys ih =>
      by_cases h : getName y = key <;> simp [findByName, h, ih]

theorem findClass_mem
    (h : findClass ct cname = some c) : c ∈ ct :=
  findByName_mem h

theorem findClass_name
    (h : findClass ct cname = some c) : c.name = cname :=
  findByName_name h

section Forall2Lookup

variable {R : α → β → Prop}
  {getName₁ : α → Identifier} {getName₂ : β → Identifier}
  {xs : List α} {ys : List β} {key : Identifier}

/-- Failed lookup transports across any pointwise list relation that preserves
member names. -/
theorem findByName_none_of_forall₂
    (hname : ∀ {a b}, R a b → getName₁ a = getName₂ b)
    (hrel : Forall₂ R xs ys)
    (h : findByName getName₁ xs key = none) :
    findByName getName₂ ys key = none := by
  induction hrel generalizing key with
  | nil => rfl
  | @cons a b as bs hr _ ih =>
      by_cases hhead : getName₁ a = key
      · simp [findByName, hhead] at h
      · have hhead₂ : getName₂ b ≠ key :=
          fun hEq => hhead ((hname hr).trans hEq)
        simpa [findByName, hhead₂] using
          ih (by simpa [findByName, hhead] using h)

end Forall2Lookup

universe u v w

section Forall2DataLookup

variable {α : Type u} {β : Type v} {R : α → β → Type w}
  {getName₁ : α → Identifier} {getName₂ : β → Identifier}

/-- Constructive result for transporting a successful left-list lookup to a
right-list lookup. The equality fields are proof-only facts, and the relation
field carries the pointwise data. -/
structure FindByNameForwardData
    (R : α → β → Type w)
    (getName₂ : β → Identifier)
    (ys : List β)
    (key : Identifier)
    (x : α) where
  /-- The related right-list element found by transported lookup. -/
  value : β
  /-- The right-list lookup equality for `value`. -/
  found : findByName getName₂ ys key = some value
  /-- The data-bearing relation between the original left element and `value`. -/
  related : R x value

/-- Constructive result for transporting a successful right-list lookup to a
left-list lookup. The equality fields are proof-only facts, and the relation
field carries the pointwise data. -/
structure FindByNameReverseData
    (R : α → β → Type w)
    (getName₁ : α → Identifier)
    (xs : List α)
    (key : Identifier)
    (y : β) where
  /-- The related left-list element found by reverse transported lookup. -/
  value : α
  /-- The left-list lookup equality for `value`. -/
  found : findByName getName₁ xs key = some value
  /-- The data-bearing relation between `value` and the original right element. -/
  related : R value y

/-- Transport a failed lookup through aligned Type-valued list data by projecting
to the existing Prop lookup theorem. -/
theorem findByName_none_of_forall2Data
    {xs : List α} {ys : List β} {key : Identifier}
    (hname : ∀ {a b}, R a b → getName₁ a = getName₂ b)
    (hrel : Forall2Data R xs ys)
    (h : findByName getName₁ xs key = none) :
    findByName getName₂ ys key = none :=
  findByName_none_of_forall₂
    (R := fun a b => Nonempty (R a b))
    (getName₁ := getName₁)
    (getName₂ := getName₂)
    (fun hdata => hdata.elim hname)
    (forall2Data_to_forall2 hrel (fun _ _ hr => ⟨hr⟩))
    h

/-- Transport a successful left-list lookup to a right-list lookup while
preserving the pointwise data artifact. -/
def findByName_some_of_forall2Data
    {xs : List α} {ys : List β} {key : Identifier} {x : α}
    (hname : ∀ {a b}, R a b → getName₁ a = getName₂ b)
    (hrel : Forall2Data R xs ys)
    (h : findByName getName₁ xs key = some x) :
    FindByNameForwardData R getName₂ ys key x :=
  match hrel with
  | .nil => by
      simp [findByName] at h
  | @Forall2Data.cons _ _ _ a b as bs hr hrelTail =>
      if hhead : getName₁ a = key then
        have hx : a = x := by
          simpa [findByName, hhead] using h
        have hhead₂ : getName₂ b = key :=
          (hname hr).symm.trans hhead
        { value := b
          found := by simp [findByName, hhead₂]
          related := by simpa [hx] using hr }
      else
        have hhead₂ : getName₂ b ≠ key :=
          fun hEq => hhead ((hname hr).trans hEq)
        have htailLookup : findByName getName₁ as key = some x := by
          simpa [findByName, hhead] using h
        let tail :
            FindByNameForwardData R getName₂ bs key x :=
          findByName_some_of_forall2Data
            (xs := as)
            (ys := bs)
            hname
            hrelTail
            htailLookup
        { value := tail.value
          found := by simpa [findByName, hhead₂] using tail.found
          related := tail.related }

/-- Transport a successful right-list lookup back to a left-list lookup while
preserving the pointwise data artifact. Derived from
`findByName_some_of_forall2Data` by swapping sides of the pointwise relation
through `Forall2Data.symm`. -/
def findByName_some_right_of_forall2Data
    {xs : List α} {ys : List β} {key : Identifier} {y : β}
    (hname : ∀ {a b}, R a b → getName₁ a = getName₂ b)
    (hrel : Forall2Data R xs ys)
    (h : findByName getName₂ ys key = some y) :
    FindByNameReverseData R getName₁ xs key y :=
  let forward :=
    findByName_some_of_forall2Data
      (R := fun b a => R a b)
      (getName₁ := getName₂)
      (getName₂ := getName₁)
      (fun hr => (hname hr).symm)
      hrel.symm
      h
  { value := forward.value
    found := forward.found
    related := forward.related }

end Forall2DataLookup

/-- Generic member lookup by following a list of class names in order. -/
def findMemberInHierarchy
    (findClass : CT → Identifier → Option C)
    (getMembers : C → List M)
    (getName : M → Identifier) :
    CT → List Identifier → Identifier → Option M
  | _, [], _ => none
  | ct, cname :: rest, memberName =>
      match findClass ct cname with
      | none => findMemberInHierarchy findClass getMembers getName ct rest memberName
      | some cls =>
          match findByName getName (getMembers cls) memberName with
          | some member => some member
          | none => findMemberInHierarchy findClass getMembers getName ct rest memberName

section Lookup

variable {CT C M : Type}
  {findClass : CT → Identifier → Option C}
  {getMembers : C → List M}
  {getName : M → Identifier}
  {ct : CT} {hierarchy : List Identifier} {memberName : Identifier} {member : M}

/-- Successful hierarchy lookup returns a member from some class in the hierarchy. -/
theorem findMemberInHierarchy_provenance
    (h : findMemberInHierarchy findClass getMembers getName ct hierarchy memberName = some member) :
    ∃ cname cls, cname ∈ hierarchy ∧ findClass ct cname = some cls ∧ member ∈ getMembers cls := by
  induction hierarchy with
  | nil => simp [findMemberInHierarchy] at h
  | cons cname rest ih =>
      cases hfind : findClass ct cname with
      | none =>
          obtain ⟨dname, dcls, hmem, hclass, hmember⟩ :=
            ih (by simpa [findMemberInHierarchy, hfind] using h)
          exact ⟨dname, dcls, .tail _ hmem, hclass, hmember⟩
      | some cls =>
          cases hmember : findByName getName (getMembers cls) memberName with
          | none =>
              obtain ⟨dname, dcls, hmem, hclass, hmember'⟩ :=
                ih (by simpa [findMemberInHierarchy, hfind, hmember] using h)
              exact ⟨dname, dcls, .tail _ hmem, hclass, hmember'⟩
          | some _ =>
              simp [findMemberInHierarchy, hfind, hmember] at h
              subst h
              exact ⟨cname, cls, .head _, hfind, findByName_mem hmember⟩

/-- Successful hierarchy lookup preserves the queried member name. -/
theorem findMemberInHierarchy_name
    (h : findMemberInHierarchy findClass getMembers getName ct hierarchy memberName = some member) :
    getName member = memberName := by
  induction hierarchy with
  | nil => simp [findMemberInHierarchy] at h
  | cons cname rest ih =>
      cases hfind : findClass ct cname with
      | none => exact ih (by simpa [findMemberInHierarchy, hfind] using h)
      | some cls =>
          cases hmember : findByName getName (getMembers cls) memberName with
          | none => exact ih (by simpa [findMemberInHierarchy, hfind, hmember] using h)
          | some _ =>
              simp [findMemberInHierarchy, hfind, hmember] at h
              subst h
              exact findByName_name hmember

/-- If a class in the hierarchy contains a member with the queried name,
    hierarchy lookup succeeds somewhere along the path. -/
theorem findMemberInHierarchy_exists_of_mem {cname : Identifier} {cls : C}
    (hmem : cname ∈ hierarchy)
    (hclass : findClass ct cname = some cls)
    (hmember : member ∈ getMembers cls)
    (hname : getName member = memberName) :
    ∃ member',
      findMemberInHierarchy findClass getMembers getName ct hierarchy memberName = some member' := by
  induction hierarchy with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · cases hlookup : findByName getName (getMembers cls) memberName with
        | none => exact absurd hname (findByName_eq_none_iff.mp hlookup member hmember)
        | some member' => exact ⟨member', by simp [findMemberInHierarchy, hclass, hlookup]⟩
      · obtain ⟨member', hlookupRest⟩ := ih hmemRest
        cases hhead : findClass ct head with
        | none => exact ⟨member', by simp [findMemberInHierarchy, hhead, hlookupRest]⟩
        | some headCls =>
            cases hlookupHead : findByName getName (getMembers headCls) memberName with
            | some member'' =>
                exact ⟨member'', by simp [findMemberInHierarchy, hhead, hlookupHead]⟩
            | none =>
                exact ⟨member', by simp [findMemberInHierarchy, hhead, hlookupHead, hlookupRest]⟩

end Lookup

section Transport

variable {CT₁ CT₂ C₁ C₂ M₁ M₂ : Type}
  {findClass₁ : CT₁ → Identifier → Option C₁}
  {findClass₂ : CT₂ → Identifier → Option C₂}
  {getMembers₁ : C₁ → List M₁} {getMembers₂ : C₂ → List M₂}
  {getName₁ : M₁ → Identifier} {getName₂ : M₂ → Identifier}
  {ct₁ : CT₁} {ct₂ : CT₂}
  {memberName : Identifier}
  {RClass : C₁ → C₂ → Prop}

/-- Transport successful hierarchy lookup across any relation that preserves
    class lookup and per-class member lookup. -/
theorem findMemberInHierarchy_transport {RMember : M₁ → M₂ → Prop} {m₁ : M₁}
    (classNone :
      ∀ {cname}, findClass₁ ct₁ cname = none → findClass₂ ct₂ cname = none)
    (classSome :
      ∀ {cname c₁}, findClass₁ ct₁ cname = some c₁ →
        ∃ c₂, findClass₂ ct₂ cname = some c₂ ∧ RClass c₁ c₂)
    (memberNone :
      ∀ {c₁ c₂}, RClass c₁ c₂ →
        findByName getName₁ (getMembers₁ c₁) memberName = none →
        findByName getName₂ (getMembers₂ c₂) memberName = none)
    (memberSome :
      ∀ {c₁ c₂ x₁}, RClass c₁ c₂ →
        findByName getName₁ (getMembers₁ c₁) memberName = some x₁ →
        ∃ x₂, findByName getName₂ (getMembers₂ c₂) memberName = some x₂ ∧ RMember x₁ x₂)
    (hfind :
      findMemberInHierarchy findClass₁ getMembers₁ getName₁ ct₁ hierarchy memberName = some m₁) :
    ∃ m₂,
      findMemberInHierarchy findClass₂ getMembers₂ getName₂ ct₂ hierarchy memberName = some m₂ ∧
        RMember m₁ m₂ := by
  induction hierarchy with
  | nil => simp [findMemberInHierarchy] at hfind
  | cons cname rest ih =>
      cases hfc : findClass₁ ct₁ cname with
      | none =>
          obtain ⟨m₂, hfind₂, hm⟩ := ih (by simpa [findMemberInHierarchy, hfc] using hfind)
          exact ⟨m₂, by simpa [findMemberInHierarchy, classNone hfc] using hfind₂, hm⟩
      | some c₁ =>
          obtain ⟨c₂, hfc₂, hc⟩ := classSome hfc
          cases hfm : findByName getName₁ (getMembers₁ c₁) memberName with
          | some x₁ =>
              obtain ⟨x₂, hfm₂, hm⟩ := memberSome hc hfm
              have hxEq : x₁ = m₁ := by
                simpa [findMemberInHierarchy, hfc, hfm] using hfind
              exact ⟨x₂, by simp [findMemberInHierarchy, hfc₂, hfm₂], hxEq ▸ hm⟩
          | none =>
              obtain ⟨m₂, hfind₂, hm⟩ :=
                ih (by simpa [findMemberInHierarchy, hfc, hfm] using hfind)
              exact ⟨m₂, by
                simpa [findMemberInHierarchy, hfc₂, memberNone hc hfm] using hfind₂, hm⟩

/-- Transport failed hierarchy lookup across any relation that preserves
    class lookup and per-class member lookup failure. -/
theorem findMemberInHierarchy_none_transport
    (classNone :
      ∀ {cname}, findClass₁ ct₁ cname = none → findClass₂ ct₂ cname = none)
    (classSome :
      ∀ {cname c₁}, findClass₁ ct₁ cname = some c₁ →
        ∃ c₂, findClass₂ ct₂ cname = some c₂ ∧ RClass c₁ c₂)
    (memberNone :
      ∀ {c₁ c₂}, RClass c₁ c₂ →
        findByName getName₁ (getMembers₁ c₁) memberName = none →
        findByName getName₂ (getMembers₂ c₂) memberName = none)
    (hfind :
      findMemberInHierarchy findClass₁ getMembers₁ getName₁ ct₁ hierarchy memberName = none) :
    findMemberInHierarchy findClass₂ getMembers₂ getName₂ ct₂ hierarchy memberName = none := by
  induction hierarchy with
  | nil => simp [findMemberInHierarchy]
  | cons cname rest ih =>
      cases hfc : findClass₁ ct₁ cname with
      | none =>
          have hrest := ih (by simpa [findMemberInHierarchy, hfc] using hfind)
          simpa [findMemberInHierarchy, classNone hfc] using hrest
      | some c₁ =>
          obtain ⟨c₂, hfc₂, hc⟩ := classSome hfc
          cases hfm : findByName getName₁ (getMembers₁ c₁) memberName with
          | some _ =>
              simp [findMemberInHierarchy, hfc, hfm] at hfind
          | none =>
              have hrest := ih (by simpa [findMemberInHierarchy, hfc, hfm] using hfind)
              simpa [findMemberInHierarchy, hfc₂, memberNone hc hfm] using hrest

end Transport

section TransportData

variable {CT₁ CT₂ C₁ C₂ M₁ M₂ : Type}
  {findClass₁ : CT₁ → Identifier → Option C₁}
  {findClass₂ : CT₂ → Identifier → Option C₂}
  {getMembers₁ : C₁ → List M₁} {getMembers₂ : C₂ → List M₂}
  {getName₁ : M₁ → Identifier} {getName₂ : M₂ → Identifier}
  {ct₁ : CT₁} {ct₂ : CT₂}
  {hierarchy : List Identifier} {memberName : Identifier}

/-- Constructive result for transporting a class lookup into the target table. -/
structure RelatedClassLookupData
    (findClass₂ : CT₂ → Identifier → Option C₂)
    (ct₂ : CT₂)
    (cname : Identifier)
    (RClass : C₁ → C₂ → Type u)
    (c₁ : C₁) where
  /-- The class found in the target table. -/
  class2 : C₂
  /-- The target-table lookup equality for `class2`. -/
  found : findClass₂ ct₂ cname = some class2
  /-- The data-bearing relation between the source and target classes. -/
  related : RClass c₁ class2

/-- Constructive result for transporting a member lookup into the target class. -/
structure RelatedMemberLookupData
    (getMembers₂ : C₂ → List M₂)
    (getName₂ : M₂ → Identifier)
    (memberName : Identifier)
    (RMember : M₁ → M₂ → Type v)
    (c₂ : C₂)
    (m₁ : M₁) where
  /-- The member found in the target class member list. -/
  member2 : M₂
  /-- The target member-list lookup equality for `member2`. -/
  found : findByName getName₂ (getMembers₂ c₂) memberName = some member2
  /-- The data-bearing relation between the source and target members. -/
  related : RMember m₁ member2

/-- Constructive result for transporting a hierarchy member lookup into the
target hierarchy. -/
structure RelatedHierarchyLookupData
    (findClass₂ : CT₂ → Identifier → Option C₂)
    (getMembers₂ : C₂ → List M₂)
    (getName₂ : M₂ → Identifier)
    (ct₂ : CT₂)
    (hierarchy : List Identifier)
    (memberName : Identifier)
    (RMember : Identifier → M₁ → M₂ → Type v)
    (m₁ : M₁) where
  /-- The hierarchy entry whose member list produced `member2`. -/
  definingClassName : Identifier
  /-- The member found by transported target hierarchy lookup. -/
  member2 : M₂
  /-- The target hierarchy lookup equality for `member2`. -/
  found :
    findMemberInHierarchy findClass₂ getMembers₂ getName₂
      ct₂ hierarchy memberName = some member2
  /-- The data-bearing relation for the source member, target member, and
      defining class name. -/
  related : RMember definingClassName m₁ member2

/-- Transport a successful hierarchy member lookup through data-bearing class
and member lookup transports, preserving the defining class name for the
returned member artifact. -/
def findMemberInHierarchy_transportData
    {RClass : C₁ → C₂ → Type u}
    {RMember : Identifier → M₁ → M₂ → Type v}
    {m₁ : M₁}
    (hierarchy : List Identifier)
    (classNone :
      ∀ {cname}, findClass₁ ct₁ cname = none → findClass₂ ct₂ cname = none)
    (classSome :
      ∀ {cname c₁}, findClass₁ ct₁ cname = some c₁ →
        RelatedClassLookupData findClass₂ ct₂ cname RClass c₁)
    (memberNone :
      ∀ {c₁ c₂}, RClass c₁ c₂ →
        findByName getName₁ (getMembers₁ c₁) memberName = none →
        findByName getName₂ (getMembers₂ c₂) memberName = none)
    (memberSome :
      ∀ {cname c₁ c₂ x₁}, RClass c₁ c₂ →
        findClass₁ ct₁ cname = some c₁ →
        findByName getName₁ (getMembers₁ c₁) memberName = some x₁ →
        RelatedMemberLookupData getMembers₂ getName₂ memberName (RMember cname) c₂ x₁)
    (hfind :
      findMemberInHierarchy findClass₁ getMembers₁ getName₁
        ct₁ hierarchy memberName = some m₁) :
    RelatedHierarchyLookupData
      findClass₂ getMembers₂ getName₂ ct₂ hierarchy memberName RMember m₁ :=
  match hierarchy with
  | [] => by
      simp [findMemberInHierarchy] at hfind
  | cname :: rest =>
      match hclass : findClass₁ ct₁ cname with
      | none =>
          let restData :
              RelatedHierarchyLookupData
                findClass₂ getMembers₂ getName₂ ct₂ rest memberName RMember m₁ :=
            findMemberInHierarchy_transportData
              rest
              (classNone := classNone)
              (classSome := classSome)
              (memberNone := memberNone)
              (memberSome := memberSome)
              (hfind := by simpa [findMemberInHierarchy, hclass] using hfind)
          { definingClassName := restData.definingClassName
            member2 := restData.member2
            found := by
              simpa [findMemberInHierarchy, classNone hclass] using restData.found
            related := restData.related }
      | some c₁ =>
          let classLookup := classSome hclass
          match hmember : findByName getName₁ (getMembers₁ c₁) memberName with
          | none =>
              let restData :
                  RelatedHierarchyLookupData
                    findClass₂ getMembers₂ getName₂ ct₂ rest memberName RMember m₁ :=
                findMemberInHierarchy_transportData
                  rest
                  (classNone := classNone)
                  (classSome := classSome)
                  (memberNone := memberNone)
                  (memberSome := memberSome)
                  (hfind := by simpa [findMemberInHierarchy, hclass, hmember] using hfind)
              { definingClassName := restData.definingClassName
                member2 := restData.member2
                found := by
                  simpa [findMemberInHierarchy, classLookup.found,
                    memberNone classLookup.related hmember] using restData.found
                related := restData.related }
          | some x₁ =>
              let memberLookup := memberSome classLookup.related hclass hmember
              have hx : x₁ = m₁ := by
                simpa [findMemberInHierarchy, hclass, hmember] using hfind
              { definingClassName := cname
                member2 := memberLookup.member2
                found := by
                  simp [findMemberInHierarchy, classLookup.found, memberLookup.found]
                related := by simpa [hx] using memberLookup.related }

end TransportData

/-- Constructive lookup witness for a class name together with its MRO. -/
structure ClassLookupWitnessOf
    (findClass : CT → Identifier → Option C)
    (computeMro : CT → C → List Identifier → Prop)
    (ct : CT)
    (cname : Identifier) where
  cls : C
  mro : List Identifier
  hfind : findClass ct cname = some cls
  hmro : computeMro ct cls mro

/-- Constructive MRO witness for an already chosen class. -/
structure ClassMroWitnessOf
    (computeMro : CT → C → List Identifier → Prop)
    (ct : CT)
    (cls : C) where
  mro : List Identifier
  hmro : computeMro ct cls mro

/-- Constructive witness that a distinguished root class exists and has no explicit bases. -/
structure ObjectExistsWitnessOf
    (findClass : CT → Identifier → Option C)
    (getBases : C → List Identifier)
    (rootName : Identifier)
    (ct : CT) where
  cls : C
  hfind : findClass ct rootName = some cls
  hbases : getBases cls = []

theorem ClassLookupWitnessOf.exists
    (w : ClassLookupWitnessOf findClass computeMro ct cname) :
    ∃ cls mro, findClass ct cname = some cls ∧ computeMro ct cls mro :=
  ⟨w.cls, w.mro, w.hfind, w.hmro⟩

theorem ClassLookupWitnessOf.exists_find
    (w : ClassLookupWitnessOf findClass computeMro ct cname) :
    ∃ cls, findClass ct cname = some cls :=
  ⟨w.cls, w.hfind⟩

theorem ClassMroWitnessOf.exists
    (w : ClassMroWitnessOf computeMro ct cls) :
    ∃ mro, computeMro ct cls mro :=
  ⟨w.mro, w.hmro⟩

theorem ClassLookupWitnessOf.subsingleton
    (hdet :
      ∀ {cls mro₁ mro₂}, computeMro ct cls mro₁ → computeMro ct cls mro₂ → mro₁ = mro₂) :
    Subsingleton (ClassLookupWitnessOf findClass computeMro ct cname) :=
  ⟨fun ⟨cls₁, mro₁, hfind₁, hmro₁⟩ ⟨cls₂, mro₂, hfind₂, hmro₂⟩ => by
    have hcls : cls₁ = cls₂ := by simpa [hfind₁] using hfind₂
    subst hcls
    have hmro : mro₁ = mro₂ := hdet hmro₁ hmro₂
    subst hmro
    congr 1 <;> exact Subsingleton.elim _ _⟩

theorem ClassMroWitnessOf.subsingleton
    (hdet :
      ∀ {mro₁ mro₂}, computeMro ct cls mro₁ → computeMro ct cls mro₂ → mro₁ = mro₂) :
    Subsingleton (ClassMroWitnessOf computeMro ct cls) :=
  ⟨fun ⟨mro₁, hmro₁⟩ ⟨mro₂, hmro₂⟩ => by
    have hmro : mro₁ = mro₂ := hdet hmro₁ hmro₂
    subst hmro
    congr 1 <;> exact Subsingleton.elim _ _⟩

theorem ObjectExistsWitnessOf.subsingleton :
    Subsingleton (ObjectExistsWitnessOf findClass getBases rootName ct) :=
  ⟨fun ⟨cls₁, hfind₁, _⟩ ⟨cls₂, hfind₂, _⟩ => by
    have hcls : cls₁ = cls₂ := by simpa [hfind₁] using hfind₂
    subst hcls
    congr 1 <;> exact Subsingleton.elim _ _⟩

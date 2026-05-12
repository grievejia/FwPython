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

/-- Generic class lookup for class tables built from `ClassDecl`. -/
def findClass {Method : Type} (ct : ClassTableDecl Method) (cname : Identifier) :
    Option (ClassDecl Method) :=
  findByName ClassDecl.name ct cname

/-- Generic method lookup for method lists built from `MethodDecl`. -/
abbrev findMethodInList {Ty : Type} {Expr : Type}
    (ms : List (MethodDecl Ty Expr)) (mname : Identifier) :
    Option (MethodDecl Ty Expr) :=
  findByName MethodDecl.name ms mname

theorem findByName_mem
    (h : findByName getName xs key = some x) :
    x ∈ xs := by
  induction xs with
  | nil =>
      simp [findByName] at h
  | cons y ys ih =>
      unfold findByName at h
      split at h <;> simp_all

theorem findByName_name
    (h : findByName getName xs key = some x) :
    getName x = key := by
  induction xs with
  | nil =>
      simp [findByName] at h
  | cons y ys ih =>
      unfold findByName at h
      split at h <;> simp_all

theorem findByName_eq_none_iff :
    findByName getName xs key = none ↔
      ∀ x, x ∈ xs → getName x ≠ key := by
  induction xs with
  | nil =>
      simp [findByName]
  | cons y ys ih =>
      by_cases h : getName y = key
      · simp [findByName, h]
      · simp [findByName, h, ih]

theorem findClass_mem
    (h : findClass ct cname = some c) : c ∈ ct :=
  findByName_mem h

theorem findClass_name
    (h : findClass ct cname = some c) : c.name = cname :=
  findByName_name h

theorem findMethodInList_mem
    (h : findMethodInList ms mname = some m) : m ∈ ms :=
  findByName_mem h

theorem findMethodInList_name
    (h : findMethodInList ms mname = some m) : m.name = mname :=
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

/-- Successful lookup transports across any pointwise list relation that
preserves member names. -/
theorem findByName_some_of_forall₂
    (hname : ∀ {a b}, R a b → getName₁ a = getName₂ b)
    (hrel : Forall₂ R xs ys)
    (h : findByName getName₁ xs key = some x) :
    ∃ y, findByName getName₂ ys key = some y ∧ R x y := by
  induction hrel generalizing key x with
  | nil => simp [findByName] at h
  | @cons a b as bs hr _ ih =>
      by_cases hhead : getName₁ a = key
      · simp [findByName, hhead] at h
        subst h
        exact ⟨b, by simp [findByName, (hname hr).symm.trans hhead], hr⟩
      · have hhead₂ : getName₂ b ≠ key :=
          fun hEq => hhead ((hname hr).trans hEq)
        obtain ⟨y, hy, hxy⟩ := ih (by simpa [findByName, hhead] using h)
        exact ⟨y, by simpa [findByName, hhead₂] using hy, hxy⟩

end Forall2Lookup

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
  {hierarchy : List Identifier} {memberName : Identifier}
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

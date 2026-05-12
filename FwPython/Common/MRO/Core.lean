import FwPython.Common.ClassModel
import FwPython.Static.MRO.C3
import FwPython.Builtins

/-! # MRO core parameterized over the method payload. -/

/-- Effective base classes, accounting for implicit Object inheritance.
    Classes with no explicit bases implicitly inherit from Object unless
    they are Object itself. -/
def ClassDecl.resolvedBases {Method : Type} (c : ClassDecl Method) : List Identifier :=
  if c.baseClasses.isEmpty then
    if c.name = objectClass then [] else [objectClass]
  else
    c.baseClasses

/-- `resolvedBases = []` exactly for `Object` with no explicit bases. -/
theorem resolvedBases_nil_iff {Method : Type} (c : ClassDecl Method) :
    c.resolvedBases = [] ↔ c.baseClasses = [] ∧ c.name = objectClass := by
  unfold ClassDecl.resolvedBases
  cases c.baseClasses with
  | nil => simp [objectClass]
  | cons _ _ => simp

mutual
/-- Each base name resolves to the corresponding parent MRO entry. -/
inductive AllParentMros {Method : Type} :
    ClassTableDecl Method → List Identifier → List (List Identifier) → Prop where
  | nil : AllParentMros ct [] []
  | cons :
      findClass ct bname = some bcls →
      ComputeMro ct bcls mro →
      AllParentMros ct rest restMros →
      AllParentMros ct (bname :: rest) (mro :: restMros)

/-- MRO witness obtained by recursively merging parent MROs with C3. -/
inductive ComputeMro {Method : Type} :
    ClassTableDecl Method → ClassDecl Method → List Identifier → Prop where
  | root :
      c.resolvedBases = [] →
      ComputeMro ct c [c.name]
  | step :
      c.resolvedBases = bases →
      bases ≠ [] →
      AllParentMros ct bases parentMros →
      c3Merge (parentMros ++ [bases]) = some mergedSuffix →
      ComputeMro ct c (c.name :: mergedSuffix)
end

theorem allParentMros_length {Method : Type}
    {ct : ClassTableDecl Method}
    {bases : List Identifier}
    {parentMros : List (List Identifier)}
    (h : AllParentMros (Method := Method) ct bases parentMros) :
    bases.length = parentMros.length :=
  AllParentMros.rec
    (motive_1 := fun _ bases parentMros _ => bases.length = parentMros.length)
    (motive_2 := fun _ _ _ _ => True)
    (fun {_} => rfl)
    (fun _ _ _ _ ih => by simp [ih])
    (fun _ => trivial)
    (fun _ _ _ _ _ => trivial)
    h

theorem allParentMros_mem {Method : Type}
    {ct : ClassTableDecl Method}
    {bases : List Identifier}
    {parentMros : List (List Identifier)}
    {bname : Identifier}
    (h : AllParentMros (Method := Method) ct bases parentMros)
    (hbname : bname ∈ bases) :
    ∃ bcls pmro, findClass ct bname = some bcls ∧
      ComputeMro ct bcls pmro ∧ pmro ∈ parentMros := by
  have key := AllParentMros.rec
    (motive_1 := fun ct bases parentMros _ =>
      ∀ bname, bname ∈ bases →
      ∃ bcls pmro, findClass ct bname = some bcls ∧
        ComputeMro ct bcls pmro ∧ pmro ∈ parentMros)
    (motive_2 := fun _ _ _ _ => True)
    (fun bname' hm => absurd hm List.not_mem_nil)
    (fun hfind hmro _ _ ih bname' hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ⟨_, _, hfind, hmro, List.Mem.head _⟩
      · obtain ⟨bcls, pmro, hf, hm, hpmem⟩ := ih bname' hmem'
        exact ⟨bcls, pmro, hf, hm, List.mem_cons_of_mem _ hpmem⟩)
    (fun _ => trivial)
    (fun _ _ _ _ _ => trivial)
    h
  exact key bname hbname

/-- A class always appears in its own MRO. -/
theorem mro_self_mem {Method : Type}
    {ct : ClassTableDecl Method}
    {c : ClassDecl Method}
    {mro : List Identifier}
    (hmro : ComputeMro (Method := Method) ct c mro) :
    c.name ∈ mro := by
  cases hmro <;> exact List.Mem.head _

theorem findClass_self {Method : Type}
    {ct : ClassTableDecl Method}
    {cname : Identifier}
    {c : ClassDecl Method}
    (h : findClass (Method := Method) ct cname = some c) :
    findClass ct c.name = some c := by
  rw [findClass_name h]
  exact h

/-- Unique class names imply lookup succeeds on any member of the table. -/
theorem findClass_of_mem {Method : Type}
    {ct : ClassTableDecl Method}
    {c : ClassDecl Method}
    (huniq : ∀ c₁ c₂, c₁ ∈ ct → c₂ ∈ ct → c₁.name = c₂.name → c₁ = c₂)
    (hmem : c ∈ ct) :
    findClass (Method := Method) ct c.name = some c := by
  induction ct with
  | nil =>
      cases hmem
  | cons c' ct ih =>
      cases hmem with
      | head =>
          simp [findClass, findByName]
      | tail _ hmemTail =>
          have huniq' :
              ∀ c₁ c₂,
                c₁ ∈ ct → c₂ ∈ ct → c₁.name = c₂.name → c₁ = c₂ := by
            intro c₁ c₂ hc₁ hc₂ hname
            exact huniq c₁ c₂ (.tail _ hc₁) (.tail _ hc₂) hname
          by_cases hname : c'.name = c.name
          · have hc' : c' = c := huniq c' c (.head _) (.tail _ hmemTail) hname
            simp [findClass, findByName, hc']
          · simpa [findClass, findByName, hname] using ih huniq' hmemTail

/-- Determinism of C3-based MRO construction. -/
theorem determinism {Method : Type}
    {ct : ClassTableDecl Method}
    {c : ClassDecl Method}
    {mro₁ mro₂ : List Identifier}
    (h1 : ComputeMro (Method := Method) ct c mro₁)
    (h2 : ComputeMro ct c mro₂) :
    mro₁ = mro₂ := by
  have key := ComputeMro.rec
    (motive_1 := fun ct bases pms _ =>
      ∀ pms₂, AllParentMros ct bases pms₂ → pms = pms₂)
    (motive_2 := fun ct c mro _ =>
      ∀ mro₂, ComputeMro ct c mro₂ → mro = mro₂)
    (fun pms₂ hall₂ => by cases hall₂; rfl)
    (fun hfind _ _ ih_mro ih_rest pms₂ hall₂ => by
      cases hall₂ with
      | cons hfind₂ hmro₂ hall₂ =>
        rw [hfind] at hfind₂
        cases hfind₂
        congr 1
        · exact ih_mro _ hmro₂
        · exact ih_rest _ hall₂)
    (fun hnil mro₂ hmro₂ => by
      cases hmro₂ with
      | root => rfl
      | step hbases₂ hne₂ =>
        rw [hnil] at hbases₂
        exact absurd hbases₂.symm hne₂)
    (fun hbases hne _ hmerge ih_parents mro₂ hmro₂ => by
      cases hmro₂ with
      | root hnil₂ =>
        rw [hbases] at hnil₂
        exact (hne hnil₂).elim
      | step hbases₂ _ hall₂ hmerge₂ =>
        rw [hbases] at hbases₂
        cases hbases₂
        rw [ih_parents _ hall₂] at hmerge
        rw [hmerge] at hmerge₂
        cases hmerge₂
        rfl)
    h1
  exact key mro₂ h2

/-- Find a method by searching each class in the MRO in order. -/
abbrev findMethodInMro {Ty : Type} {Expr : Type}
    (ct : ClassTableDecl (MethodDecl Ty Expr)) (mro : List Identifier)
    (mname : Identifier) : Option (MethodDecl Ty Expr) :=
  findMemberInHierarchy findClass ClassDecl.methods MethodDecl.name ct mro mname

/-- Lookup result of MRO-based method resolution for a fixed MRO predicate. -/
def MethodInReceiverMroOf {Ty : Type} {Expr : Type}
    (computeMro :
      ClassTableDecl (MethodDecl Ty Expr) →
      ClassDecl (MethodDecl Ty Expr) →
      List Identifier → Prop)
    (ct : ClassTableDecl (MethodDecl Ty Expr))
    (recvClass : Identifier)
    (m : MethodDecl Ty Expr) : Prop :=
  ∃ recvCls mro,
    findClass ct recvClass = some recvCls ∧
    computeMro ct recvCls mro ∧
    findMethodInMro ct mro m.name = some m

/-- Successful MRO lookup returns a method from some class in the MRO. -/
theorem findMethodInMro_provenance {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {mro : List Identifier} {methodName : Identifier} {m : MethodDecl Ty Expr}
    (h : findMethodInMro (Ty := Ty) (Expr := Expr) ct mro methodName = some m) :
    ∃ dname d, dname ∈ mro ∧ findClass ct dname = some d ∧ m ∈ d.methods :=
  findMemberInHierarchy_provenance h

/-- Successful MRO lookup preserves the searched method name. -/
theorem findMethodInMro_name {Ty : Type} {Expr : Type}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {mro : List Identifier} {mname : Identifier} {m : MethodDecl Ty Expr}
    (h : findMethodInMro (Ty := Ty) (Expr := Expr) ct mro mname = some m) :
    m.name = mname :=
  findMemberInHierarchy_name h

/-- Build a receiver-MRO witness from a concrete successful lookup. -/
theorem method_in_receiver_mro_of_lookup {Ty : Type} {Expr : Type}
    {computeMro :
      ClassTableDecl (MethodDecl Ty Expr) →
      ClassDecl (MethodDecl Ty Expr) →
      List Identifier → Prop}
    {ct : ClassTableDecl (MethodDecl Ty Expr)}
    {recvClass : Identifier} {recvCls : ClassDecl (MethodDecl Ty Expr)}
    {recvMro : List Identifier} {attrName : Identifier} {m : MethodDecl Ty Expr}
    (hfind : findClass ct recvClass = some recvCls)
    (hmro : computeMro ct recvCls recvMro)
    (hlookup : findMethodInMro ct recvMro attrName = some m) :
    MethodInReceiverMroOf computeMro ct recvClass m :=
  ⟨recvCls, recvMro, hfind, hmro, findMethodInMro_name hlookup ▸ hlookup⟩

/-- Generic method-signature lookup through an MRO predicate. -/
def FindMethodTypeOf {Ty : Type} {Expr : Type}
    (computeMro :
      ClassTableDecl (MethodDecl Ty Expr) →
      ClassDecl (MethodDecl Ty Expr) →
      List Identifier → Prop)
    (ct : ClassTableDecl (MethodDecl Ty Expr))
    (cname : Identifier)
    (methodName : Identifier)
    (paramTy returnTy : Ty) : Prop :=
  ∃ c mro m,
    findClass ct cname = some c ∧
    computeMro ct c mro ∧
    findMethodInMro ct mro methodName = some m ∧
    m.paramTy = paramTy ∧
    m.returnTy = returnTy

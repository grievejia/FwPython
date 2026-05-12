import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.Value.Typing

/-! ## Heap well-formedness -/

/-- The heap is consistent with the class table. -/
structure HeapWellFormed (ct : ClassTable) (h : Heap) : Prop where
  idsBounded : h.IdsBounded
  classesExist : ∀ oid obj, h.lookup oid = some obj →
    ∃ c mro, findClass ct obj.className = some c ∧ ComputeMro ct c mro
  initialNone : h.lookup noneOid = some ⟨noneClass, .ordinary⟩
  initialTrue : h.lookup trueOid = some ⟨boolClass, .ordinary⟩
  initialFalse : h.lookup falseOid = some ⟨boolClass, .ordinary⟩
  boolExhaustive : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
    oid = trueOid ∨ oid = falseOid
  /-- Bound-method payload only appears on BoundMethod-class objects. -/
  payloadBoundMethod : ∀ oid cname recvOid m,
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    cname = boundMethodClass
  /-- Bound-method receivers exist in the heap with valid method provenance. -/
  payloadReceiverValid : ∀ oid cname recvOid m,
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    ∃ recvObj, h.lookup recvOid = some recvObj ∧
      MethodInReceiverMro ct recvObj.className m

/-! ## Well-formed class table -/

/-- Constructive lookup witness for a class name together with its MRO. -/
abbrev ClassLookupWitness (ct : ClassTable) (cname : Identifier) :=
  ClassLookupWitnessOf findClass ComputeMro ct cname

/-- Constructive MRO witness for an already chosen class. -/
abbrev ClassMroWitness (ct : ClassTable) (cls : Class) :=
  ClassMroWitnessOf ComputeMro ct cls

/-- Constructive witness that `Object` exists and has no explicit bases. -/
abbrev ObjectExistsWitness (ct : ClassTable) :=
  ObjectExistsWitnessOf findClass ClassDecl.baseClasses objectClass ct

/-- Every method body typechecks under its declared signature. -/
def AllMethodsWellTyped (ct : ClassTable) : Prop :=
  ∀ cname c m,
    findClass ct cname = some c →
    m ∈ c.methods →
    HasType ct
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy

/-- Method overrides satisfy the Liskov substitution principle:
    contravariant parameters, covariant returns. -/
def LiskovCondition (ct : ClassTable) : Prop :=
  ∀ cname aname c_cls a_cls mro_c mro_a methodName m_c m_a,
    findClass ct cname = some c_cls →
    ComputeMro ct c_cls mro_c →
    aname ∈ mro_c →
    findClass ct aname = some a_cls →
    ComputeMro ct a_cls mro_a →
    findMethodInMro ct mro_c methodName = some m_c →
    findMethodInMro ct mro_a methodName = some m_a →
    IsSubtype ct m_a.paramTy m_c.paramTy ∧
      IsSubtype ct m_c.returnTy m_a.returnTy

/-- A well-formed class table has well-typed methods, Liskov-compatible overrides,
    and properly configured built-in classes. -/
structure WellFormedClassTable (ct : ClassTable) where
  allMethodsWellTyped : AllMethodsWellTyped ct
  liskovCondition : LiskovCondition ct
  /-- Bool and NoneType exist in the class table with valid MROs. -/
  boolExists : ClassLookupWitness ct boolClass
  noneExists : ClassLookupWitness ct noneClass
  /-- BoundMethod exists in the class table with a valid MRO. -/
  boundMethodExists : ClassLookupWitness ct boundMethodClass
  /-- No class extends Bool or NoneType — they are leaf classes. -/
  builtinsLeaf : ∀ cname c mro, findClass ct cname = some c →
    ComputeMro ct c mro → boolClass ∈ mro → cname = boolClass
  noneLeaf : ∀ cname c mro, findClass ct cname = some c →
    ComputeMro ct c mro → noneClass ∈ mro → cname = noneClass
  /-- BoundMethod is a leaf class. -/
  boundMethodLeaf : ∀ cname c mro, findClass ct cname = some c →
    ComputeMro ct c mro → boundMethodClass ∈ mro → cname = boundMethodClass
  /-- Every class in the table has a valid MRO (no cycles). -/
  allMrosExist : ∀ cname c, findClass ct cname = some c → ClassMroWitness ct c
  /-- Method names are unique within each class. -/
  allMethodNamesDistinct : ∀ cname c, findClass ct cname = some c →
    List.Nodup (c.methods.map MethodDecl.name)
  /-- Every method signature uses well-formed types. -/
  allMethodSignaturesWellFormed : ∀ cname c m, findClass ct cname = some c →
    m ∈ c.methods → WellFormedTy ct m.paramTy ∧ WellFormedTy ct m.returnTy
  /-- Class names in the class table are unique. -/
  classNamesUnique : ∀ c₁ c₂, c₁ ∈ ct → c₂ ∈ ct → c₁.name = c₂.name → c₁ = c₂
  /-- Direct parent lists are duplicate-free. -/
  baseClassesDistinct : ∀ cname c, findClass ct cname = some c → c.baseClasses.Nodup
  /-- Object exists in the class table and has no explicit base class. -/
  objectExists : ObjectExistsWitness ct

/-- `class_ objectClass` is well-formed under any well-formed class table. -/
theorem wellFormed_object_type (hwf : WellFormedClassTable ct) :
    WellFormedTy ct (.class_ objectClass) := by
  obtain ⟨c, hfind, _⟩ := hwf.objectExists
  exact .class_ hfind (hwf.allMrosExist _ _ hfind).hmro

/-- `class_ boolClass` is well-formed under any well-formed class table. -/
theorem wellFormed_bool_type (hwf : WellFormedClassTable ct) :
    WellFormedTy ct (.class_ boolClass) :=
  .class_ hwf.boolExists.hfind hwf.boolExists.hmro

/-- `class_ noneClass` is well-formed under any well-formed class table. -/
theorem wellFormed_none_type (hwf : WellFormedClassTable ct) :
    WellFormedTy ct (.class_ noneClass) :=
  .class_ hwf.noneExists.hfind hwf.noneExists.hmro

/-! ## Leaf built-in derivations -/

/-- `Bool` is a leaf built-in under any well-formed class table. -/
theorem leafBuiltin_bool (hwf : WellFormedClassTable ct) :
    LeafBuiltin ct boolClass :=
  .bool hwf.builtinsLeaf

/-- `NoneType` is a leaf built-in under any well-formed class table. -/
theorem leafBuiltin_none (hwf : WellFormedClassTable ct) :
    LeafBuiltin ct noneClass :=
  .none hwf.noneLeaf

/-- `BoundMethod` is a leaf built-in under any well-formed class table. -/
theorem leafBuiltin_boundMethod (hwf : WellFormedClassTable ct) :
    LeafBuiltin ct boundMethodClass :=
  .boundMethod hwf.boundMethodLeaf

theorem WellFormedClassTable.allMrosExist_exists (hwf : WellFormedClassTable ct) :
    ∀ cname c, findClass ct cname = some c → ∃ mro, ComputeMro ct c mro :=
  fun _ _ hfind => (hwf.allMrosExist _ _ hfind).exists

theorem WellFormedClassTable.boundMethodExists_find (hwf : WellFormedClassTable ct) :
    ∃ c, findClass ct boundMethodClass = some c :=
  hwf.boundMethodExists.exists_find

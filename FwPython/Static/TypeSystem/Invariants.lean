import FwPython.Static.MRO.Structure
import FwPython.Static.TypeSystem.Typing
import FwPython.Static.TypeSystem.Value.Typing

/-! ## Heap well-formedness -/

/-- The heap is consistent with the class table. -/
structure HeapWellFormed (ct : ClassTable) (h : Heap) : Prop where
  /-- Every allocated object identifier is below the heap allocation frontier. -/
  idsBounded : h.IdsBounded
  /-- Every stored object's class name has a declaration with a successful MRO. -/
  classesExist : ∀ oid obj, h.lookup oid = some obj →
    ∃ c mro, findClass ct obj.className = some c ∧ ComputeMro ct c mro
  /-- The distinguished None identifier contains the ordinary None singleton. -/
  initialNone : h.lookup noneOid = some ⟨noneClass, .ordinary⟩
  /-- The distinguished true identifier contains an ordinary Boolean. -/
  initialTrue : h.lookup trueOid = some ⟨boolClass, .ordinary⟩
  /-- The distinguished false identifier contains an ordinary Boolean. -/
  initialFalse : h.lookup falseOid = some ⟨boolClass, .ordinary⟩
  /-- Every Boolean object is one of the two distinguished Boolean singletons. -/
  boolExhaustive : ∀ oid obj, h.lookup oid = some obj → obj.className = boolClass →
    oid = trueOid ∨ oid = falseOid
  /-- BoundMethod membership identifies exactly the objects with an invokable method payload. -/
  boundMethodShape : ∀ oid obj, h.lookup oid = some obj →
    (obj.className = boundMethodClass ↔
      ∃ receiver method, obj.payload = .boundMethod receiver method)
  /-- Bound-method receivers exist in the heap with valid method provenance. -/
  payloadReceiverValid : ∀ oid cname recvOid m,
    h.lookup oid = some ⟨cname, .boundMethod recvOid m⟩ →
    ∃ recvObj, h.lookup recvOid = some recvObj ∧
      MethodInReceiverMro ct recvObj.className m

/-! ## Well-typed class hierarchy -/

/-- Every own method body in the first declaration found for each class name
typechecks under its declared signature. -/
def AllMethodsWellTyped {ct : ClassTable} (structural : WellFormedClassHierarchy ct) : Prop :=
  ∀ cname c m,
    findClass ct cname = some c →
    m ∈ c.methods →
    HasType structural
      [(m.param, m.paramTy), (m.receiverParam, .class_ cname)]
      m.body
      m.returnTy

/-- Compare the method selected through a class's MRO with the same named method
selected through each ancestor's own MRO. The class's selected method must accept
the ancestor's inputs and have a result type below the ancestor's result type,
whether inherited or declared directly. -/
def LiskovCondition {ct : ClassTable} (structural : WellFormedClassHierarchy ct) : Prop :=
  ∀ cname aname c_cls a_cls mro_c mro_a methodName m_c m_a,
    findClass ct cname = some c_cls →
    ComputeMro ct c_cls mro_c →
    aname ∈ mro_c →
    findClass ct aname = some a_cls →
    ComputeMro ct a_cls mro_a →
    findMethodInMro ct mro_c methodName = some m_c →
    findMethodInMro ct mro_a methodName = some m_a →
    IsSubtype structural m_a.paramTy m_c.paramTy ∧
      IsSubtype structural m_c.returnTy m_a.returnTy

/-- The hierarchy of `ct` together with typed method bodies, compatible MRO-selected
methods, and declaration consistency. The inherited `WellFormedClassHierarchy`
supplies the facts for subtyping; subtyping supports the method typing and
override checks in this record. -/
structure WellTypedClassHierarchy (ct : ClassTable) extends WellFormedClassHierarchy ct where
  /-- In the first declaration found for each class name, every own method body
  has its declared result type when the argument has its declared parameter type
  and the receiver has that declaration's class type. -/
  allMethodsWellTyped : AllMethodsWellTyped toWellFormedClassHierarchy
  /-- The method selected through a class's MRO accepts the input type of the
  method selected through each ancestor's MRO and has a result type below that
  method's result type. -/
  liskovCondition : LiskovCondition toWellFormedClassHierarchy
  /-- In the first declaration found for each class name, method names are distinct.
  This is a source language rule. -/
  allMethodNamesDistinct : ∀ cname c, findClass ct cname = some c →
    List.Nodup (c.methods.map MethodDecl.name)
  /-- In the first declaration found for each class name, every own method
  signature mentions only class names with declarations. -/
  allMethodSignaturesWellFormed : ∀ cname c m, findClass ct cname = some c →
    m ∈ c.methods → WellFormedTy ct m.paramTy ∧ WellFormedTy ct m.returnTy
  /-- Declarations sharing a name agree in their entire class and method data. -/
  classNamesUnique : ∀ c₁ c₂, c₁ ∈ ct → c₂ ∈ ct → c₁.name = c₂.name → c₁ = c₂
  /-- The first declaration found for each class name lists each explicit direct parent at most once. -/
  baseClassesDistinct : ∀ cname c, findClass ct cname = some c → c.baseClasses.Nodup

/-- A method selected from the receiver's MRO has a valid function annotation. -/
theorem methodInReceiverMro_wellFormed (hwf : WellTypedClassHierarchy ct)
    (selected : MethodInReceiverMro ct receiverClass method) :
    WellFormedTy ct (.callable method.paramTy method.returnTy) := by
  obtain ⟨_, _, _, _, methodLookup⟩ := selected
  obtain ⟨owner, declaration, _, classLookup, member⟩ := findMethodInMro_provenance methodLookup
  exact (hwf.allMethodSignaturesWellFormed owner declaration method classLookup member).elim .callable

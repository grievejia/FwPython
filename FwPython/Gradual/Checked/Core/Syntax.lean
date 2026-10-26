import FwPython.Gradual.MRO.Lookup
import FwPython.Gradual.Contracts
import FwPython.Gradual.SourceObligation
import FwPython.Gradual.TypeSystem.CheckedTargetSyntax

/-! # Checked Runtime Vocabulary

Defines the checked target language and runtime objects for the gradual system.
The checked language extends the gradual source with explicit enforcement nodes
(`enforce` against `BoundaryContract`). Blame-capable checked operations carry
the source obligation that the checked machine reports when the operation
rejects a value. -/

/-! ## Checked expressions -/

/-- The checked target language extends the gradual source expressions with:
    - `enforce e target obligation`: runtime type enforcement against the
      compiled contract image of `target`; boundary blame reports `obligation`
    - `dynAttrAccess e attrName obligation`: dynamic attribute access; missing
      attributes report `obligation` instead of producing a raw runtime error
    - `call callee arg paramTy returnTy returnObligation`: ordinary call with
      explicit argument and return targets; the caller-side return boundary
      reports `returnObligation` -/
inductive CheckedExpr : Type where
  | var : Identifier → CheckedExpr
  | new : Identifier → CheckedExpr
  | attrAccess : CheckedExpr → Identifier → CheckedExpr
  | call : CheckedExpr → CheckedExpr →
      (paramTy : CheckedTarget) → (returnTy : CheckedTarget) →
      SourceObligation → CheckedExpr
  | constNone : CheckedExpr
  | constTrue : CheckedExpr
  | constFalse : CheckedExpr
  | cond : CheckedExpr → CheckedExpr → CheckedExpr → CheckedExpr
  | isInstance : Identifier → Identifier → CheckedExpr
  | enforce : (e : CheckedExpr) → (target : CheckedTarget) →
      SourceObligation → CheckedExpr
  | dynAttrAccess : CheckedExpr → Identifier → SourceObligation → CheckedExpr
  deriving DecidableEq, Repr

/-! ## Checked classes -/

/-- A checked runtime method stores lookup names, machine-facing targets,
source obligations for method boundaries, and the checked expression executed
as the method body. -/
structure CheckedMethod where
  /-- The method name used for checked method lookup. -/
  name : Identifier
  /-- The local variable name bound to the receiver object when checking the method body. -/
  receiverParam : Identifier
  /-- The local variable name bound to the explicit argument. -/
  param : Identifier
  /-- The machine-facing `CheckedTarget` annotation for the explicit argument. -/
  paramTy : CheckedTarget
  /-- The machine-facing `CheckedTarget` annotation for the return value. -/
  returnTy : CheckedTarget
  /-- Source obligation reported when the method's explicit-argument boundary rejects an argument. -/
  parameterObligation : SourceObligation
  /-- Source obligation reported when the method's declared return boundary rejects the method body result. -/
  returnObligation : SourceObligation
  /-- The checked expression executed as the method body. -/
  body : CheckedExpr
  deriving DecidableEq, Repr

/-- A checked class has the same structure as a gradual class but with checked methods. -/
structure CheckedClass where
  name : Identifier
  baseClasses : List Identifier
  methods : List CheckedMethod
  deriving DecidableEq, Repr

/-- A checked class table is a list of checked class definitions. -/
abbrev CheckedClassTable := List CheckedClass

/-- A checked program consists of a checked class table and a main checked expression. -/
structure CheckedProgram where
  classes : CheckedClassTable
  main : CheckedExpr
  deriving DecidableEq, Repr

/-- Find a class by name in the checked class table. -/
def findCheckedClass (ct : CheckedClassTable) (cname : Identifier) :
    Option CheckedClass :=
  findByName CheckedClass.name ct cname

/-- Find a method by name in a list of checked methods. -/
abbrev findCheckedMethodInList (ms : List CheckedMethod) (mname : Identifier) :
    Option CheckedMethod :=
  findByName CheckedMethod.name ms mname

/-- Find a checked method by searching each class in the MRO order
    within a checked class table. -/
abbrev findCheckedMethodInMro (cct : CheckedClassTable) (mro : List Identifier)
    (mname : Identifier) : Option CheckedMethod :=
  findMemberInHierarchy findCheckedClass CheckedClass.methods CheckedMethod.name cct mro mname

/-! ### Checked method lookup lemmas -/

/-- If checked MRO lookup finds a method, its name matches the query. -/
theorem findCheckedMethodInMro_name
    (h : findCheckedMethodInMro cct mro mname = some m) : m.name = mname :=
  findMemberInHierarchy_name h

/-- If checked MRO lookup finds a method, that method comes from some class in the MRO. -/
theorem findCheckedMethodInMro_provenance
    (h : findCheckedMethodInMro cct mro methodName = some m) :
    ∃ cname cc, cname ∈ mro ∧ findCheckedClass cct cname = some cc ∧ m ∈ cc.methods :=
  findMemberInHierarchy_provenance h

/-- If some class in the MRO contains a checked method with the queried name,
    checked MRO lookup succeeds somewhere along the MRO. -/
theorem findCheckedMethodInMro_exists_of_mem
    (hmem : dname ∈ mro)
    (hclass : findCheckedClass cct dname = some dc)
    (hmethod : cm ∈ dc.methods)
    (hname : cm.name = mname) :
    ∃ cm', findCheckedMethodInMro cct mro mname = some cm' :=
  findMemberInHierarchy_exists_of_mem hmem hclass hmethod hname

/-! ### Method reachability via receiver MRO -/

/-- Method `cm` is the result of checked MRO method lookup from the receiver's class. -/
def CheckedMethodInReceiverMro (gct : GClassTable) (cct : CheckedClassTable)
    (recvClassName : Identifier) (cm : CheckedMethod) : Prop :=
  ∃ recvCls mro,
    findGClass gct recvClassName = some recvCls ∧
    GComputeMro gct recvCls mro ∧
    findCheckedMethodInMro cct mro cm.name = some cm

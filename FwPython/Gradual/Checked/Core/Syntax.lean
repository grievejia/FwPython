import FwPython.Gradual.MRO.Lookup
import FwPython.Gradual.Contracts
import FwPython.Gradual.Statics
import FwPython.Gradual.TypeSystem.CheckedTargetSyntax
import FwPython.Builtins

/-! # Checked Runtime Vocabulary

Defines the checked target language and runtime objects for the gradual system.
The checked language extends the gradual source with explicit enforcement nodes
(`enforce` against `BoundaryContract`). Method calls carry their call-site
return boundary labels explicitly so the runtime can enforce method returns
against both the method contract and the call-site contract. -/

/-! ## Checked expressions -/

/-- The checked target language extends the gradual source expressions with:
    - `enforce e target labels`: runtime type enforcement against the compiled
      contract image of `target`; blames `labels.direct` if `e` does not conform
    - `dynAttrAccess e attrName ℓ`: dynamic attribute access; blames `ℓ` if
      the attribute is missing, rather than producing a raw runtime error -/
inductive CheckedExpr : Type where
  | var : Identifier → CheckedExpr
  | new : Identifier → CheckedExpr
  | attrAccess : CheckedExpr → Identifier → CheckedExpr
  | call : CheckedExpr → CheckedExpr →
      (paramTy : CheckedTarget) → (returnTy : CheckedTarget) →
      BoundaryLabels (compileBoundaryTarget returnTy) → CheckedExpr
  | constNone : CheckedExpr
  | constTrue : CheckedExpr
  | constFalse : CheckedExpr
  | cond : CheckedExpr → CheckedExpr → CheckedExpr → CheckedExpr
  | isInstance : Identifier → Identifier → CheckedExpr
  | enforce : (e : CheckedExpr) → (target : CheckedTarget) →
      BoundaryLabels (compileBoundaryTarget target) → CheckedExpr
  | dynAttrAccess : CheckedExpr → Identifier → Label → CheckedExpr
  deriving DecidableEq, Repr

/-- Child positions inside checked expressions, used for provenance paths. -/
inductive ExprChild : Type where
  | attrBase
  | callCallee
  | callArg
  | condTest
  | condThen
  | condElse
  | enforceBody
  | dynAttrBase
  deriving DecidableEq, Repr

/-- Paths from the expression root to a descendant node. -/
abbrev ExprPath := List ExprChild

/-- Read the subexpression at a path. Returns the root expression at `[]`. -/
def CheckedExpr.nodeAt : CheckedExpr → ExprPath → Option CheckedExpr
  | e, [] => some e
  | .attrAccess base _, .attrBase :: path => base.nodeAt path
  | .call callee _ _ _ _, .callCallee :: path => callee.nodeAt path
  | .call _ arg _ _ _, .callArg :: path => arg.nodeAt path
  | .cond test _ _, .condTest :: path => test.nodeAt path
  | .cond _ thenBr _, .condThen :: path => thenBr.nodeAt path
  | .cond _ _ elseBr, .condElse :: path => elseBr.nodeAt path
  | .enforce e _ _, .enforceBody :: path => e.nodeAt path
  | .dynAttrAccess e _ _, .dynAttrBase :: path => e.nodeAt path
  | _, _ => none

theorem CheckedExpr.nodeAt_append
    {e e' : CheckedExpr}
    (h : e.nodeAt p = some e') :
    e.nodeAt (p ++ q) = e'.nodeAt q := by
  induction p generalizing e with
  | nil =>
      simp [CheckedExpr.nodeAt] at h ⊢
      cases h
      rfl
  | cons child p ih =>
      cases e <;> cases child <;> simp [CheckedExpr.nodeAt] at h ⊢ <;> exact ih h

theorem checkedExpr_call_inversion
    {callee₁ callee₂ arg₁ arg₂ : CheckedExpr}
    {paramTy₁ paramTy₂ returnTy₁ returnTy₂ : CheckedTarget}
    {returnLabels₁ : BoundaryLabels (compileBoundaryTarget returnTy₁)}
    {returnLabels₂ : BoundaryLabels (compileBoundaryTarget returnTy₂)}
    (h :
      CheckedExpr.call callee₁ arg₁ paramTy₁ returnTy₁ returnLabels₁ =
        CheckedExpr.call callee₂ arg₂ paramTy₂ returnTy₂ returnLabels₂) :
    ∃ hret : returnTy₁ = returnTy₂,
      callee₁ = callee₂ ∧
      arg₁ = arg₂ ∧
      paramTy₁ = paramTy₂ ∧
      hret ▸ returnLabels₁ = returnLabels₂ := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Checked classes -/

/-- A checked method stores both the original gradual type annotations and the
    explicit checked targets with blame labels indexed by their compiled
    contract images. -/
structure CheckedMethod where
  name : Identifier
  receiverParam : Identifier
  param : Identifier
  paramTy : CheckedTarget
  returnTy : CheckedTarget
  parameterLabels : BoundaryLabels (compileBoundaryTarget paramTy)
  returnLabels : BoundaryLabels (compileBoundaryTarget returnTy)
  body : CheckedExpr
  deriving DecidableEq, Repr

namespace CheckedMethod

/-- The machine-facing parameter contract is recovered from the stored checked
target annotation on demand rather than stored redundantly. -/
def parameterContract (m : CheckedMethod) : BoundaryContract :=
  compileBoundaryTarget m.paramTy

/-- The machine-facing return contract is recovered from the stored checked
target annotation on demand rather than stored redundantly. -/
def returnContract (m : CheckedMethod) : BoundaryContract :=
  compileBoundaryTarget m.returnTy

@[simp] theorem parameterContract_eq
    (m : CheckedMethod) :
    m.parameterContract = compileBoundaryTarget m.paramTy :=
  rfl

@[simp] theorem returnContract_eq
    (m : CheckedMethod) :
    m.returnContract = compileBoundaryTarget m.returnTy :=
  rfl

end CheckedMethod

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

theorem findCheckedMethodInList_mem
    (h : findCheckedMethodInList ms mname = some m) : m ∈ ms :=
  findByName_mem h

theorem findCheckedMethodInList_name
    (h : findCheckedMethodInList ms mname = some m) : m.name = mname := by
  exact findByName_name h

/-- Within one checked class, distinct method-list members cannot share a name. -/
theorem findCheckedMethodInList_unique
    {ms : List CheckedMethod} {m₁ m₂ : CheckedMethod}
    (hnodup : List.Nodup (ms.map CheckedMethod.name))
    (hmem₁ : m₁ ∈ ms)
    (hmem₂ : m₂ ∈ ms)
    (hname : m₁.name = m₂.name) :
    m₁ = m₂ := by
  induction ms with
  | nil => cases hmem₁
  | cons m ms ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hnotmem, hnodup⟩
      cases hmem₁ with
      | head =>
          cases hmem₂ with
          | head => rfl
          | tail _ hmem₂ => exact absurd (List.mem_map.mpr ⟨m₂, hmem₂, hname.symm⟩) hnotmem
      | tail _ hmem₁ =>
          cases hmem₂ with
          | head => exact absurd (List.mem_map.mpr ⟨m₁, hmem₁, hname⟩) hnotmem
          | tail _ hmem₂ => apply ih <;> assumption

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

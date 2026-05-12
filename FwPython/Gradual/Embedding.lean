import FwPython.Gradual.ClassTable
import FwPython.Static.ClassTable
import FwPython.Common.MRO.Core
import FwPython.Builtins

/-! # Erasure and embedding between gradual and fully static types

The erasure from `GClassTable` to `ClassTable` preserves only the class
hierarchy (names and base-class lists). Method entries receive dummy `Ty`
annotations and dummy `Expr` bodies. The erased fully static class table
is used exclusively for hierarchy and subtyping queries through
`FwPython.Static.Subtyping.Core` — never for method-level reasoning. -/

/-! ## Erasure definitions -/

/-- Erase a gradual method to a fully static method with dummy annotations.
    Only the method name, receiver parameter, and parameter name are kept;
    the parameter type becomes `Ty.bottom`, the return type becomes
    `Ty.class_ noneClass`, and the body becomes `constNone`. -/
def eraseMethod (m : GMethod) : Method where
  name := m.name
  receiverParam := m.receiverParam
  param := m.param
  paramTy := Ty.bottom
  returnTy := Ty.class_ noneClass
  body := .constNone

/-- Erase a gradual class to a fully static class, preserving name and inheritance. -/
def eraseClass (gc : GClass) : Class where
  name := gc.name
  baseClasses := gc.baseClasses
  methods := gc.methods.map eraseMethod

/-- Erase a gradual class table to a fully static class table. -/
def eraseClassTable (gct : GClassTable) : ClassTable :=
  gct.map eraseClass

/-- Erase a gradual program to a fully static program with dummy types and body. -/
def eraseProgram (gp : GProgram) : Program where
  classes := eraseClassTable gp.classes
  main := .constNone

/-! ## Basic erasure properties -/

@[simp] theorem eraseClass_name (gc : GClass) : (eraseClass gc).name = gc.name := rfl

@[simp] theorem eraseClass_baseClasses (gc : GClass) :
    (eraseClass gc).baseClasses = gc.baseClasses := rfl

/-- The erased class has the same resolved base-class list as the original. -/
@[simp] theorem eraseClass_resolvedBases (gc : GClass) :
    (eraseClass gc).resolvedBases = gc.resolvedBases := rfl

/-! ## Static-to-gradual embedding -/

/-- Embed a static expression into the gradual source language. -/
def embedExpr : Expr → GExpr
  | .var x => .var x
  | .new cname => .new cname
  | .attrAccess base attr => .attrAccess (embedExpr base) attr
  | .call callee arg => .call (embedExpr callee) (embedExpr arg)
  | .constNone => .constNone
  | .constTrue => .constTrue
  | .constFalse => .constFalse
  | .cond condExpr thenBranch elseBranch =>
      .cond (embedExpr condExpr) (embedExpr thenBranch) (embedExpr elseBranch)
  | .isInstance x cname => .isInstance x cname

/-! ## Class lookup bridge -/

private theorem findByName_map_eq
    (f : α → β)
    (getNameβ : β → Identifier)
    (getNameα : α → Identifier)
    (hname : ∀ x, getNameβ (f x) = getNameα x)
    (xs : List α) (name : Identifier) :
    findByName getNameβ (xs.map f) name =
      (findByName getNameα xs name).map f := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
      by_cases h : getNameα a = name
      · simp [findByName, h, hname]
      · simpa [findByName, h, hname] using ih

/-- Unified bridge: `findClass` on the erased table equals `findGClass`
    composed with `Option.map eraseClass`. -/
theorem findClass_eraseClassTable_eq (gct : GClassTable) (cname : Identifier) :
    findClass (eraseClassTable gct) cname = (findGClass gct cname).map eraseClass :=
  findByName_map_eq eraseClass ClassDecl.name ClassDecl.name (fun _ => rfl) gct cname

/-- Forward lookup bridge: gradual lookup implies static lookup on the erased table. -/
theorem findClass_eraseClassTable {gct : GClassTable} {cname : Identifier} {gc : GClass}
    (h : findGClass gct cname = some gc) :
    findClass (eraseClassTable gct) cname = some (eraseClass gc) := by
  simp [findClass_eraseClassTable_eq, h]

/-- Reverse lookup bridge: static lookup on the erased table implies gradual lookup. -/
theorem findGClass_of_findClass_eraseClassTable {gct : GClassTable} {cname : Identifier}
    {c : Class} (h : findClass (eraseClassTable gct) cname = some c) :
    ∃ gc, findGClass gct cname = some gc ∧ eraseClass gc = c := by
  simpa [findClass_eraseClassTable_eq] using h

/-- Class name uniqueness is preserved by erasure. -/
theorem eraseClassTable_classNamesUnique {gct : GClassTable}
    (huniq : ∀ c₁ c₂, c₁ ∈ gct → c₂ ∈ gct → c₁.name = c₂.name → c₁ = c₂) :
    ∀ c₁ c₂, c₁ ∈ eraseClassTable gct → c₂ ∈ eraseClassTable gct →
      c₁.name = c₂.name → c₁ = c₂ := by
  intro c₁ c₂ h₁ h₂ hname
  obtain ⟨gc₁, hgc₁_mem, rfl⟩ := List.mem_map.mp h₁
  obtain ⟨gc₂, hgc₂_mem, rfl⟩ := List.mem_map.mp h₂
  exact congrArg eraseClass (huniq gc₁ gc₂ hgc₁_mem hgc₂_mem hname)

/-! ## Static top -/

/-- The fully static universal supertype, `class_ objectClass`. Used as
    the upper bound of `any` (the unknown fully static type) under the
    semantic gradual interpretation. -/
def staticTop : Ty := .class_ objectClass

/-! ## Type embedding -/

/-- Embed a static type into the gradual type language, preserving the
    primitive `negClass` atom. -/
def embedTy : Ty → GTy
  | .class_ c => .class_ c
  | .negClass c => .negClass c
  | .callable p r => .callable (embedTy p) (embedTy r)
  | .union t u => .union (embedTy t) (embedTy u)
  | .intersection t u => .intersection (embedTy t) (embedTy u)
  | .bottom => .bottom

/-! ## Semantic lower and upper bounds -/

mutual
/-- The fully static lower bound of a gradual type: the largest fully
    static type that every materialization of the gradual type is a
    supertype of.

    `any` (the unknown fully static type) lowers to `bottom` (no
    obligation). Callable types are contravariant/covariant as usual.
    `negClass C` is atomic and lowers to the same static atom. -/
def lowerBound : GTy → Ty
  | .any => .bottom
  | .class_ c => .class_ c
  | .callable p r => .callable (upperBound p) (lowerBound r)
  | .union t u => .union (lowerBound t) (lowerBound u)
  | .intersection t u => .intersection (lowerBound t) (lowerBound u)
  | .bottom => .bottom
  | .negClass c => .negClass c

/-- The fully static upper bound of a gradual type: the smallest fully
    static type that every materialization of the gradual type is a
    subtype of.

    `any` (the unknown fully static type) uppers to `staticTop`.
    Callable types are contravariant/covariant as usual. `negClass C`
    is atomic. -/
def upperBound : GTy → Ty
  | .any => staticTop
  | .class_ c => .class_ c
  | .callable p r => .callable (lowerBound p) (upperBound r)
  | .union t u => .union (upperBound t) (upperBound u)
  | .intersection t u => .intersection (upperBound t) (upperBound u)
  | .bottom => .bottom
  | .negClass c => .negClass c
end

/-! ## Basic embedding lemmas -/

theorem embedTy_bounds (t : Ty) :
    lowerBound (embedTy t) = t ∧ upperBound (embedTy t) = t := by
  induction t with
  | class_ _ | negClass _ | bottom => exact ⟨rfl, rfl⟩
  | callable _ _ ih₁ ih₂ =>
    exact ⟨by simp [embedTy, lowerBound, ih₁.2, ih₂.1],
           by simp [embedTy, upperBound, ih₁.1, ih₂.2]⟩
  | union _ _ ih₁ ih₂ | intersection _ _ ih₁ ih₂ =>
    exact ⟨by simp [embedTy, lowerBound, ih₁.1, ih₂.1],
           by simp [embedTy, upperBound, ih₁.2, ih₂.2]⟩

theorem embedTy_lowerBound (t : Ty) :
    lowerBound (embedTy t) = t :=
  (embedTy_bounds t).1

theorem embedTy_upperBound (t : Ty) :
    upperBound (embedTy t) = t :=
  (embedTy_bounds t).2

/-! ## Static-to-gradual program embedding -/

/-- Embed a static method into a gradual method. -/
def embedMethod (m : Method) : GMethod where
  name := m.name
  receiverParam := m.receiverParam
  param := m.param
  paramTy := embedTy m.paramTy
  returnTy := embedTy m.returnTy
  body := embedExpr m.body

/-- Embed a static class into a gradual class. -/
def embedClass (c : Class) : GClass where
  name := c.name
  baseClasses := c.baseClasses
  methods := c.methods.map embedMethod

/-- Embed a static class table into a gradual class table. -/
def embedClassTable (ct : ClassTable) : GClassTable :=
  ct.map embedClass

/-- Embed a static program into a gradual program. -/
def embedProgram (p : Program) : GProgram where
  classes := embedClassTable p.classes
  main := embedExpr p.main

@[simp] theorem embedMethod_name (m : Method) : (embedMethod m).name = m.name := rfl

@[simp] theorem embedMethod_paramTy (m : Method) :
    (embedMethod m).paramTy = embedTy m.paramTy := rfl

@[simp] theorem embedMethod_returnTy (m : Method) :
    (embedMethod m).returnTy = embedTy m.returnTy := rfl

@[simp] theorem embedClass_name (c : Class) : (embedClass c).name = c.name := rfl

@[simp] theorem embedClass_baseClasses (c : Class) :
    (embedClass c).baseClasses = c.baseClasses := rfl

/-- The embedded gradual class has the same resolved base-class list as the
    original static class. -/
@[simp] theorem embedClass_resolvedBases (c : Class) :
    (embedClass c).resolvedBases = c.resolvedBases := rfl

/-! ## Static-to-gradual lookup bridge -/

/-- Class lookup on the embedded gradual table is static lookup followed by
    `embedClass`. -/
theorem findGClass_embedClassTable_eq (ct : ClassTable) (cname : Identifier) :
    findGClass (embedClassTable ct) cname = (findClass ct cname).map embedClass :=
  findByName_map_eq embedClass ClassDecl.name ClassDecl.name (fun _ => rfl) ct cname

/-- Forward class lookup bridge for embedded class tables. -/
theorem findGClass_embedClassTable {ct : ClassTable} {cname : Identifier} {c : Class}
    (h : findClass ct cname = some c) :
    findGClass (embedClassTable ct) cname = some (embedClass c) := by
  simp [findGClass_embedClassTable_eq, h]

/-- Reverse class lookup bridge for embedded class tables. -/
theorem findClass_embedClassTable_reverse {ct : ClassTable} {cname : Identifier}
    {gc : GClass} (h : findGClass (embedClassTable ct) cname = some gc) :
    ∃ c, findClass ct cname = some c ∧ embedClass c = gc := by
  simpa [findGClass_embedClassTable_eq] using h

theorem findGMethodInList_embedMethods_eq
    (ms : List Method) (mname : Identifier) :
    findGMethodInList (ms.map embedMethod) mname =
      (findMethodInList ms mname).map embedMethod :=
  findByName_map_eq embedMethod MethodDecl.name MethodDecl.name (fun _ => rfl) ms mname

/-- Forward method lookup bridge on embedded method lists. -/
theorem findGMethodInList_embedMethods {ms : List Method} {mname : Identifier} {m : Method}
    (h : findMethodInList ms mname = some m) :
    findGMethodInList (ms.map embedMethod) mname = some (embedMethod m) := by
  simp [findGMethodInList_embedMethods_eq, h]

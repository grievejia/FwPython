import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.TypeSystem.Context
import FwPython.Static.Subtyping.Core
import FwPython.Static.TypeSystem.Value.Typing

/-! ## Surface typing core

This file is definition-only and remains below theorem-heavy modules such as
`WellFormedness`, `Invariants`, and runtime preservation/progress proofs.
-/

/-- An expression has a static type under one hierarchy and variable environment.
Every recursive typing premise and subtype comparison uses that same table. -/
inductive HasType {ct : ClassTable} (structural : WellFormedClassHierarchy ct) : TyEnv → Expr → Ty → Prop where
  /-- Widen the expression's type through subtyping, which certifies both types' validity. -/
  | sub :
      HasType structural Γ e S →
      IsSubtype structural S T →
      HasType structural Γ e T
  | var :
      Γ.lookup x = some T →
      HasType structural Γ (.var x) T
  | constNone :
      HasType structural Γ .constNone (.class_ noneClass)
  | constTrue :
      HasType structural Γ .constTrue (.class_ boolClass)
  | constFalse :
      HasType structural Γ .constFalse (.class_ boolClass)
  | new :
      findClass ct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      HasType structural Γ (.new cname) (.class_ cname)
  | attrAccess :
      HasType structural Γ base (.class_ cname) →
      FindMethodType ct cname attrName paramTy returnTy →
      HasType structural Γ (.attrAccess base attrName) (.callable paramTy returnTy)
  | attrAccessUnion :
      HasType structural Γ base (.union (.class_ c1) (.class_ c2)) →
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      HasType structural Γ (.attrAccess base attrName)
        (.union (.callable p1 r1) (.callable p2 r2))
  | call :
      HasType structural Γ callee (.callable paramTy returnTy) →
      HasType structural Γ arg argTy →
      IsSubtype structural argTy paramTy →
      HasType structural Γ (.call callee arg) returnTy
  | cond :
      HasType structural Γ condExpr testTy →
      IsSubtype structural testTy (.class_ boolClass) →
      HasType structural Γ thenBr thenTy →
      HasType structural Γ elseBr elseTy →
      HasType structural Γ (.cond condExpr thenBr elseBr) (.union thenTy elseTy)
  | isInstance :
      Γ.lookup x = some T →
      findClass ct C = some cls →
      HasType structural Γ (.isInstance x C) (.class_ boolClass)
  | condIsInstance :
      Γ.lookup x = some T →
      findClass ct C = some cls →
      HasType structural
        (Γ.update x (.intersection T (.class_ C)))
        thenBr thenTy →
      HasType structural
        (Γ.update x (.intersection T (.negClass C)))
        elseBr elseTy →
      HasType structural Γ
        (.cond (.isInstance x C) thenBr elseBr)
        (.union thenTy elseTy)
  | interIntro :
      HasType structural Γ e T →
      HasType structural Γ e U →
      HasType structural Γ e (.intersection T U)

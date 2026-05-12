import FwPython.Static.TypeSystem.MethodLookup
import FwPython.Static.TypeSystem.Context
import FwPython.Static.Subtyping.Core
import FwPython.Static.TypeSystem.Value.Typing

/-! ## Surface typing core

This file is definition-only and remains below theorem-heavy modules such as
`WellFormedness`, `Invariants`, and runtime preservation/progress proofs.
-/

/-- Surface typing in the source-facing static language. -/
inductive HasType : ClassTable → TyEnv → Expr → Ty → Prop where
  | sub :
      HasType ct Γ e S →
      IsSubtype ct S T →
      WellFormedTy ct T →
      HasType ct Γ e T
  | var :
      Γ.lookup x = some T →
      HasType ct Γ (.var x) T
  | constNone :
      HasType ct Γ .constNone (.class_ noneClass)
  | constTrue :
      HasType ct Γ .constTrue (.class_ boolClass)
  | constFalse :
      HasType ct Γ .constFalse (.class_ boolClass)
  | new :
      findClass ct cname = some c →
      cname ≠ boolClass →
      cname ≠ noneClass →
      cname ≠ boundMethodClass →
      HasType ct Γ (.new cname) (.class_ cname)
  | attrAccess :
      HasType ct Γ base (.class_ cname) →
      FindMethodType ct cname attrName paramTy returnTy →
      HasType ct Γ (.attrAccess base attrName) (.callable paramTy returnTy)
  | attrAccessUnion :
      HasType ct Γ base (.union (.class_ c1) (.class_ c2)) →
      FindMethodType ct c1 attrName p1 r1 →
      FindMethodType ct c2 attrName p2 r2 →
      HasType ct Γ (.attrAccess base attrName)
        (.union (.callable p1 r1) (.callable p2 r2))
  | call :
      HasType ct Γ callee (.callable paramTy returnTy) →
      HasType ct Γ arg argTy →
      IsSubtype ct argTy paramTy →
      HasType ct Γ (.call callee arg) returnTy
  | cond :
      HasType ct Γ condExpr testTy →
      IsSubtype ct testTy (.class_ boolClass) →
      HasType ct Γ thenBr thenTy →
      HasType ct Γ elseBr elseTy →
      HasType ct Γ (.cond condExpr thenBr elseBr) (.union thenTy elseTy)
  | isInstance :
      Γ.lookup x = some T →
      findClass ct C = some cls →
      HasType ct Γ (.isInstance x C) (.class_ boolClass)
  | condIsInstance :
      Γ.lookup x = some T →
      findClass ct C = some cls →
      HasType ct
        (Γ.update x (.intersection T (.class_ C)))
        thenBr thenTy →
      HasType ct
        (Γ.update x (.intersection T (.negClass C)))
        elseBr elseTy →
      HasType ct Γ
        (.cond (.isInstance x C) thenBr elseBr)
        (.union thenTy elseTy)
  | interIntro :
      HasType ct Γ e T →
      HasType ct Γ e U →
      HasType ct Γ e (.intersection T U)

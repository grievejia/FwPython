import FwPython.Common.ClassModel
import FwPython.Gradual.Types
import FwPython.Gradual.Ast

/-! # Gradual methods, classes, and class table -/

abbrev GMethod := MethodDecl GTy GExpr

abbrev GClass := ClassDecl GMethod

/-- A gradual class table is a list of gradual class definitions. -/
abbrev GClassTable := ClassTableDecl GMethod

/-- A gradual program consists of a gradual class table and a main expression. -/
abbrev GProgram := ProgramDecl GClass GExpr

/-- Find a class by name in the gradual class table. -/
abbrev findGClass (ct : GClassTable) (cname : Identifier) : Option GClass :=
  findClass ct cname

/-- Find a method by name in a list of gradual methods. -/
abbrev findGMethodInList (ms : List GMethod) (mname : Identifier) : Option GMethod :=
  findMethodInList ms mname

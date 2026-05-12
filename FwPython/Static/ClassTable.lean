import FwPython.Common.ClassModel
import FwPython.Static.Types
import FwPython.Static.Ast

/-! # Methods, classes, and class table -/

abbrev Method := MethodDecl Ty Expr

abbrev Class := ClassDecl Method

/-- A class table is a list of class definitions. -/
abbrev ClassTable := ClassTableDecl Method

/-- A program consists of a class table and a main expression to evaluate. -/
abbrev Program := ProgramDecl Class Expr

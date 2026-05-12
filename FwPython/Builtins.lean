import FwPython.Common.Identifier

/-! # Built-in class names and pre-allocated object IDs -/

/-- Class names for built-in constants. -/
def noneClass : Identifier := "NoneType"
def boolClass : Identifier := "Bool"

/-- Base class for all classes. -/
def objectClass : Identifier := "Object"

/-- Built-in class for reified bound methods. -/
def boundMethodClass : Identifier := "BoundMethod"

/-- Object IDs for pre-allocated constant objects. -/
def noneOid : Nat := 0
def trueOid : Nat := 1
def falseOid : Nat := 2

# FwPython syntax

This reference describes the static language defined by
[Ast.lean](../FwPython/Static/Ast.lean) and
[ClassTable.lean](../FwPython/Static/ClassTable.lean).
A program contains class declarations and one main expression.
Method bodies are also expressions.

The notation below explains the Lean syntax constructors. It is not a separate
text parser. Type annotations are described in the
[static type system](type_system.md#types-and-their-meaning).

## Names and declarations

Names are strings. Variables, classes, and methods use the same identifier type.

| Program field | Meaning |
| --- | --- |
| `classes` | The list of class declarations available to the program. |
| `main` | The expression evaluated when the program starts. |

The declaration list is called the *class table*. Class lookup selects the
first declaration with the requested name.

| Class field | Meaning |
| --- | --- |
| `name` | The name that identifies the class in expressions and parent lists. |
| `baseClasses` | Direct parent names, in the declared inheritance order. |
| `methods` | Methods defined by this class. Inherited methods are found through the parents. |

A *method resolution order* (MRO) lists a class and its ancestors in method
lookup order. C3 computes this list while preserving each parent's MRO and the
declared parent order. If a class has no explicit parents, it inherits Object.
Object itself has no parents.

| Method field | Meaning |
| --- | --- |
| `name` | The name used by method lookup. |
| `receiverParam` | The variable bound to the object on which the method runs. |
| `param` | The variable bound to the method's one explicit argument. |
| `paramTy` | The declared type of that argument. |
| `returnTy` | The declared type required of a returned result. |
| `body` | The expression evaluated with the receiver and argument bound. |

Each method takes one explicit argument in addition to its receiver. Classes
have methods but no fields. Object creation does not run a constructor.

## Expressions

| Lean constructor | Readable notation | Meaning |
| --- | --- | --- |
| `var x` | `x` | Return the value bound to variable `x`. |
| `new C` | `new C` | Allocate an object of class `C`. |
| `attrAccess e m` | `e.m` | Find method `m` on the object produced by `e` and return a bound method. |
| `call f a` | `f(a)` | Evaluate the function, then the argument, then call the bound method. |
| `constNone` | `NONE` | Return the None singleton. |
| `constTrue` | `TRUE` | Return the true Boolean singleton. |
| `constFalse` | `FALSE` | Return the false Boolean singleton. |
| `cond c t f` | `if c then t else f` | Evaluate `c`; evaluate `t` for TRUE or `f` for FALSE. |
| `isInstance x C` | `isInstance(x, C)` | Test whether the bound object's runtime MRO contains `C`. |

A *bound method* combines a selected method definition with its receiver.
Attribute access allocates an object that stores this pair. The resulting value
can be passed to another method or called later.

`isInstance` takes a variable name. This lets the type checker refine that
variable's type in each branch of a conditional. A positive test establishes
class membership; a negative test establishes class exclusion.

## Builtin classes and constants

| Class | Meaning |
| --- | --- |
| `Object` | The root ancestor of every class. |
| `Bool` | The class of the TRUE and FALSE singletons. |
| `NoneType` | The class of the NONE singleton. |
| `BoundMethod` | The class of objects that store a receiver and a method. |

Bool, NoneType, and BoundMethod are sealed: a different class cannot inherit
from them. The class-table validation rules enforce this restriction.

`new C` requires a declared class and excludes Bool, NoneType, and BoundMethod.
Constants provide Bool and NoneType values; attribute lookup creates BoundMethod values.

Every runtime value is an object reference. The initial heap contains the three
constant objects:

| Constant | Object identifier | Class |
| --- | --- | --- |
| `NONE` | `noneOid = 0` | `NoneType` |
| `TRUE` | `trueOid = 1` | `Bool` |
| `FALSE` | `falseOid = 2` | `Bool` |

These definitions are in [Builtins.lean](../FwPython/Builtins.lean).

## Scope

The language focuses on inheritance, method lookup, function types, and branch
refinement. Methods with one argument avoid extra rules for argument lists.
The absence of fields avoids mutation rules. These choices keep the safety proofs
focused on calls and class tests.

FwPython takes these features from Python but specifies its own small language.
It does not model Python statements, constructors, fields, or descriptors.

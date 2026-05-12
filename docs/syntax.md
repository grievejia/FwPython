# FwPython Syntax

This document describes the surface language defined in
`FwPython/Static/Ast.lean` and `FwPython/Static/ClassTable.lean`. FwPython is intentionally small. A program is just a
class table together with one main expression, and evaluation is expression
oriented from end to end.

The language is designed to isolate a specific cluster of issues:

- nominal classes with multiple inheritance
- runtime method lookup through an MRO
- first-class method values
- conditionals with branch-sensitive `isInstance` tests

It does not try to model a full Python-like object system. There are no
statements, no mutable fields, no constructors, and no descriptor machinery.

## Identifiers

Identifiers are strings. The same underlying type is used for:

- variable names
- class names
- method names

The syntax layer does not impose further structure.

## Programs, Classes, and Methods

A program has two components:

- a class table
- a main expression

A class declaration has three components:

- the class name
- a list of direct base-class names
- a list of methods

A method declaration has six components:

- the method name
- the receiver parameter name
- the ordinary parameter name
- the parameter type annotation
- the return type annotation
- the body expression

Methods are unary: every method takes exactly one explicit argument in addition
to the receiver. This keeps the core calculus small while still supporting the
interaction between method lookup, callable values, and variance.

Classes contain methods but no fields. If a class declares no explicit base
classes, the MRO machinery treats it as implicitly inheriting from `Object`,
unless the class itself is `Object`.

## Expressions

FwPython has nine expression forms.

| Lean constructor | Surface intuition | Role |
| --- | --- | --- |
| `var x` | `x` | Look up variable `x` in the runtime environment. |
| `new C` | `new C` | Allocate a fresh object of class `C`. No constructor is invoked. |
| `attrAccess e m` | `e.m` | Resolve method `m` on the runtime class of `e`, allocate a fresh bound-method object, and return it. |
| `call e1 e2` | `e1(e2)` | Invoke the value of `e1` on argument `e2`. Calls succeed only for objects carrying bound-method payload. |
| `constNone` | `NONE` | The distinguished none object. |
| `constTrue` | `TRUE` | The distinguished true object. |
| `constFalse` | `FALSE` | The distinguished false object. |
| `cond e1 e2 e3` | `if e1 then e2 else e3` | Evaluate `e1`; on `TRUE` continue with `e2`, on `FALSE` continue with `e3`. |
| `isInstance x C` | `isInstance(x, C)` | Test whether the runtime class of the value stored in variable `x` lies under class `C`. |

The important design choice is that `isInstance` takes a variable name rather
than an arbitrary expression. That restriction is deliberate: the type system
uses `isInstance` as a narrowing construct, so the test has to refer to a name
whose type can be refined on each branch.

## Built-In Names

The syntax layer fixes four distinguished class names:

- `Object`
- `Bool`
- `NoneType`
- `BoundMethod`

It also fixes three distinguished object identifiers:

| Name | Meaning | Object ID |
| --- | --- | --- |
| `noneOid` | the object returned by `NONE` | `0` |
| `trueOid` | the object returned by `TRUE` | `1` |
| `falseOid` | the object returned by `FALSE` | `2` |

These names matter throughout the rest of the development:

- `Object` is the nominal root of the class hierarchy.
- `Bool` and `NoneType` support the distinguished runtime constants.
- `BoundMethod` is the runtime class used for reified method values.

The syntax file only fixes the names and identifiers. Their semantic role is
explained by the runtime and typing documents.

## Runtime Reading of the Syntax

Although the syntax files only define the abstract syntax tree, two runtime facts
help explain why the expression forms look the way they do.

First, every runtime value is an object reference. FwPython does not have a
separate runtime category for booleans, `None`, or functions.

Second, every heap object carries:

- a runtime class name
- a payload

Most payloads are ordinary. Bound methods are represented as ordinary heap
objects whose payload stores:

- the receiver object id
- the selected method declaration

This is why attribute access is not just a static projection. Operationally, it
allocates a fresh heap object of class `BoundMethod`, and that object can then
be passed around like any other value.

## Why the Language Looks This Way

### No Fields

FwPython omits fields to keep the metatheory focused on dispatch, subtyping,
callability, and flow-sensitive reasoning. Read-only field-like behavior can be
encoded with methods that ignore their argument.

### Unary Methods

Unary methods make the operational semantics and variance story much cleaner.
The language still exercises the important interaction between method lookup and
call application without adding tuple-like argument structure.

### Variable-Only `isInstance`

The `isInstance` form exists primarily to support narrowing in conditionals.
Allowing arbitrary expressions there would require a separate story for naming
and tracking the tested value across branches.

### Python-Inspired, Not Python-Complete

FwPython borrows some recognizable object-oriented features from Python:

- multiple inheritance
- C3 linearization
- runtime method lookup
- reified bound methods
- runtime class tests

But it deliberately omits the rest of Python's object model. The point of the
language is not realism for its own sake; it is to isolate a precise formal core
that is still rich enough to make the metatheory interesting.

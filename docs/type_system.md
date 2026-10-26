# Static type system

This document explains the design of static typing in FwPython. It connects the
meaning of types to subtyping, expression checking, and the type safety proof.
The [syntax reference](syntax.md) describes the language forms.

## Start with a method call

Suppose Echo defines an identity method with a Bool argument and a Bool result:

```text
class Echo(Object):
    echo(self, x: Bool) -> Bool = x

(new Echo).echo(TRUE)
```

This is readable notation for a class declaration and a main expression.
The method body is the expression `x`.

The call first creates an Echo object. Attribute access finds `echo` and
produces a *bound method*: a method definition paired with its receiver object.
Calling this value binds its argument to TRUE, evaluates the body, and returns TRUE.

This example needs two kinds of type information. The receiver has class Echo,
which determines method lookup. The bound method has function type
`Bool -> Bool`, which determines the permitted argument and result.
Both values are object references. The *heap* stores the objects to which they refer.

## Types and their meaning

A type states requirements on a value. A single value can satisfy several types.
For example, TRUE has class types Bool and Object.

A *method resolution order* (MRO) lists a class and its ancestors in method
lookup order. A value has class type C when its runtime class's MRO contains C.
This includes objects of C's subclasses.

Bool and NoneType are the classes of the Boolean and None constants.
BoundMethod is the class of method values.

The static type language is `Ty`. The following notation applies to method
annotations, expression types, and types assigned to heap values.

| Type | Meaning |
| --- | --- |
| `class_ C`, written C below | The object's runtime MRO contains C. |
| `negClass C` | The object's runtime MRO excludes C. |
| `callable P R`, written `P -> R` | Calls on P inputs must not fail. Any returned result must have type R. |
| `T \| U` | The value has type T, type U, or both. |
| `T & U` | The value has both types. |
| `bottom` | No values. |

Object contains every value. Only bound methods can be called, so every
function type requires class BoundMethod.

Function types do not require termination. A method with type `P -> bottom`
can run forever on P inputs. An empty input has a different meaning:
`bottom -> R` places no requirement on results because no argument can reach
the call. Every bound method satisfies that empty-input requirement.

Class exclusion supports the negative branch of a class test. The language
does not provide general negation of function types, unions, or intersections.

## Why subtyping comes from equations

Subtyping answers whether a value of one type can be used where another type
is required. We write `T <: U` for this relation.

Every Bool is an Object. Thus, adding Bool to the alternatives in
`Bool | Object` does not change Object:

```text
Bool | Object ≈ Object
```

Here, `≈` means equality derived from the type laws. The general definition is:

```text
T <: U  means  T | U ≈ U
```

This definition gives one common foundation for subtyping rules. A rule is
proved by deriving its union equation from the laws for types.

Union combines alternatives; intersection combines requirements. Their laws
permit changes of order and grouping, removal of repeated types, and distribution:

```text
T | bottom ≈ T
T & Object ≈ T
T & (U | V) ≈ (T & U) | (T & V)
```

These laws also give an equivalent subtype test, `T & U ≈ T`.
They imply that bottom is below every type, every type is below Object,
and each part of a union is below the union.

### Function inputs and results

A function can replace another function when it accepts all required inputs
and returns only permitted results. Therefore, input and result subtyping have
different directions:

```text
P' <: P and R <: R'
imply
(P -> R) <: (P' -> R')
```

For example, an Object-input function accepts Bool inputs. A Bool-result
function also meets an Object-result requirement.

The function equations explain these rules:

```text
(P | Q) -> R ≈ (P -> R) & (Q -> R)
P -> (R & S) ≈ (P -> R) & (P -> S)
```

The first equation splits the accepted inputs into alternatives. The second
combines simultaneous result requirements. Substituting `Object | Bool ≈ Object`
in the first equation derives `Object -> R <: Bool -> R`.
The second equation gives the corresponding result rule.

Intersections can also combine different inputs and results:

```text
(Bool -> Bool) & (NoneType -> NoneType)
    <: (Bool | NoneType) -> (Bool | NoneType)
```

The same function meets both requirements. A Bool argument requires a Bool
result, and a NoneType argument requires a NoneType result.
If an argument meets two input requirements, the returned value must meet both
result requirements.

## Validate the hierarchy before checking methods

Subtyping needs to know which classes exist and how they inherit.
Method typing then uses subtyping to check arguments, results, and overrides.
Full program validation must follow that order:

```text
WellFormedClassHierarchy → subtyping → method typing → WellTypedClassHierarchy
```

The *class table* is the list of declarations. The two hierarchy records
contain data and validation evidence about that list.

`WellFormedClassHierarchy ct` supplies the classes selected by lookup, their
computed MROs, and the builtin class restrictions. Object is the root.
Bool, NoneType, and BoundMethod are *sealed*: a different class cannot inherit
from them.

These facts define the class context used by the type equations.
Every class name in a type must occur in that context.
The Lean proofs package an annotation with proof that its names are declared.
Derived types can reuse this evidence. Subtyping therefore applies to valid annotations;
an unknown class name does not denote bottom.

`WellTypedClassHierarchy ct` extends the hierarchy record with method typing
and declaration checks. In particular:

- Each method body has its declared result type under its receiver and argument types.
- The method selected by a class accepts each ancestor method's inputs and returns results below that ancestor's result type.
- Method names and direct parents do not repeat within a selected declaration.
- Method signatures use known class names, and declarations sharing a class name agree.

The override requirement applies to inherited methods as well as explicit
overrides. A call checked against an ancestor's signature can run on a subclass,
so the subclass's selected method must meet that signature.

## Account for future subclasses

A class annotation includes possible subclass objects. Suppose A and B each
inherit Object. A future class C could inherit both:

```text
class C(A, B): ...
```

An object of C would have both types A and B. Thus, `A & B` can remain possible
even when the current class table has no common subclass.
The absence of a declared common subclass is insufficient to derive
`A <: negClass B`.

Inheritance order can rule out such a subclass:

```text
class A(X, Y): ...
class B(Y, X): ...
```

A subclass of A must preserve X before Y. A subclass of B must preserve Y before X.
No single MRO can preserve both orders, so `A & B` is bottom in this case.
The C3 check also detects conflicts that involve more than two classes.

### Describe a possible subclass with known names

Types cannot refer to a class name that the program has not declared.
They can still describe whether an object's MRO includes each known class.

A *complete class conjunction* makes that choice for every known name.
For example, with names Object, A, and B, one choice is
`Object & A & negClass B`. The actual context also includes the sealed builtins.

A valid choice must include Object and every ancestor of an included class.
It must obey sealing and have an MRO order compatible with all included classes.
These conditions determine which choices the subtype checker retains.

The hierarchy proofs establish both directions of this characterization.
Every class in a valid extension gives such a choice.
Every valid choice has an extension that realizes it, possibly by adding a
fresh class with no methods. Each choice can use a separate extension.

This result concerns inheritance. It does not establish full method typing for
every constructed extension. For example, suppose A supplies `m: Bool -> Bool`
and B supplies `m: NoneType -> NoneType`. A subclass C(A, B) can have a valid MRO
but select A.m, which fails B.m's input requirement.
The program needs a compatible method and a typing proof for its body.

The development also does not prove general transport of every subtype proof
to an extended class table. Its extension results justify the class possibilities
and impossibilities used by the type equations.

## Check expressions with these subtype rules

Expression typing uses the hierarchy and an environment that assigns types to
variables. Attribute access obtains a method's function type. A call checks
that the argument type is below the function's input type, then uses its result type.

A conditional requires a Boolean condition and combines the possible branch
results with a union. A class test also refines the tested variable:

| Branch of `if isInstance(x, C)` | Type of x |
| --- | --- |
| Positive | `T & C` |
| Negative | `T & negClass C` |

T is x's type before the test. Each branch keeps that information and adds
the fact established by the test.

An expression can have more than one type. If it has T and U, it can also have
`T & U`. For example, different function requirements can describe the same
bound method. The executable checker must account for these combined typings.

### Decide subtyping

The subtype checker rewrites a type as a union of intersections.
Each intersection contains a complete class conjunction and any function
requirements that apply to that class choice. The type laws justify this rewrite.

The checker requires every source alternative to fit a target alternative.
Class choices must agree. Function comparison combines all applicable source
requirements, as in the Bool and NoneType example above.

For a requested result R, the checker considers nonempty groups of function
requirements whose combined results are below R. Each group applies where all
its inputs hold. The union of those input types must cover the target input.
This permits several requirements to justify one function subtype.

Recursive comparisons inspect function inputs and results with less function
nesting. The proof connects the complete calculation to the equations in both
directions: an accepted comparison gives a subtype derivation, and every subtype
derivation is accepted. A rejected comparison therefore proves that no such
derivation exists.

### Decide expression typing

The expression checker constructs a finite collection of possible result types,
including intersections needed to cover combined typings.
It accepts a requested type when a candidate is below that type.

Completeness means that every declarative result type has a candidate below it.
Together with candidate soundness and the subtype checker, this proves agreement
between executable checking and the typing rules.

These exhaustive calculations support constructive proofs. Large class lists
or repeated calls on returned function types can exceed Lean's evaluation limits.
The examples check concrete queries within those limits.

## Connect typing to execution

The safety proof must connect the method signature found during checking to
the method body that executes. Heap validity supplies that connection:
a bound method stores a real receiver and a method from that receiver's MRO.
Method typing and the override requirement then justify execution of that body.

Heap validity also connects builtin class names to object storage.
Bool objects are the two Boolean singletons, and a BoundMethod object contains
exactly the receiver and method data needed for a call.
Each execution step preserves these requirements.

One call case needs special care. If `P -> R <: Q -> S`, the equations imply
`Q <: P`. They imply `R <: S` only when Q is not below bottom.
An empty input places no result requirement on a function.

While the argument is being evaluated, it can have type bottom and run forever.
If it returns, the proof has an actual typed value.
No typed heap value can have type bottom, so the input is nonempty and the result
comparison applies. Method body typing can then establish the required result.

The proof uses each actual object's MRO for class membership and exclusion.
`objectTypeLowerBound` constructs a type below every type assigned to that
object reference. This supports the union and exclusion cases; method execution
also needs the proof that the body is typed, as described above.

Preservation proves that a step keeps the heap and machine types valid.
Progress proves that a valid unfinished state can take a step.
Together, these results give static type safety: from a well-typed hierarchy,
a valid heap, and correctly typed variable values, a typed expression cannot fail.
If it finishes, its result has the expression's type. It can also run forever.

## Key definitions and results

| Lean name | Role |
| --- | --- |
| `HasType` | Declarative expression typing under a validated hierarchy and variable types. |
| `ValueHasType` | Typing of object references in a heap. |
| `checkSubtypeBool_iff_subtype` | The Boolean subtype checker agrees with subtyping defined by equations. |
| `checkHasType?_iff_hasType` | The expression checker agrees with declarative typing for valid inputs. |
| `SmallStep.program_soundness` | Static safety from the initial heap and an empty variable environment. |

The public imports are `FwPython.Static.Language` for language definitions and
`FwPython.Static` for the complete static development.

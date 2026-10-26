# Gradual typing

This document explains how FwPython combines known and unknown type information.
It follows a source call through type inference, compilation, runtime checks,
and the safety guarantees. The [static design](type_system.md) supplies the
type equations and inheritance rules used here.

## Why unknown types need runtime checks

Suppose a bound method f returns its Bool argument, but x has unknown type:

```text
f: Bool -> Bool
x: any
f(x)
```

The source checker permits this call. If x is TRUE, the call can return TRUE.
If x is NONE, the method's parameter check fails before its body runs.
The failure report identifies the method's Bool parameter requirement.
FwPython calls this report *blame*.

The annotation `any` represents unknown type information. It differs from
Object, which is a known static type containing every object.
An Object annotation alone cannot meet a Bool input requirement.
An `any` annotation permits a check to establish whether the actual value is Bool.

The source language has the static type forms plus `any`.
Union means alternative types; intersection means simultaneous requirements.
A function type `P -> R` specifies input and result requirements, but gradual
execution can report blame when a runtime check rejects a value.

## From source types to checked execution

A program passes through three stages:

1. Source inference assigns a type to each expression.
2. Compilation uses those types and the requirements of surrounding expressions to insert checks.
3. The checked runtime evaluates the compiled program and reports any failed requirement.

The source type describes the information inferred for an expression.
The *expected type* describes what the surrounding expression needs.
These types can differ. For example, a value inferred as `any` can occur where
Bool is expected; compilation inserts the Bool check.

All runtime values are object references. A bound method stores its selected
method and receiver. Method selection follows the *method resolution order*
(MRO), the ordered list of a class and its ancestors.

Gradual type comparisons use the static inheritance facts. Erasure replaces
method annotations and bodies but preserves class names and MROs.
`WellFormedGClassTableCore.toWellFormedClassHierarchy` provides that static
hierarchy for subtype comparisons. This works because those comparisons need
inheritance information before they need method body typing.

## Decide which source calls to permit

The checker must permit calls that can need runtime checks while retaining
known result information for later expressions.
The call in the first example illustrates both requirements:
x needs a Bool check, but f's declared Bool result remains useful.

### Approximate unknown information with two bounds

To interpret the uncertainty in an annotation, consider replacing each
occurrence of `any` independently with a static type. For example,
`any -> Bool` can become `Bool -> Bool` or `NoneType -> Bool`.
These replacements are called *materializations*.

The checker uses a lower bound and an upper bound in the static subtype order.
The lower bound is below the possible replacements; the upper bound is above them.
Together they describe an *interval*, meaning the static types between the bounds:

```text
lowerBound G <: T <: upperBound G
```

The Lean relation `MaterializesTo` tests this interval membership.
The interval is an approximation of independent replacements, not an exact
enumeration of them.

| Annotation | Lower bound | Upper bound |
| --- | --- | --- |
| `Bool` | `Bool` | `Bool` |
| `any` | `bottom` | `Object` |
| `any & Bool` | `bottom` | `Bool` |
| `any -> Bool` | `Object -> Bool` | `bottom -> Bool` |

Function inputs reverse the bound direction because input subtyping reverses.
The last interval admits `Bool -> Object`, although replacing the unknown input
of `any -> Bool` always keeps a Bool result. This example shows why result
selection also needs the original function annotations.

### Use the lower bounds for call acceptance

For valid callee annotation C and argument annotation A, the source call is
accepted exactly when:

```text
lowerBound C <: (lowerBound A -> Object)
```

Object leaves the result unrestricted during this acceptance check.
The result is selected in a separate step.

For `Bool -> Bool` called with `any`, the argument lower bound is bottom.
The subtype comparison accepts the call, and runtime checking decides whether
the actual argument is Bool.

The full callee annotation matters. `Bool | (Bool -> Bool)` called on Bool is
rejected because the callee might be a noncallable Bool value.
Knowing only that a value has class BoundMethod also gives no guarantee that
it accepts Bool. A BoundMethod call with an `any` argument can be accepted,
but its result is unknown and its actual input is checked at runtime.

The acceptance theorem proves agreement with this bounds comparison.
It does not characterize all independent replacements of `any`.

## Keep the result information needed by later calls

For an accepted call on one function annotation `P -> R`, inference keeps R.
Thus, the first example gives a Bool result even though its argument is `any`.
A later call requiring NoneType rejects that result during source checking.
Unknown input information alone does not erase an explicit result annotation.

Intersections require more care because one function must satisfy several rules:

```text
f: (Bool -> Bool) & (NoneType -> NoneType)
```

| Argument type | Selected result | Reason |
| --- | --- | --- |
| `Bool` | `Bool` | The Bool requirement applies. |
| `NoneType` | `NoneType` | The NoneType requirement applies. |
| `Bool \| NoneType` | `Bool \| NoneType` | Both requirements together cover the input alternatives. |
| `Bool & NoneType` | `Bool & NoneType` | Both requirements apply; this input cannot return a value. |

A union of functions has a different meaning: the callee can be either
function. The input must work for each alternative, and the result can come
from either one.

### An unknown argument can select different results

Consider a variable with these requirements:

```text
f: (Object -> Bool | NoneType) & (Bool -> NoneType)
x: any
consume: NoneType -> Bool
```

A Bool argument meets both inputs, so the result must be NoneType.
A NoneType argument meets only the Object input, so its result can be
Bool or NoneType.

Since x is `any`, the source result must account for both cases.
That uncertainty permits `consume(f(x))` to pass the source check.
If f actually returns Bool, consume's parameter check reports blame.

### Represent several possible results

For two static case results X and Y, the checker uses:

```text
(X & Y) | (any & (X | Y))
```

Its lower bound is `X & Y`; its upper bound is `X | Y`.
These are the tightest bounds that include both results.

In the preceding example, X is NoneType and Y is `Bool | NoneType`.
The result therefore has lower bound NoneType and upper bound `Bool | NoneType`.
The lower bound permits the later NoneType call; the runtime checks enforce its
requirement on the actual value.

This representation can admit extra static types between its bounds.
For example, an interval that includes Bool and Object also includes
`Bool | NoneType`. The approximation can therefore lose information.
When all cases give the same result, the checker keeps that result without
adding an unknown part.

For gradual case results, the same construction intersects their lower bounds
and unions their upper bounds. An unknown part of the callee can also impose
unknown result requirements. For example, `any & (Dog -> Dog)` can have a result
more specific than Dog. This differs from `any -> Dog`, which explicitly fixes
the result to Dog.

### Preserve unknown inputs in returned functions

Bounds can also hide information needed by a second call:

```text
f: (Bool -> (any -> Bool)) & (NoneType -> (Bool -> Object))
x: any
```

If x is replaced with NoneType, the first call selects `Bool -> Object`.
If x is replaced with Bool, it selects `any -> Bool`.
Keeping only the latter type would lose the Object result possible on a later
Bool call.

The selector therefore keeps distinct result requirements when either contains
an unknown function input. Equal results remain unchanged.
This rule retains information that bounds alone can hide, but the combined
approximation can still lose precision in later calls.
Exact result selection for all independent replacements is not proved.

An empty callee type gives result bottom because no callee value can reach the
call. Empty union alternatives add no possible result.
An accepted call with no selected result uses bottom for an empty argument
upper bound and `any` otherwise. These cases distinguish unreachable calls
from calls whose result is unknown.

## Attribute lookup and class tests

Attribute lookup on `any` gives result `any`; the runtime checks whether the
actual object provides the method. For `A | B`, source lookup must succeed on
both alternatives because the object can have either type. It combines the
two method types with a union.

For `A & B`, one successful lookup is sufficient because the object must meet
both class requirements. If both lookups succeed, the method value must meet
both function requirements, so the result is their intersection.

A class test refines a variable using the information available before the test:

| Type before `isInstance(x, C)` | Positive branch | Negative branch |
| --- | --- | --- |
| `any` | `C` | `negClass C` |
| `A & any` | `A & C` | `A & negClass C` |
| `A \| any` | `C` | `negClass C` |

The intersection retains A because it is a simultaneous requirement.
The union does not guarantee A. The test establishes class information;
it does not inspect a function's input or result annotations.

## Compile and enforce the requirements

The compiler represents a runtime check type as a *target*.
A target is the expected type in a form used by the checked language.

Class checks inspect the object's MRO. Class exclusion checks require the class
name to be absent. A union check permits either part; an intersection check
requires both parts. A successful check returns the same reference and does
not change the heap.

A function check verifies that the value is a bound method.
It cannot test all possible inputs or run the method to predict its results.
Those requirements are checked when the call takes place.

### Check the caller and the method

For the first example, the function expression must produce a bound method.
Compilation also checks the argument against the caller's selected input target.

That target retains the argument annotation's class information and replaces
function parts with `any`. It is a permitted class-formula target.
The method's parameter check applies its declared requirement.

The runtime then applies the method's stored requirements:

1. Check the actual argument against the method's declared parameter type.
2. Run the compiled body with the receiver and argument bound.
3. Check any returned value against the method's declared result type.
4. Check that value against the result type expected by the caller.

The last two requirements can differ. Checking both protects the method's
declaration and the surrounding expression.
A failure reports the requirement of the check that rejected the value.

### Limit the types used by runtime checks

Source types include intersections of function requirements, but runtime
targets have a restricted form. `CheckedTargetTy` states this restriction.

Targets permit class types, class exclusions, `any`, bottom, and unions and
intersections of these forms. They also permit function types whose input and
result targets are permitted, and unions of permitted targets.

A function can be intersected with a class expression only when every bound
method satisfies that expression. A direct intersection of two function
signatures, such as `(A -> B) & (C -> D)`, is not a permitted target.
Function types can still occur inside another function's input or result.

These restrictions let the execution proof use the evidence produced by each
check. Compilation must supply permitted targets with known class names.
A source annotation is therefore not automatically a permitted runtime target.

## Explain failures at their source

Compilation attaches a source location and a requirement to each operation
that can report blame. The requirement identifies a type check or method lookup.
For a method, it can identify the parameter or declared result.

A blame report contains that source requirement and the runtime operation and
value that failed. The report is supplied by the failing operation, so runtime
checks do not need to reconstruct source locations from the heap.

`Checked.blame_adequacy` proves that a final blame report describes a requirement
violated in the final heap. The theorem connects the report to the failed check
or lookup.

## State the safety guarantees with their assumptions

The proof tracks valid heap objects, correctly typed variable values, and
correspondence between the source and compiled class tables.
It also tracks the type of the current expression and the requirements of
the remaining operations. Each execution step preserves these facts.

`ElaboratesProgramAt` records a valid source typing proof, the corresponding
compiled program, and a permitted expected result type P with known class names.
From the initial heap and an empty environment, `gradual_soundness_at` proves:

- If execution finishes successfully, the result satisfies P.
- A finished execution can instead report blame.
- Such an execution cannot produce `runtimeError`.

These statements do not require termination. They concern correctly compiled
programs; malformed checked code supplied directly to the machine is outside
the theorem's assumptions. For functions, runtime satisfaction establishes that
the value is a bound method; input and result requirements are enforced at calls.

### Translate statically typed programs

A stronger result excludes blame for static programs with the required
translation evidence. `EmbeddedStaticElaboration` connects the static typing
of the main expression and method bodies to their gradual and checked versions.

Translated method input and result annotations must be permitted runtime
targets. For example, a method annotation that directly intersects two function
signatures is outside this theorem's scope.
The development does not construct this translation evidence for every
statically typed program.

Given that record, `embedded_static_no_blame` excludes final blame, and
`embedded_static_success` proves that a finished execution returns a value.
The Bool identity method is a concrete example in
[MethodEmbeddingExamples.lean](../FwPython/Examples/Gradual/MethodEmbeddingExamples.lean).

### Limit the claims about annotation changes

The call-acceptance proof shows that enlarging either bounds interval preserves
acceptance of one call on a fixed valid class table.
It does not compare the inferred results that later calls use.
Thus, it does not prove that replacing annotations with `any` preserves
acceptance or behavior of a whole program.

The safety result comes from compiled checks, while the bounds approximation
controls which source expressions are accepted. These are separate guarantees.
The detailed regression examples include calls on inferred function results
because a first-call type alone does not show how later calls behave.

## Key definitions and results

| Lean name | Role |
| --- | --- |
| `GSrcInfer` | Source expression typing, including the computed call result. |
| `callSourceTy?_accepts_iff` | Exact agreement between call acceptance and its bounds comparison. |
| `compileCheck` | Compilation of a typed source expression at an expected type and source location. |
| `compileCheck_checked` | The compiled expression has its expected checked type. |
| `Checked.gradual_soundness_at` | Execution safety for a correctly compiled whole program. |

The public imports are `FwPython.Gradual.Language` for language definitions and
`FwPython.Gradual` for the complete gradual development.

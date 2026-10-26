#set page(
  paper: "us-letter",
  margin: (x: 0.9in, y: 0.85in),
)

#set text(size: 10.5pt)
#set par(justify: true, leading: 0.68em)
#set heading(numbering: "1.")
#show table: body => block(breakable: false, body)

#let formal(body) = text(size: 10pt, style: "italic")[#body]

#let rule(name, premises, conclusion, barWidth: 17em) = block(width: 100%, breakable: false)[
  #align(center)[
    #stack(
      dir: ttb,
      spacing: 0.4em,
      formal(premises),
      grid(
        columns: (barWidth, auto),
        column-gutter: 0.85em,
        align: center,
        box(width: barWidth)[#line(length: 100%)],
        box[
          #align(right)[#text(size: 8.2pt, fill: luma(45%), style: "italic")[#name]]
        ],
      ),
      formal(conclusion),
    )
  ]
]

#let theorem(kind, name, statement, proof: none) = [
  *#kind.* _#name._ #statement
  #if proof != none [

    _Proof idea._ #proof
  ]
]

#align(center)[
  #text(size: 18pt, weight: "bold")[FwPython]
  #v(0.3em)
  #text(size: 11pt, fill: luma(40%))[
    A Lean 4 specification and type safety proofs for a small
    object-oriented language with static and gradual typing
  ]
]

= Overview

FwPython formalizes a small object-oriented language with multiple inheritance
and first-class bound methods in Lean 4. Its static types combine class membership,
class exclusion, and function requirements through unions and intersections.
The development connects these types to method selection and execution.

Static subtyping is defined by type equations. An executable comparison is proved
to accept exactly the subtypes derived from those equations. Class intersections
account for possible future subclasses while respecting C3 method resolution
order and builtin sealing. Typed method bodies and compatible selected methods
then connect the subtype algebra to static type safety.

The gradual system adds unknown type information, written `any`. Source inference
retains declared function requirements while approximating unknown information
with subtype bounds. Compilation inserts runtime checks with explicit source
requirements. A correctly compiled execution that finishes returns a value of
the expected type or reports a failed requirement as blame. Both safety results
permit nontermination. The comparisons, method resolution search, compiler, and
their proofs are constructive and use no classical choice.

= Runtime objects

A program contains a class table and one main expression. The class table lists
the class declarations and their methods. C3 computes each class's *method
resolution order* (MRO): the class and its ancestors in method lookup order.
Lookup selects the first class in that list that declares the requested method.

Each class declares an ordered list of direct parents. A method declares its
name, receiver variable, one argument variable, input and result types, and an
expression body. The expression forms are:

```text
e ::= x | new C | e.m | e(e) | NONE | TRUE | FALSE
    | if e then e else e | isInstance(x, C)
```

This is notation for the abstract syntax; the project has no text parser.
`isInstance` tests a variable, which permits branch typing to refine its type.

The machine evaluates expressions using a heap and a variable environment.
Every value is an object reference. A heap object stores a runtime class name
and a *payload*: either an ordinary-object marker or a method definition paired
with its receiver. The receiver is the object on which the method runs.

Method attribute lookup allocates an object of class BoundMethod containing this
pair. Such a value has both a class type and a function type. Only bound methods
can be called; the language has no separate function objects or user-defined
`__call__` methods.

The initial heap contains NONE of class NoneType and TRUE and FALSE of class
Bool. `new C` requires a declared class and excludes Bool, NoneType, and
BoundMethod. Constants and method attribute lookup supply values of these classes.

= Static Core

== Judgments and Type Language

Fix a class table `ct` and its validated hierarchy. Let Γ assign types to
variables, h be a heap, e an expression, v an object reference, and T a type.
Every class name in a type must be declared. A *valid type package* pairs an
annotation with proof of this condition. The Lean judgments are:

- `HasType hierarchy Γ e T`: expression `e` has type `T` under variable types `Γ`.
- `ValueHasType hierarchy h v T`: value `v` in heap `h` has type `T`.
- `FindMethodType ct cname methodName paramTy returnTy`: method lookup finds the stated input and result types.
- `TypeEquivalence context T U`: the type laws derive an equation between valid type packages T and U.
- `IsSubtype hierarchy T U`: T and U are valid annotations, and the equations prove that `T | U` equals `U`.

`hierarchy : WellFormedClassHierarchy ct` supplies the class declarations found by
lookup and their computed MROs.
The execution proofs require a well-typed class hierarchy and a well-formed heap.
These requirements supply the inheritance, method lookup, and object storage facts used in the proofs.

The static type language is `Ty`.
Method annotations, expression types, runtime types, and subtype checks use this language.
The following table gives the type forms.

#table(
  columns: (1.7fr, 2.4fr),
  inset: 6pt,
  stroke: luma(80%),
  [Type form], [Meaning],

  [`class C`], [The runtime class has `C` in its MRO.],
  [`negClass(C)`], [The runtime class does not have `C` in its MRO.],
  [`P → R`], [A callable object. Calls on `P` inputs must not fail. Any returned result must have type `R`.],
  [`T | U`], [Values with type `T`, type `U`, or both.],
  [`T & U`], [Values with both type `T` and type `U`.],
  [`bottom`], [The empty type.],
)

Every value has type `class Object`.
A call of type `P → R` can run forever.
This type restricts returned results and failures; it does not require termination.

== Subtyping

Subtyping determines whether a value of one type can be used where another
is required. Every Bool is an Object, for example, so `Bool <: Object`.
We express this through a type equation: adding Bool as an alternative in
`Bool | Object` does not change Object. In general,

```text
T <: U  means  T | U ≈ U
```

Here, `≈` is equality derived from the type laws. To prove a subtype rule,
we show that its defining union equation follows from those laws.

=== The laws behind the basic rules

Union combines alternatives, while intersection combines requirements.
Their laws form a bounded distributive lattice: we can reorder and regroup
both operations, repeated types have no effect, intersection distributes
over union, bottom is the least type, and Object is the greatest.

These equations explain the basic subtype rules. Repetition gives
`T | T ≈ T`, hence `T <: T`. Absorption gives `T | (T & U) ≈ T`, hence
`T & U <: T`: a value satisfying both requirements satisfies T. Equations
also compose to give transitivity. If `T | U ≈ U` and `U | V ≈ V`, then

```text
T | V ≈ T | (U | V) ≈ (T | U) | V ≈ U | V ≈ V
```

so `T <: V`. The same laws give the equivalent subtype test `T & U ≈ T`,
which is convenient for proofs about simultaneous requirements.

=== Adding the class hierarchy

The lattice laws tell us how to combine types; the class laws supply the
hierarchy facts. If A occurs in C's MRO, every C object also belongs to A.
The inheritance equation records this as

```text
class C & class A ≈ class C
```

Using the intersection test above immediately gives `class C <: class A`.
In particular, Bool's MRO contains Object, which justifies the example at
the start of this section. Class exclusion and builtin sealing supply further
hierarchy equations, described in @class-exclusion.

=== Deriving the function rule

A function type `P → R` requires calls on P inputs to accept those inputs and
give every returned result type R. The function equations describe how these
input and result requirements combine:

```text
(P | Q) → R ≈ (P → R) & (Q → R)
P → (R & S) ≈ (P → R) & (P → S)
```

The first says that accepting either input means satisfying both input
requirements. Since `Object | Bool ≈ Object`, it gives
`(Object → R) & (Bool → R) ≈ Object → R`. By the intersection test,
`Object → R <: Bool → R`: accepting a broader input makes a function usable
where a narrower input is required.

The second equation explains the result direction. Since
`Bool & Object ≈ Bool`, it gives
`(P → Bool) & (P → Object) ≈ P → Bool`. Thus,
`P → Bool <: P → Object`: returning a narrower result satisfies a broader
result requirement. The general rule follows from these two derivations:

#rule(
  "S-Callable",
  stack(
    dir: ttb,
    spacing: 0.35em,
    [P' <: P],
    [R <: R'],
  ),
  [P → R <: P' → R'],
)

This also explains how to summarize different requirements on one function. From
`P → R` and `Q → S`, result subtyping first widens each result to `R | S`. The
first function equation applies once both result types agree:

```text
(P → (R | S)) & (Q → (R | S)) ≈ (P | Q) → (R | S)
```

Composing result widening with this equation gives

```text
(P → R) & (Q → S) <: (P | Q) → (R | S)
```

If the two requirements have the same input type P, both results are required;
the second function equation gives `P → (R & S)` directly.

One further equation connects function types to callable objects:
`bottom → R ≈ class BoundMethod`. With no possible input, the result requirement
places no restriction on results, but the value must still be callable.
Because bottom is below every input type, the function rule also gives
`P → R <: bottom → R`, so every function value belongs to BoundMethod.
An empty result has a different meaning: `P → bottom` can describe a method
that runs forever on P inputs, and therefore need not be an empty type.

All these rules are derived in Lean from `TypeEquivalence` in `Algebra.lean`.
The equations use a validated hierarchy and type packages whose class names
are declared. Operations preserve that validity, so derivations can build
intermediate types without repeating name checks.

`WellFormedClassHierarchy` supplies the names and valid MROs needed by these equations.
Method typing itself uses subtyping, so the hierarchy facts must be available before
method bodies are checked. `WellTypedClassHierarchy` extends `WellFormedClassHierarchy`
with typed method bodies, compatible overrides, and declaration consistency.
Its method typing proofs justify method execution.

== Class exclusion <class-exclusion>

`negClass(C)` means that the object's runtime class does not have `C` in its MRO.

The following laws state three facts.
A sealed class excludes names absent from its MRO.
Every object either has class `C` or excludes that class.
No object can both have and exclude class `C`.

#rule(
  "S-SealedClass-NegClass",
  stack(
    dir: ttb,
    spacing: 0.35em,
    [B ∈ sealedClasses],
    [ct(B) = b],
    [MRO(b) = M],
    [D ∉ M],
  ),
  [class B <: negClass(D)],
)

#rule(
  "S-Object-Cover",
  [],
  [class Object <: class C | negClass(C)],
)

#rule(
  "S-ClassSelf-NegClass-Bottom",
  [],
  [class C & negClass(C) <: bottom],
)

`sealedClasses` contains Bool, NoneType, and BoundMethod. No different class can
inherit from these sealed classes. `WellFormedClassHierarchy` supplies this restriction.

A valid future hierarchy can give two user classes a common subclass, so their
intersection remains possible. Conflicting MRO orders can rule out such a class
and make the intersection empty.

`Negation.lean` provides proofs that use these class membership and exclusion facts.
For example, a callable value cannot have type `negClass(BoundMethod)`.

== Static Typing and Runtime Typing

The expression typing judgment

#align(center)[#formal([Γ ⊢ e : T])]

assigns a type to an expression.
Attribute access finds a method on the receiver's class.
A call requires a function type and an argument that fits its input type.
A conditional requires a Boolean test and returns the union of its branch result types.
The same expression can receive an intersection type when it satisfies both component types.

The test `isInstance(x, C)` adds information about `x` in each branch:

#rule(
  "T-IfIsInstance",
  stack(
    dir: ttb,
    spacing: 0.35em,
    [Γ(x) = T],
    [ct(C) is defined],
    [Γ[x ↦ T & class C] ⊢ e_t : R_t],
    [Γ[x ↦ T & negClass(C)] ⊢ e_f : R_f],
  ),
  [Γ ⊢ if isInstance(x, C) then e_t else e_f : R_t | R_f],
  barWidth: 29em,
)

The positive branch adds type `class C` to the type of `x`.
The negative branch adds `negClass(C)`.
The conditional returns the union of the two branch result types.

`ValueHasType hierarchy h v T` assigns a type to a heap reference.
The same reference can have a class type, a function type, or a class exclusion type.
Subtype rules and intersection rules can assign further types.

`ValueHasType.objRefNegClass` requires the object's runtime MRO to exclude the tested class.
The execution proof uses the actual MRO check result.

== Future class hierarchies

If A and B inherit only Object, a future program can add `C(A, B)`. The
intersection `A & B` must therefore remain possible even when the current
program has no common subclass. A *complete class conjunction* fixes whether
each known class is included or excluded. A *common MRO order* has no repeated
name and contains every included class's entire MRO in its order.
`hasValidClassOrder` checks it by applying C3 merge to those MRO lists.

A conjunction meets the *conjunction constraints* when it includes Object and
every included class's ancestors, respects builtin sealing, and has a common
MRO order. The subtype comparison keeps these conjunctions because they can
describe objects of an existing class or a future subclass.

Future classes must still have valid C3 MROs and respect builtin sealing. This
excludes a common subclass of `A(X, Y)` and `B(Y, X)`: one parent requires X before
Y, while the other requires Y before X. Each parent is valid on its own, but no class
can preserve both orders.

For any class in an extension with a valid hierarchy,
`classIntersectionOfExtension` computes its complete class conjunction from its
MRO and returns a proof that the conjunction constraints hold. This justifies
making a type empty when those constraints fail. Conversely,
`extendWithClassIntersection` constructs a separate valid extension for each
complete class conjunction that meets the constraints. The conjunctions can use
different extensions; this justifies keeping every conjunction that meets the
constraints.

This is a guarantee about ancestry and MROs. Static program checking also requires
compatible methods. An empty subclass can inherit two methods with the same name and
incompatible signatures; it has a valid MRO but fails `LiskovCondition`, so the
program is rejected.

== Deciding subtyping

`splitIntoIntersections` computes a type's *normal form*: a list of
intersections whose union equals the original type. It also returns a proof of
that equation. The normalizer distributes `(A | B) & C` into `(A & C) | (B & C)`
and splits class types and exclusions into complete class conjunctions.
Inheritance, sealing, and incompatible MROs determine which conjunctions remain
possible. The lattice and class equations justify these transformations. This
puts alternatives and class restrictions into a form the subtype comparison can
inspect, with a proof that the transformations preserve the original type.
Function requirements are compared together, because separate requirements can cover
separate inputs. For example,

```text
(Bool → Bool) & (NoneType → NoneType)
```

covers a `Bool | NoneType` input with a `Bool | NoneType` result, even though neither
input requirement covers that union alone. The recursive check decreases an explicit
depth limit. Smaller function nesting keeps a sufficient limit from running out.
Increasing an already sufficient limit leaves the answer unchanged; this is called
*depth independence*.

#theorem(
  "Theorem",
  "Subtype comparison agrees with the type equations",
  [For valid type packages, `checkSubtypeBool_iff_subtype` states that the
   Boolean comparison accepts exactly the subtypes derived from the equations.],
  proof: [Induction on function nesting turns a true answer into a subtype proof.
    A false answer must rule out every possible derivation, including ones that
    rewrite inside types or pass through intermediate types. The proof checks
    that each stated equation is accepted in both directions and that comparison
    respects component rewrites and transitivity. Depth independence handles
    intermediate types with deeper nesting. Every derivation therefore passes,
    so a false answer rules out a subtype proof.],
)

The proof-producing decision is `WellFormedType.subtypeDecidable`. Raw
annotations enter through name validation; subsequent comparisons reuse the
proof stored with each type. The subtype relation itself is defined by the
equations, so its definition does not depend on the subtype comparison.

== Deciding expression typing

Declarative typing can assign several types to one expression, including their
intersection. An executable checker therefore needs more than one inferred
type. `inferBasis` constructs a finite collection of valid candidate types and
closes it under nonempty intersections. Each candidate has a typing proof.
Completeness means that every declarative result type has a candidate below it.

To check a call without executing it, `callableSummaries` produces input and
result pairs called *summaries*. Each pair describes a function type above the
callee's type. An argument below the pair's input permits the call, and the
pair's result is compared with the requested type. Combining requirements
accounts for overlapping inputs of one function and for alternative functions.

A callee that could be an ordinary object fails checking. If its type is below
bottom, its summary is `(Object, bottom)`: every argument fits, but evaluating
the callee cannot return. For a callable type that is not below bottom, an empty
collection of requirement subsets gives a summary equivalent to
`(bottom, bottom)`. It accepts an argument expression that cannot return, so
execution cannot reach the call. Each summary supplies the input and result
types for an instance of the static call typing rule.

`checkHasType?` accepts a requested annotation T when its class names are valid
and some candidate is below T. For a well-typed hierarchy and valid variable
types, `checkHasType?_iff_hasType` proves agreement with declarative typing.
Candidate soundness and subsumption justify acceptance. Candidate completeness
and subtype decidability ensure that every typing derivation is accepted.

== Proof of static type safety

The heap rules require a BoundMethod object to contain a receiver and method.
Ordinary object creation excludes that class.
Method allocation creates an object with the required class and payload.
Every execution step preserves these facts.

The proof uses `objectTypeLowerBound`: it fixes the object's class membership
from its actual MRO and, for bound methods, adds `Object → bottom`. With a
well-typed class hierarchy and a well-formed heap, `valueHasType_lowerBound`
places this type below every type assigned to a reference whose lookup finds that exact object.
For a known class D, this *object lower bound* is below an exclusion of D exactly
when D is outside the MRO. This type supports algebraic inversion; method body
typing supplies the execution guarantee.

The object's own class C is inside the MRO, so the
object lower bound cannot be below an exclusion of C. If it were below bottom,
it would be below that exclusion too, giving a contradiction.
`objectTypeLowerBound_nonempty` states that the object lower bound is not below
bottom. If a typed heap value had type bottom,
`valueHasType_lowerBound` would place its object lower bound below bottom,
contradicting that nonemptiness theorem. This proves
`valueHasType_bottom_impossible` for every typed heap value under a well-typed
class hierarchy and a well-formed heap.

A method declared `Bool → Bool` can be called with required result Object.
Preservation must relate its declared Bool result to that Object result once the
argument returns. That return matters: an argument expression of type bottom can
run forever, and `bottom → R` imposes no result restriction. Once argument
evaluation produces a typed value, its type cannot be below bottom. Function
inversion can then compare the declared result with the result required at the
call.

Preservation proves that execution keeps the heap and machine types valid.
Progress proves that a valid state can take a step or has already finished.
The `isInstance` cases use the actual class membership test result.
`Heap.initial_wellFormed` proves every heap rule for the pre-allocated None and Boolean objects, including `boundMethodShape`.
`SmallStep.program_soundness` applies static safety to a typed program that starts with that heap and an empty environment.

#theorem(
  "Theorem",
  "Static Type Soundness",
  [`SmallStep.soundness` assumes a well-typed class hierarchy, a well-formed heap,
   and runtime variable values that satisfy their assigned types. If expression e has type T
   and execution terminates, it returns a value of type T.],
  proof: [Preservation proves that each step keeps the heap and machine types valid.
    Progress proves that a valid unfinished state can take a step.
    The final state contains a successful value of type T.],
)

= Gradual Layer

== Unknown types and runtime checks

`any` permits unknown type information.
For example, a value of type `any` can reach an expression that requires a function.
The runtime checks whether the value is a bound method before calling it.
If this check fails, the machine reports blame.

The compiler records a source location and requirement for each check.
`BlameInfo.obligation` identifies the reported requirement.
`BlameInfo.cause` identifies the operation and value that failed.

The type safety theorem applies to correctly typed compiled programs.
If execution reaches a final state, the result is a value of the expected type or blame.
The theorem excludes `runtimeError` for these executions.
It does not require termination.

== Program translation

The program passes through three stages:

+ `GSrcInfer` assigns one source type to each expression.
+ `compileCheck` translates the expression and adds runtime checks.
+ The checked machine executes the translated program.

The source environment stores one type for each variable.
The compiler selects the type used by each runtime check at the use of an expression.
This check type is called a *target*.
The source type and the target can differ.

The execution proofs use the checks stored in the compiled expression.
They prove that each machine step preserves the typing requirements.

== Gradual source language

The source type language `GTy` adds `any` to the static type forms.
`any` represents unknown type information. Object is a known type containing
every value; `any` permits runtime checks to establish more specific facts.

Erasure of gradual method annotations and bodies preserves the class names and
ordered parents. `WellFormedGClassTableCore` supplies a validated hierarchy for
this erased table. Gradual bounds comparisons therefore use the static subtype
equations without requiring static typing of the gradual method bodies.

=== Bounds for unknown information

To *materialize* an annotation is to replace each occurrence of `any` with a
static type, independently of the other occurrences. The checker approximates
these replacements with a lower bound L(G) and an upper bound U(G) in the static
subtype order. Class types, class exclusions, and bottom remain unchanged.
Union and intersection apply the bounds to their components. The other cases are:

```text
L(any) = bottom                    U(any) = Object
L(P → R) = U(P) → L(R)            U(P → R) = L(P) → U(R)
```

Function inputs exchange lower and upper bounds because input subtyping is
contravariant. For example, `any → Bool` has lower bound `Object → Bool`
and upper bound `bottom → Bool`. For valid annotations, `lowerBound_le_upperBound`
proves L(G) <: U(G). The relation `MaterializesTo G T` is defined by interval membership:

```text
L(G) <: T <: U(G)
```

This interval can include types that independent replacements do not produce.
For example, `Bool → Object` lies between the bounds of `any → Bool`, although
replacing its unknown input always retains a Bool result. The bounds thus support
type comparisons, while result selection also retains the source annotations.

=== Function calls with unknown annotations

Static function typing requires calls to accept the required inputs without failure
and give every returned result the required type. Gradual annotations retain those
requirements while permitting `any`. The compiler inserts runtime checks: a function
check verifies bound-method shape, while checks at the call enforce input and result
requirements. A failed check can report blame. An intersection places several
requirements on the same function.

For a callee annotation G and argument annotation A on a fixed valid hierarchy,
`callSourceTy?_accepts_iff` characterizes source call acceptance exactly:

```text
callSourceTy?(G, A) is defined  iff  L(G) <: (L(A) → Object)
```

Object leaves the result unrestricted during acceptance. Calling a
`Bool → Bool` function with `any` passes because L(any) is bottom; runtime
checking then decides whether the actual argument is Bool. The comparison uses
the full callee type. Thus, `Bool | (Bool → Bool)` called on Bool is rejected:
the callee could be a noncallable Bool value.

Source typing permits calls that need runtime checks, so acceptance does not
mean every materialization works. The compiler checks the actual function,
argument, and result and reports blame if a check fails. The inferred result
still needs to retain useful information, because it determines which later
calls pass source typing. Consider:

```text
f: (Object -> Bool | NoneType) & (Bool -> NoneType)
x: any
consume: NoneType -> Bool
```

Materializing x as Bool or NoneType gives different results:

#table(
  columns: (1fr, 2fr, 1fr),
  inset: 6pt,
  stroke: luma(80%),
  [Argument materialization], [Requirements that apply], [Type of `f(x)`],
  [`Bool`], [Both.], [`NoneType`],
  [`NoneType`], [The Object requirement.], [`Bool | NoneType`],
)

With x typed as `any`, both argument materializations are possible, so the
checker retains both results. The Bool materialization gives the NoneType
required by `consume(f(x))`, letting that expression pass source typing.
If f actually returns Bool, consume's runtime input check rejects it.

=== Representing alternative result types

Different argument materializations can select different result types.
Suppose two cases select static results X and Y. An exact representation of
these choices need not be a single subtype interval. Every interval containing
both X and Y also contains their intersection and union, and all types between
those endpoints. The greatest common lower bound is `X & Y`; the least common
upper bound is `X | Y`. The checker represents these bounds with:

```text
(X & Y) | (any & (X | Y))
```

Its lower bound is `X & Y` and its upper bound is `X | Y`, so it gives the
tightest interval containing both case results. It can still admit extra types:
an interval containing Bool and Object also contains `Bool | NoneType`.
This loss of precision is the cost of the bounds approximation. When all cases
select the same result, the checker retains that annotation without adding `any`.

=== Selecting the result of a call

After acceptance, the checker selects a result from the callee's function
requirements. A declared `P → R` supplies its input and result pair, while an
unknown callee part supplies `any → any`. Class membership and exclusion can
rule out callable values according to BoundMethod's MRO; they supply no input
or result annotations. The earlier acceptance test accounts for noncallable values.

For an intersection, the candidate requirements include its individual function
requirements and their combinations. Requirements that cover different inputs
can combine their inputs and results by union. Requirements whose input has
empty overlap with U(A) contribute no reachable case. For a union of callees,
each candidate combines requirements from both alternatives: inputs intersect,
while results union. The input must work for either callee, and either result
can occur.

Each candidate `P → R` defines a case when L(A) <: U(P). For that case, let
T = U(A) & U(P). The checker retains R and the result S of every other candidate
`Q → S` for which T <: L(Q). Those requirements apply to the same case input,
so their results are intersected. The results from distinct cases are then
combined with the interval construction above. In the preceding example,
the Bool case gives NoneType and the Object case gives `Bool | NoneType`.
Their combined bounds permit the later NoneType input check.

Equal result annotations remain unchanged. Bounds comparisons can also remove
redundant results, but only when the annotations contain no unknown function
inputs. The restriction matters for calls on returned functions. Consider:

```text
f: (Bool → (any → Bool)) & (NoneType → (Bool → Object))
x: any
```

A Bool argument selects `any → Bool`; a NoneType argument selects
`Bool → Object`. Bounds alone would treat the first interval as covering the
second and discard the Object-result alternative. Yet replacing the unknown
input in `any → Bool` always retains Bool as its result. The selector therefore
keeps both distinct function annotations before combining their uncertainty.
The combined interval can still lose information; exact result selection for
all independent replacements is not proved.

An annotation that excludes callable values contributes no successful call result.
A bottom callee gives bottom because no value can reach the call.
If acceptance succeeds but no result is selected, the fallback is bottom when
U(A) is empty and `any` otherwise. This distinguishes unreachable calls from
calls whose result is unknown.

=== Declared results and unknown function constraints

A single `P -> R` keeps its declared result R on an accepted call. Thus,
`Bool -> Bool` with an `any` argument gives Bool, as does `any -> Bool` with
True: uncertainty about an input alone does not change the declared result.
The result associated with each materialization is the one selected by this
call rule. Static expression typing can assign additional types to
unreachable calls, such as those with a bottom argument.

An unknown part of the whole function can restrict the result as well. In
`any & (Dog -> Dog)`, it can materialize to `Dog -> (Dog & Cat)`, so the
result must allow a more specific type than Dog. The checker gives bounds
from bottom to Dog, letting a later Cat parameter check pass source typing;
the runtime check fails if the actual Dog is not a Cat. These rules balance
retained information with runtime checks, but the development does not prove
that changing annotations to `any` preserves acceptance of a whole program.

=== Attribute lookup and class tests

Attribute lookup on `any` returns `any` and requires a runtime lookup check.
For `A | B`, source lookup must succeed on both alternatives, because the
receiver can have either type. The result is the union of their method types.
For `A & B`, one successful lookup suffices because both receiver requirements
hold. If both succeed, the result intersects their method types.

The test `isInstance(x, C)` adds class information to the type of `x` in each branch.
The checker keeps known class requirements before adding the test result.
`any` and `A | any` use `class C` in the positive branch and `negClass(C)` in the negative branch.
`A & any` uses `A & class C` and `A & negClass(C)`.
This rule does not inspect input and result annotations inside a function type.

== Compiled expressions <checked-targets>

Source annotations and runtime check types have different roles. Source types
can intersect several function requirements. Runtime checks use the restricted
fragment `CheckedTargetTy`, which lets preservation use the evidence produced
by enforcement. Let F be a class formula and T a permitted target:

```text
F ::= any | class C | negClass(C) | bottom
    | union(F, F) | intersection(F, F)
T ::= F | (T → T) | union(T, T)
    | intersection(T → T, F) | intersection(F, T → T)
```

Here, `union` and `intersection` denote the type operations `|` and `&`.
In the final two forms, F must hold for every computed BoundMethod MRO.
Class membership checks inclusion, exclusion checks absence, union permits
either formula, and intersection requires both. This side condition makes F
compatible with every callable value. Target class names must also be declared.
A direct intersection of two function signatures is excluded, while function
types can occur recursively in another function's input or result.

`CheckedTarget` stores a type that runtime checks can use.
`interpTarget` gives its gradual type meaning.
`compileBoundaryTarget` converts it to `BoundaryContract`, the structure used by the runtime type check.
`checkedTargetOfGTy` gives the checked syntax for an expected gradual type.

The compiler emits these expression forms:

#table(
  columns: (1.4fr, 2fr),
  inset: 5pt,
  [*Form*], [*Meaning*],
  [`enforce e target obligation`],
  [Evaluate `e`. Check its value against `target`. Report `obligation` if the check fails.],
  [`dynAttrAccess e attrName obligation`],
  [Evaluate `e`. Look up `attrName`. Report `obligation` if the attribute is absent.],
  [`call callee arg paramTy returnTy returnObligation`],
  [Call `callee` with `arg`. Store the caller's input and result targets. Report `returnObligation` if the returned value fails the caller's result check.],
)

An *obligation* is a source location and the requirement checked there.
`SourceExpressionSite` identifies an expression by a path from its root.
`SourceSite` also identifies method parameter and method result checks.
`SourceObligation.hasType site G` requires the value at `site` to satisfy type G.
`SourceObligation.hasAttribute site attr` requires lookup at `site` to find `attr`.

`compileCheck` takes a source typing proof, a source expression location, and an expected type P.
It returns the compiled expression.
The surrounding expression can require a different P at each use.

#theorem(
  "Theorem",
  "Compiler Typing",
  [`compileCheck_checked` proves that the compiled expression has its expected type P.
   It requires a valid source typing proof and matching source and checked environments.
   It also requires a source location and proofs that P is a permitted target with valid class names.],
  proof: [The proof follows the source typing proof.
    Each case compiles the smaller expressions and applies the corresponding checked typing rule.],
)

== Runtime type checks and calls

`CheckedValue.objRef oid` refers to the heap object with identifier `oid`.
The heap stores ordinary objects and bound-method objects.
A bound-method object contains a receiver reference and a checked method.
Only bound methods can be called.
Successful method attribute lookup allocates a bound-method object and returns its reference.

`EnforceValue` checks a value against a `BoundaryContract`.
The check reads the heap without allocating objects or changing it.
A successful check returns the same object reference.
A function check only verifies that the reference points to a bound-method object.
It does not execute the body or test possible inputs.

For a source call with expected result type P, the compiler performs these steps:

+ Compute `D := callParamTarget argSrcTy` from the argument's source type.
+ Compile the function expression with expected type `D → P`.
+ Compile the argument with expected type D.
+ Emit a checked call with the input target, result target, and source result obligation.

`callParamTarget` retains the argument annotation's class information and
replaces each function part with `any`, then simplifies unions and intersections.
This produces a permitted class-formula target. The compiled argument
establishes this caller requirement before the machine applies the method's
stored parameter check. Function input and result requirements are enforced
when those functions are called.

After the function expression gives a bound method, the machine performs these steps:

+ Evaluate the argument.
+ Check its value against the method's stored parameter target.
  Report the method parameter obligation if the check fails.
+ Run the compiled body with variable bindings `[param, receiver]`.
  The body was compiled with expected type `any`.
+ Check the body's result against the method's stored result target.
  Report the method result obligation if the check fails.
+ Check the result against the caller's expected result target.
  Report the call result obligation if the check fails.
+ Restore the caller's environment.

The method's declared result type and the caller's expected result type can differ.
The machine checks both.

== Machine and value invariants

An *invariant* is a property that each execution step preserves.
`CheckedStateSafe` requires these properties:

- The heap objects have valid classes and payloads.
- The gradual class table satisfies its typing and inheritance rules.
- The checked class table matches its source table.
- The variable values satisfy their assigned types.
- The current expression or result has the required type.
- The continuation accepts that type and gives the required final type.

The continuation is a stack of pending operations.
Each frame stores the information needed to complete one operation.
For example, `awaitArgument` waits for a call argument.
It retains the call's result target and failure obligation.

`CheckedValueWitness` stores a type validity proof and the data that explains why a value satisfies that type.
For `any`, it records a reference to a valid heap object.
For `class_ C`, it records that the object's runtime MRO contains C.
For a function type, it records a bound method from its receiver's MRO.
Input and result checks occur when the machine performs the call.
Union records at least one member type; intersection records both.

The compiler and its helpers compute without classical choice.
`computeGMro?` searches for the MRO with a finite fuel limit.
Its result agrees with the relation `GComputeMro`.
`lookupMethodTy?` searches this MRO for the method's input and result types.
Call acceptance supplies the type validity needed to build runtime checks.

== Gradual type safety

`ElaboratesProgramAt` connects a source program to its compiled program at expected result type P.
It records the class-table correspondence and the source typing proof.
It also records that the compiled main expression equals `compileCheck` at the main source location.
P must be a permitted runtime check type with valid class names.

#theorem(
  "Theorem",
  "Initial State",
  [`compiled_initial_safe_at` proves that the compiled initial state satisfies `CheckedStateSafe`.
   `compiled_initial_safe_from_elaboration_at` obtains the required data from `ElaboratesProgramAt`.],
  proof: [`compileCheck_checked` supplies the expression type.
    The initial heap satisfies its storage rules.
    The translation record supplies class-table correspondence and valid target types.],
)

#theorem(
  "Theorem",
  "Gradual Type Safety",
  [`gradual_soundness_at` takes an `ElaboratesProgramAt` record and an execution that reaches a final state.
   It proves that the final result is a value that satisfies P or blame.
   It excludes `runtimeError` for that execution.],
  proof: [The initial state satisfies `CheckedStateSafe`.
    Preservation proves that each step keeps this invariant.
    Progress proves that a valid unfinished state can take a step.
    The final state can contain only a successful value or a blame report.],
)

`Checked.blame_adequacy` proves that a final blame report describes a violated requirement in the final heap.
A failed type check violates the reported type requirement.
A missing attribute violates the requirement to find that attribute.

`embedded_static_no_blame` requires an `EmbeddedStaticElaboration` record for a static program.
It proves that the compiled execution cannot finish with blame.
`embedded_static_success` proves that any final result is a successful value.
The record requires permitted runtime targets for translated method input and
result annotations, as defined in @checked-targets. Thus, a method annotation
that directly intersects two function signatures is outside its scope.
It also supplies translation proofs for the main expression and each method body.
For example, a class C with method `m(self, x: Bool) → Bool = x` has the required
evidence. Its compiled main expression `(new C).m(TRUE)` terminates with TRUE.
The development does not construct this evidence for every statically typed program.

== Comparing runtime check types

`CheckedTargetPrecision` compares targets by their syntax. `CompileTargetPrecision`
also permits changes made by compiler simplification. The no-blame proof uses these
relations to widen runtime satisfaction facts. They do not state a theorem comparing
whole program executions with different annotations.

= Limits of the development

The type language permits class exclusion with `negClass C`.
It does not contain general negation of function types, unions, or intersections.

The future-hierarchy construction supplies class ancestry and MROs. Call safety
comes from the program's typed method declarations. There is no separate theorem
relating all the function equations to arbitrary method executions.

Exhaustive enumeration makes the correctness proofs simple, but evaluation can
exhaust time or memory. Repeated calls on returned functions can make this
especially costly: each call enumerates subsets and collections of the
function requirements in the preceding result.

A function check verifies the bound-method storage shape. The machine checks input
and result types at calls. Gradual call acceptance compares the full callee
annotation's materialization lower bound with a function type. This uses the subtype comparison
proved equivalent to the type equations. Result selection uses the function
requirements extracted from its source type. It does not use every consequence of the
full type to narrow the result.

`callSourceTy?_moreStatic` preserves acceptance of one call when each new bounds interval includes the old interval.
It does not compare the selected results or later parameter checks.
There is no theorem that changing annotations to `any` preserves acceptance of a whole program.

The soundness theorems apply to correctly typed compiled programs.
The checked machine also contains `runtimeError` rules for other inputs.
The theorems do not cover malformed inputs that bypass compilation.

The language has no parametric polymorphism, recursive types, or mutable fields.
It has no concurrency or exceptions other than blame.

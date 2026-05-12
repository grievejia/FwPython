# FwPython Type System

## Overview

FwPython uses a declarative static type system. The runtime has one value shape,
object references, so nominal class views, callable views, and branch-sensitive
negative facts all describe the same heap objects.

The static development is built around four ideas:

- nominal class membership is determined by MRO membership
- `callable P R` is behavioral, not a nominal callable class
- unions and intersections are primitive type constructors
- negative information is class-only: `negClass C` means the runtime class has
  a deterministic MRO that excludes `C`

`negClass C` is not a generic complement operator. It records a positive
exclusion witness about one class name.

## Core Judgments

The main judgments are:

- `HasType ct Γ e T`
  expression typing
- `ValueHasType ct h v T`
  runtime value typing
- `FindMethodType ct cname methodName paramTy returnTy`
  method-signature lookup through the receiver MRO
- `IsSubtype ct T U`
  declarative subtyping

The metatheory assumes:

- `WellFormedClassTable ct`
- `HeapWellFormed ct h`

These are semantic invariants, not checker artifacts. They provide the MRO and
heap facts used by the typing and soundness proofs.

## Type Language

FwPython uses a single static type language `Ty` for method annotations,
expression typing, subtyping, and denotational semantics. `HasType` is the
only public static typing judgment. Internal proof modules may package
additional lookup or dispatch choices for algorithmic completeness or the
static-to-gradual bridge, but those witnesses are not part of the public
static interface and do not introduce a second annotation language.

| Form | Meaning |
| --- | --- |
| `class_ C` | runtime class lies under `C` in the MRO |
| `negClass C` | runtime-class MRO excludes `C` |
| `callable P R` | invokable value accepting at least `P` and returning at most `R` |
| `T \| U` | union |
| `T & U` | intersection |
| `bottom` | empty type |

The universal supertype is `class_ Object`.

### Why There Is Only One Static Type Language

FwPython keeps a single `Ty` because the same facts need to be visible in four
places at once: source-level annotations, internal typing derivations, semantic
subtyping, and the static-to-gradual bridge. A separate surface annotation
language would force every proof that crosses one of those boundaries to carry
an embedding lemma before it could even state the relevant property. Using one
language keeps the public meaning of an annotation identical to the internal
meaning used by runtime typing and denotational semantics.

## Subtyping

`IsSubtype` is organized into five groups.

### Preorder

- reflexivity
- transitivity

### Bounded Distributive Lattice

- `bottom <: T`
- `T <: class_ Object`
- intersection projection and introduction
- union elimination and injection
- forward distributivity of intersection over union

### Nominal Classes

- `class_ C <: class_ A` when `A` is in the computed MRO of `C`

### Callables

- `callable P R <: callable P' R'` when `P' <: P` and `R <: R'`
- `callable P R <: class_ BoundMethod`
- `(P → R) & (Q → S) <: (P | Q) → (R & S)`

### Class-Only Negative Facts

Negative reasoning is primitive and class-only.

Primitive rules:

- `sealedClassNegClass`
  if `B` is a designated sealed built-in, `findClass B = b`, `ComputeMro b M`,
  and `D ∉ M`, then `class_ B <: negClass D`
- `objectClassUnionNegClass`
  `class Object <: class C | negClass C`
- `classSelfNegClassBottom`
  `class_ C & negClass C <: bottom`

The `LeafBuiltin` premise is restricted to `Bool`, `NoneType`, and
`BoundMethod`. This is the open-world boundary: arbitrary user-defined classes
do not get global non-overlap facts just because the current class table
happens not to show an overlap. Only the designated leaf built-ins admit
primitive global exclusion facts.

The helper API in `FwPython/Static/Subtyping/Negation.lean` packages the
usable consequences of this basis:

- `callableBoundMethod` — the callable-to-`class_ BoundMethod` bridge
- `leafBuiltinNegClass` — class-only exclusion for sealed built-ins
- `classNegClassBottom` — contradiction from positive class subtyping
- `negClassAntitone` — antitonicity of `negClass`
- `negClass_class_contradiction`, `class_self_negClass_contradiction`,
  `callable_negClass_boundMethod_contradiction`, `leaf_class_callable_bottom`

There is no generic negation constructor, no generic negation-introduction
rule, no pseudocomplement law, and no generic De Morgan library.

### Why Negation Stops Here

The negative fragment is intentionally narrower than generic semantic
complement. The runtime can witness that a concrete object's MRO excludes a
particular class name, and the subtyping rules can lift a small number of such
facts in an open-world-safe way. What the system cannot justify is arbitrary
set-theoretic complement, blanket non-overlap facts for user-defined classes,
or a proof-relevant distinction between "non-callable" and "not this
particular class". Restricting negation to `negClass C` keeps branch
narrowing, runtime typing, and semantic subtyping aligned around the same piece
of evidence.

Callable reasoning is routed through `BoundMethod` for the same reason. The
runtime callable carrier is a bound-method object in the heap, so the static
system treats `class_ BoundMethod` as the nominal bridge for callable values.
That yields exactly the negative consequences the proofs need, such as the
contradiction between callability and `negClass BoundMethod`, without
introducing a separate coarse callable / non-callable summary vocabulary.

The routing through `BoundMethod` is also a deliberate modeling choice about
what FwPython captures from Python. Real Python has many callable kinds —
plain functions, lambdas, bound methods, classmethods, staticmethods,
built-in functions, instances with `__call__`, and class types themselves —
and a faithful static type system would need a richer callable vocabulary to
distinguish them. FwPython collapses all of these into a single runtime
carrier and treats `class_ BoundMethod` as both the nominal bridge for
callability and the only callable shape in the heap. That collapse is what
lets the static type language stop at one form of callable type
(`callable P R`) and one nominal class for callable membership, and what
lets the negation fragment dispatch "callable vs. not callable" through
`negClass BoundMethod` instead of through a parallel callable-summary
vocabulary. The cost is that FwPython cannot capture patterns that depend
on Python's plurality of callable kinds, such as `__call__` on user-defined
classes or first-class functions distinct from methods.

## Static Typing

The core typing judgment is `HasType ct Γ e T`.

Relevant rules:

- object creation yields `class_ C`
- attribute access has two primitive forms: a class receiver `class_ C` yields
  the looked-up `callable P R`, and a binary union of class receivers
  `class_ C1 | class_ C2` yields the union of the two looked-up callables
- calls require the callee at type `callable P R` and the argument at a subtype
  of `P`, yielding `R`
- ordinary conditionals require a boolean condition and return the union of the
  branch result types
- intersection introduction is general at the term level

FwPython also has a specialized narrowing rule for `if isInstance(x, C)`. Like
an ordinary conditional, it returns the union of the two branch result types,
but it refines the tested variable asymmetrically on the way to those results.

- then branch: `Γ[x ↦ T & class_ C]`
- else branch: `Γ[x ↦ T & negClass C]`

A failed `isInstance` test records one nominal exclusion fact.

### Algorithmic Typing Checker

The executable checker is phrased directly for `HasType ct Γ e T`. The
synthesis procedure `inferBasis` computes a finite basis of candidate result
types for an expression, and `checkHasType?` accepts exactly when some
inferred basis member is a declarative subtype of the requested target.

Attribute checking is finite because receiver views are enumerated from the
current class table. Call checking uses a more general summary layer:
`callableSummaryBasis` does not try to enumerate only source-level callable
origins, but computes finite callable summaries that also cover collapsed
callable facts obtained through subtyping, including union summaries,
intersection-to-callable collapse, and the `.bottom` branch.

The public checker is `checkHasType?`, with the equivalence theorem
`checkHasType?_iff_hasType` under the usual well-formedness premises on the
class table and environment. In other words, the executable layer is an
algorithmic presentation of the same static typing judgment, and ordinary
static typing inherits decidability directly from that checker.

## Runtime Typing

`ValueHasType` types runtime object references in four ways:

- `objRef`
  class typing from the concrete heap object and class subtyping
- `objRefCallable`
  callable typing from bound-method payload
- `objRefNegClass`
  class-only negative typing from:
  - heap lookup of the object
  - existence of the target class and its MRO
  - existence of the object runtime class and its MRO
  - a proof that the target class name is not in that runtime MRO
- `sub` and `interIntro`
  subsumption and runtime intersection introduction

The key runtime negative fact is therefore witness-carrying from the start. It
does not route through a generic complement semantics.

## Semantic Foundation

Subtyping soundness is proved over a single semantic carrier `SemObject ct`
that distinguishes the three runtime shapes the proofs actually need:

- `ordinaryCurrent` — an existing well-formed class instance
- `ordinaryFresh` — a hypothetical instance of a fresh non-leaf class compatible
  with a list of MRO seeds (the open-world witness)
- `boundMethod` — a bound-method object with stored parameter and return types

Denotation `Ty.semDenotes ct T obj` is direct and pointwise in a single class
table. The clauses are:

- `class_ C` — `obj.hasAncestor C`
- `negClass C` — `¬ obj.hasAncestor C`
- `callable P R` — `obj` is a `boundMethod` whose stored signature is wider in
  the parameter and narrower in the return; the callable case stays
  intensional because a fully extensional clause would not pass the
  termination checker
- `union`, `intersection`, `bottom` — the obvious propositional connectives

Semantic subtyping is then plain denotation preservation:

```lean
SemSubtype ct T U := ∀ obj, Ty.semDenotes ct T obj → Ty.semDenotes ct U obj
```

Open-world reasoning is recovered without an `Extends` quantifier: the
`ordinaryFresh` carrier supplies the hypothetical-class witnesses needed for
e.g. `negClass`-style reasoning, and `WellFormedTy` is a pointwise
current-table notion throughout.

### Why The Semantics Uses `ordinaryFresh`

Completeness needs open-world counterexamples: to refute an invalid subtype, it
must sometimes imagine a fresh non-leaf class that extends the current table in
a way compatible with the visible MRO seeds. FwPython packages those witnesses
inside `SemObject` rather than quantifying over separate extended class tables.
This keeps `SemSubtype` pointwise in one class table, keeps `WellFormedTy`
local to that table, and lets the decision procedure work constructively over a
single semantic carrier instead of alternating between syntax and an external
extension relation.

## Proof Architecture

The proof stack is:

1. prove `IsSubtype` sound with respect to `SemSubtype` (`semSubtype_sound`)
2. prove the open-world completeness direction
   `SemSubtype ct T U → IsSubtype ct T U` for well-formed inputs
   (`semSubtype_complete`), giving the headline equivalence
   `isSubtype_iff_semSubtype`
3. derive the inversion lemmas needed by the runtime proofs
4. prove preservation for the continuation machine
5. combine preservation with progress to obtain soundness

For executable use, the equivalence carries through to a constructive
decision procedure: under `WellFormedClassTable ct` and `WellFormedTy`
hypotheses on the two sides,

- `isSubtype_decidable hwfct hwfT hwfU : Decidable (IsSubtype ct T U)`
- `semSubtype_decidable hwfct hwfT hwfU : Decidable (SemSubtype ct T U)`

are produced by a single `WellFounded.fix` over a `DecisionGoal` sum that
unifies the subtype recursion with the bound-method denotation recursion.
Yes-answers return syntactic `IsSubtype` proofs; no-answers return a
`SemObject` counterexample together with denotation/non-denotation evidence.
No classical reasoning is used.

This proof order is deliberate. The runtime proofs need inversion lemmas about
what a typed object reference can or cannot be, and those inversion lemmas are
cleanest when they are recovered from a prior semantic account of subtyping
rather than baked into the syntax-directed typing rules themselves. Keeping
`IsSubtype` declarative also prevents the theorem surface from depending on an
algorithm's search order or normalization strategy.

The main `isInstance` preservation case is direct:

- the then branch narrows with `class_ C`
- the else branch narrows with `negClass C`
- the runtime witness is constructed with `ValueHasType.objRefNegClass`

## Design Boundary

The static language deliberately stops at a small negative fragment.

- negative facts are only `negClass C`
- callable negative reasoning is mediated through `BoundMethod`
- leaf-built-in sealing is the only source of open-world-safe primitive class
  exclusion
- there is no coarse callable-summary / non-callable-summary vocabulary

That boundary matches the runtime evidence the proofs can actually justify.

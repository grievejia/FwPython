# Gradual Typing in FwPython

Checked runtime values are only object references. Callable enforcement
is shallow. Higher-order mediation happens through compiled call
structure plus method-entry and method-exit enforcement.

## Overview

The gradual development is organized as a translation-and-proof pipeline:

```text
gradual source program
  -- semantic/source reasoning via MoreStatic, BoundaryPrecision,
     ProgramAnnotationPrecision, and SemanticSourceEnvPrecision
  -- same-skeleton program transport via ProgramTargetPrecision
  -- use-site elaboration via compileCheck
explicit checked-target program
  -- normalized CheckedTarget annotations
  -- explicit enforce / dynAttrAccess / call-return labels
checked continuation machine
  -- checked/runtime precision on expressions, frames, states, and outcomes
  -- DGG-only elaboration/provenance wrapper ElaboratedStatePrecision
derived end-to-end theorems
  -- soundness
  -- blame correctness + unique blame origins
  -- one static gradual guarantee
  -- one dynamic gradual guarantee
```

For well-typed elaborated programs, the checked machine can finish in
only two intended ways:

- success with a value witnessing the expected gradual type
- blame at one of the boundaries inserted by compilation

The checked machine has a `runtimeError` constructor for engineering
convenience; the soundness theorem rules it out for compiled well-typed
executions.

## Why a Checked Target Exists

A direct metatheory on the surface gradual language would have to mix source
typing, implicit dynamic checks, blame assignment, runtime mediation, and
environment refinement in one operational model. The checked target separates
those concerns. Source typing determines where dynamic obligations arise,
`compileCheck` inserts them explicitly, and the safety proof is then carried
out on a smaller machine whose control states say exactly which boundary is
being checked and which labels own the potential blame. This is why the gradual
development is presented as elaboration plus checked-runtime soundness rather
than as a single ad hoc source-language evaluator.

## Source Layer

The source language is what the programmer writes. Its type language
`GTy` contains:

- class types
- callable types
- `any`
- unions and intersections
- class-only negation (`negClass C`)
- `bottom`

Source typing is expressed by `GSrcInfer`. It is:

- deterministic
- single-type per binding
- source-level, not machine-level

Checked approximations are not stored in source environments. They are
chosen later at elaboration sites.

The source-facing theorem layer is deliberately semantic.

- `MoreStatic` is the basic source-annotation relation.
- `BoundaryPrecision` is the semantic relation on compiled boundary meanings.
- `ProgramAnnotationPrecision` is the same-skeleton source-program relation
  whose fields vary only by `MoreStatic`.
- `SemanticSourceEnvPrecision` is the same-binding-name environment relation
  with pointwise `MoreStatic`.

The public static/DGG entry points also use two narrower structural relations.

- `ProgramTargetPrecision` is the same-skeleton program relation stated through
  explicit checked-target images of method annotations.
- `ProgramRootTargetInputPrecision` is the surviving root-only structural
  premise for the top-level expected target. It is intentionally separate from
  program precision.

Operational source reasoning still uses:

- `GradualSubtype` for one-way widening
- `AssignableTo` for assignment-like compatibility, especially calls and
  conditionals

The single-type front end is intentionally safe-domain-directed:

- attribute access uses the partial source summary `attrSourceTy?`
- call typing uses `calleeSummarySrc` and `callSourceTy?`
- conditionals require a boolean-safe domain
- `any` can supply dynamic behavior where the front end allows it, but
  it does not magically rescue a failing union arm

The source summaries are intentionally asymmetric across unions and
intersections.

- attribute lookup on a union succeeds if either branch finds the attribute and
  returns the union of the successful results
- attribute lookup on an intersection keeps a surviving branch if exactly one
  side finds the attribute and returns an intersection only when both sides
  succeed
- call typing on a union succeeds only when both branches accept the argument
- call typing on an intersection keeps the unique successful branch and
  collapses two simultaneous successes to `.any`

The front end is deliberately separate from checked elaboration:

- source environments track only source types
- checked environments appear only after elaboration
- checked targets are introduced only through `approxTarget`,
  `callParamTarget`, and `compileCheck`

Call-site parameter targets are also normalized before they reach the checked
layer. `callParamTarget` and `callParamCheckedTarget` absorb `.any`,
propagate `.bottom`, remove duplicates, and canonicalize the order of
non-collapsed intersections so the compile/runtime proofs compare a stable
checked-target image.

### Why The Source Layer Stays Single-Type

`GSrcInfer` assigns one source type per expression because the source layer is
supposed to explain what the programmer wrote, not to precompute every checked
approximation the runtime might later need. If checked approximations were
threaded through source environments, every source theorem would have to talk
about machine-facing artifacts such as call-site targets and boundary
approximations. By choosing those only at elaboration sites, FwPython keeps the
source typing judgment deterministic and compact while still allowing the
checked compiler to insert the exact boundaries required at each use.

### Why Negation Stays Class-Only

The source language inherits class-only negation (`negClass C`) from the
static side rather than introducing a general `negation T`. The
justification is open-world soundness, and it carries over unchanged to
the gradual layer: only sealed built-in classes admit primitive global
exclusion, and `negClass C` records exactly the runtime fact the heap
can witness. The gradual layer adds no separate negation machinery; it
simply reuses what the static side already justified.

## Checked Target

The checked/runtime layer stores explicit checked-target syntax:

- `CheckedTarget`
- `interpTarget`
- `compileBoundaryTarget`
- `coreNormalizeCheckedTarget`

`coreNormalizeCheckedTarget` is the only load-bearing normalizer for
machine-facing target syntax. `RuntimePublicCheckedTargetShape` means that a
checked target is already a fixpoint of that normalizer. There is no checked
target analogue of `runtimePublicTy`; the old raw helper survives only as the
identity on `GTy` for compatibility outside the checked-target metatheory.

The checked target makes every dynamic obligation explicit in the syntax.
Its key forms are:

- `enforce e target labels`
- `dynAttrAccess e attrName ℓ`
- `call callee arg paramTy returnTy returnLabels`

`compileCheck` inserts these forms from a source typing derivation plus an
explicit expected target `P`. Checked syntax, checked frames, and checked
methods carry explicit `CheckedTarget` annotations, and boundary-label payloads
are indexed directly by `BoundaryLabels (compileBoundaryTarget target)`.

Three details matter for the current semantics.

### Calls carry explicit checked targets and return-boundary labels

The checked `call` node stores:

- the caller-side expected parameter target
- the caller-side expected return target
- the boundary-label tree for the call-site return check

This is how the runtime remembers where return-side blame should be
attributed after a method body finishes.

### Dynamic failure is turned into blame

Operations that are dynamically allowed because of `any` are compiled
into checked forms that blame instead of exposing unchecked failure.

In particular:

- dynamic attribute access becomes `dynAttrAccess`
- missing dynamic attributes blame the stored label
- source calls elaborate through explicit callable expectations

The checked machine contains raw runtime errors for untyped or
malformed executions; those are outside the intended semantics of
compiled well-typed programs.

### Checked precision is split

The runtime precision layer is constructor-directed on checked syntax and uses
semantic information only where the machine itself needs it. The main relations
are:

- `CheckedTargetPrecision`
- `CompileTargetPrecision`
- `CheckedProgramPrecision`
- `CheckedStatePrecision`
- `CheckedOutcomePrecision`

`CheckedTargetPrecision` is diagonal on runtime-public checked-target shape:
it matches constructors rather than building semantic widenings such as
"callable below any" into the machine relation. Semantic widening lives in
`MoreStatic` after interpreting the checked target.

`CompileTargetPrecision` is the slightly larger structural relation used for
compile-generated payloads such as normalized call-parameter targets. It keeps
the checked/runtime simulation syntactic while admitting the absorption facts
introduced by source-side call-parameter normalization.

### Why Dynamic Uncertainty Becomes Blame

FwPython treats uncertainty introduced by `any` as a boundary issue rather than
as an unchecked runtime hazard. That is why dynamic attribute access elaborates
to `dynAttrAccess`, why missing dynamic attributes blame an inserted label, and
why source calls elaborate through explicit callable expectations even when the
callee is only known through `any`. The alternative would be to let the runtime
fall through to raw machine errors for operations that the source language
admitted dynamically. That would make blame incomplete as an account of dynamic
failure and would break the end-to-end theorem that well-typed elaborated
programs finish in witnessed success or blame.

## Checked Runtime

The checked runtime is a small-step continuation machine over an
explicit heap.

### Values and heap objects

Checked runtime values are only:

- `CheckedValue.objRef oid`

Checked heap objects are:

- ordinary objects
- bound-method objects carrying a receiver OID and a checked method

Bound-method objects in the heap are the only callable carrier.

### Attribute access

Ordinary attribute lookup does not return a closure-like value. It
allocates a fresh bound-method heap object and returns its object
reference.

That representation is used uniformly by:

- ordinary attribute access
- dynamic attribute access
- callable witnesses
- the call rules

### Control and continuation

The machine state consists of:

- heap
- environment
- control
- continuation

The continuation frames record exactly what the runtime is waiting for.
The call-related frames carry explicit return targets and return labels:

- `callCallee`
- `callValue`
- `awaitArgument`

This is the operational backbone of the call-site mediation design.

## Enforcement Semantics

`EnforceValue` operates on `BoundaryContract`, not directly on `GTy`.
Contracts are produced from explicit checked targets by `compileBoundaryTarget`
and coincide with the old raw compiler on interpreted targets.

Three design facts are central.

### Enforcement is heap-read-only

Enforcement does not allocate and does not mutate the heap.

### Callable enforcement is shallow

Callable enforcement checks only whether the value is invokable in the
runtime sense:

- a bound-method object reference passes unchanged
- an ordinary object reference blames

### Successful enforcement is transparent

Successful enforcement returns the same object reference it was given.
That is true for:

- `unknown`
- class checks
- callable checks
- negated class checks
- unions and intersections built from those cases

This semantic transparency is what keeps the dynamic GG proof's runtime
simulation structurally compatible with the source and checked precision
relations.

### Why Callable Enforcement Is Shallow

FwPython does not enforce callable contracts by manufacturing wrapper values.
Instead, a callable check asks only whether the object reference is a bound
method, and the higher-order obligations are discharged by the checked call
syntax itself. This choice has two motivations.

- It keeps runtime value shape stable. Successful enforcement returns the same
  object reference, which is exactly what the dynamic gradual guarantee needs in
  order to simulate two precision-related runs without introducing shape
  mismatches after successful checks.
- It keeps caller-facing callable behavior unambiguous. A wrapper-based
  alternative would force the runtime and the proofs to reason about values that
  potentially present multiple callable interfaces through wrapper chains. By
  keeping callability tied to bound-method objects and pushing mediation into
  explicit call frames, the next machine step is determined by the current
  value shape alone.

## How Calls Are Mediated

Higher-order behavior is expressed by elaboration plus the checked call
rules.

For a source call, `compileCheck`:

1. computes a raw caller-side parameter approximation
   `D := callParamTarget gct argSrcTy`
2. compiles the callee against `.callable D P`
3. compiles the argument against `D`
4. emits a checked `call` node that carries the checked parameter target
   `callParamCheckedTarget gct argSrcTy` (the checked-target image of `D`),
   the checked return target `checkedTargetOfRuntimePublicTy P`, and the
   call-site return labels

Operationally, once evaluation reaches a bound-method callee, the
machine:

1. evaluates the argument
2. enforces the resulting value against the method's stored parameter
   contract and parameter labels
3. runs the method body in the runtime binding order
   `[param, receiver]`
4. enforces the body result against the method's stored return contract
5. enforces that result again against the caller's expected return type
   using the call-site return labels
6. restores the caller environment

The checked runtime performs two conceptually distinct checks:

- the callee's own contract
- the caller's use-site expectation

## Exact Safety Invariant

The central invariant is `CheckedStateSafe`.

A checked state is safe when it packages:

- a well-formed checked heap
- a well-formed gradual class table
- an aligned checked class table
- a typed environment
- a typed control component
- a typed continuation

The continuation typing is exact: it records the input type expected by
the top frame and the output type eventually produced after the rest of
the stack runs.

This exactness is deliberate. The checked metatheory avoids proof-only
widening in the machine invariants and keeps refinement explicit through
`enforce`.

## Witness-Based Value Reasoning

The value-level invariant used throughout preservation and progress is
`CheckedValueWitness`.

A witness packages:

- well-formedness of the indexed gradual type
- proof-relevant data explaining why the runtime value inhabits it

The payload is structural:

- `.any` stores `CheckedAnyShape`
- `.class_` stores `CheckedClassView`
- `.callable` stores `CheckedCallableView`
- unions and intersections store recursive witnesses
- `.negClass` stores runtime shape plus an enforcement property

The positive view forms are exact and shallow:

- `CheckedAnyShape` says the value is a reachable object reference
- `CheckedClassView` says the object's runtime MRO contains the class
- `CheckedCallableView` says the object reference is a reachable bound
  method in the receiver's MRO

Callable evidence is exactly the bound-method case.

## Class-Table Compilation and Elaboration Witnesses

The class-table bridge is explicit.

`IsCompiledMethodAt` records that a checked method:

- preserves names and annotations
- compiles parameter and return contracts from the gradual annotations
- uses canonical parameter and return label trees
- uses a body that is exactly `compileCheck` of a source typing witness

`IsCompiledClassTable` lifts that to class tables.

`ElaboratesProgramAt` is the one elaboration witness connecting a gradual
program to its checked elaboration at target `P`. It carries:

- compiled class-table correspondence
- a source typing witness for the main expression
- exact equality between the checked main term and `compileCheck`
- `RuntimePublicAnnotation gp.classes P`
- `WellFormedGTy gp.classes P`

The last two facts live inside the elaboration witness so the soundness and
dynamic-GG APIs receive them implicitly with the witness. The derived theorem
`ElaboratesProgramAt.main_elabCheck` exposes the main term through the
proof-level graph `ElabCheck`; the record's `compileCheck` equality is the
authoritative shape/label connection used by the provenance and precision
proofs. The public program comparison theorem layer uses one relation:
`CheckedProgramPrecision` is the checked/runtime comparison relation, and the
standard initialization package combines it with source-level main-type facts
and an `ElaboratedStatePrecision` witness for the initial states.
The root expectation itself remains a source-side `GTy`; when the checked
runtime needs structural target information, it uses the explicit image
`checkedTargetOfRuntimePublicTy P` and the root-only premise
`ProgramRootTargetInputPrecision`.

## Labels and Blame Provenance

Labels are not anonymous. A label records:

- a scope
- a site number
- an owner

Owners are determined by polarity:

- positive boundaries blame the provider
- negative boundaries blame the context

Compilation allocates labels at the exact syntactic sites where checked
boundaries are introduced. The current provenance layer tracks all of the
relevant origin categories:

- main-expression `enforce`
- main-expression `dynAttrAccess`
- main-expression call-return labels
- method-parameter boundary labels
- method-return boundary labels
- method-body `enforce`
- method-body `dynAttrAccess`
- method-body call-return labels

Source operators track canonical origin summaries through `SourceOriginTrace`,
canonical origin sets, and the corresponding callable/attribute summary keys.
These keys give duplicate-insensitive operator transport.

This is exposed to the runtime/provenance story through:

- `BoundaryOrigin` and `CompiledBoundaryOrigin` as the canonical compiled-origin
  handles
- direct `BoundaryLabels (compileBoundaryTarget T)` indexing
- centralized target/label/path casts in `BoundaryCast`
- same-elaboration label reconstruction from one compiled origin plus
  concrete boundary-path data
- cross-program blame origin equivalence rather than literal label equality

The provenance and runtime layers distinguish:

- `BoundaryOrigin`, the theorem-level provenance key identifying one compiled
  boundary
- `Label.site`, the scope-local label payload stored in the runtime

Two theorems establish existence and uniqueness of blame origins:

- `gradual_blame_correctness_at`
- `gradual_blame_provenance_origin_unique_at`

A final blame can be traced back to one unique compiled origin with the
expected owner.

### Why Labels Carry Scope, Site, and Owner

The label structure is designed for the blame theorems, not just for debugging.
A bare token would be enough to distinguish two failures operationally, but it
would not explain where the label was introduced or who should be blamed.
Recording the allocating scope, site number, and polarity-derived owner makes
blame provenance a theorem about the actual compiled program: the metatheory can
reconstruct the unique source of a final blame and prove that ownership matches
the intended positive/negative boundary discipline.

## Established Theorem Surface

The gradual development has the following public theorem story.

### Elaboration typing

`compileCheck_checked` is the primary compiler typing theorem: it proves that
`compileCheck` of a `GSrcInfer` witness is well typed in the checked system
under:

- an explicit checked environment `Δ`
- an explicit expected target `P`
- `RuntimePublicAnnotation gct P`
- `WellFormedGTy gct P`

`ElabCheck` is the proof-level graph of `compileCheck`. `compileCheck_elaborates`
produces an `ElabCheck` witness for the compiler output, and `elabCheck_checked`
delivers the checked typing fact from that witness. The theorem is
target-relative; those target facts are typically supplied by
`ElaboratesProgramAt`.

### Initial safety

`compiled_initial_safe_at` proves safety of the compiled initial state from:

- well-formed class-table facts
- alignment facts
- a source typing witness
- runtime-public admissibility and well-formedness of the target `P`

`compiled_initial_safe_from_elaboration_at` is the witness-based bridge
that derives the same initial safety fact directly from
`ElaboratesProgramAt`.

`initial_state_precision`, `initial_state_elaborated_precision`, and
`initial_elaborated_state_precision` are the public entry packages for the
precision side. They consume:

- `ProgramTargetPrecision`
- `ProgramRootTargetInputPrecision`
- elaboration witnesses on both sides

and produce checked-program precision together with the initial
`ElaboratedStatePrecision` package used by DGG.

### End-to-end soundness

`gradual_soundness_at` is the canonical target-relative soundness theorem.
Its inputs are an `ElaboratesProgramAt` witness — which already carries
`RuntimePublicAnnotation gp.classes P`, restricting the root expected type
`P` to the admissible runtime-public target fragment `CheckedTargetTy` —
together with an execution to a final state. The theorem says nothing about
runs that diverge; for runs that do reach a final state it concludes:

- success with a witness for `runtimePublicTy P` (equivalently the
  interpretation of the recorded root checked target), or
- blame

and excludes raw `runtimeError`.

### Static gradual guarantee

`static_gradual_guarantee` is the static GG theorem. It consumes:

- `ProgramTargetPrecision`
- `ProgramRootTargetInputPrecision`
- the two `ElaboratesProgramAt` witnesses

and returns `CheckedProgramPrecision`. The companion corollary
`static_gradual_guarantee_main_moreStatic` exposes the main-expression
`MoreStatic` fact packaged with that same checked-program relation.

### Dynamic gradual guarantee

The binary dynamic theorem is:

- `dynamic_gradual_guarantee_at`
- `dynamic_gradual_guarantee`

It takes two `ProgramTargetPrecision`-related elaborated programs together
with two `Steps` traces from their initial states that both reach a final
state, starts from the `InitialElaboratedStateAlignmentPackage`, and runs
the simulation over `ElaboratedStatePrecision`. The conclusion is the
asymmetric `CheckedOutcomePrecision` on the two final checked outcomes;
the case where one side terminates and the other diverges is outside the
theorem's scope.

The asymmetry of `CheckedOutcomePrecision` is the standard DGG content:

- success on both sides matches with heap and value precision
- blame on the more-static side is compatible with blame or success on
  the less-static side
- there is no constructor relating success on the more-static side with
  blame on the less-static side, so weakening an annotation toward `any`
  cannot turn a successful terminating run into one that blames

## Why the Proof Works

Three proof-architecture choices do most of the work.

### The runtime model and the proof shape match

The metatheory reasons about the same distinctions the machine actually
uses:

- ordinary object vs bound method
- class view vs callable view
- explicit enforcement frame vs explicit call-return boundary

That alignment is what keeps preservation, blame provenance, and the
dynamic simulation local.

### Value invariants are exact

The proof does not try to recover operational facts from broad value
typings after the fact. It carries exact witnesses and exact frame
typings from the start.

### Enforcement preserves runtime value shape

The dynamic-GG argument depends critically on the fact that successful
enforcement is transparent: it returns the same object reference it was
given, so runtime simulation is structurally compatible with the source
and checked precision relations.

## Constructive Elaboration

The elaboration pipeline is constructive end-to-end: every executable
helper computes on a well-formed gradual class table without classical
reasoning.

- `computeGMro?` is a fuel-bounded executable MRO search, sound and
  complete against the inductive `GComputeMro`. Its completeness uses
  `gComputeMro_determinism` to identify the unique returned MRO.
- `lookupMethodTy?` is built directly on `computeGMro?` and
  `findGMethodInMro`.
- `callSourceTy?` is the executable call-result computation on
  `CallableSummary`. At each leaf facet it uses well-formedness proofs to
  install `assignableTo_decidable`, and the companion relation
  `CallResultWitness` packages the proof-relevant explanation of the result.
- `GSrcInfer` is indexed by `WellFormedGClassTableCore`. Its `.call`
  constructor stores callable, well-formedness, and argument
  well-formedness proofs alongside the result equation, so every
  derivation tree carries the proofs needed to compute its own
  elaboration.
- `Decidable (FormulaGTy …)`, `Decidable (BMCompatibleFormula …)`,
  `Decidable (RuntimePublicAnnotation …)`, and
  `Decidable (CheckedBranchRefineOk …)` are global instances; the
  BM-compatible decider collapses the universal over MROs into a single
  `match` on `computeGMro? gct boundMethodClass`.

With those instances in scope, `compileCheck` is a plain `def` and every
`if CheckedBranchRefineOk … then …` / `by_cases` site computes through
typeclass inference.

This constructiveness matters because elaboration is part of the public story,
not just a proof artifact. `compileCheck` is supposed to be the compiler from
gradual source terms to checked terms. If its branching depended on classical
choice, the theorem surface could still state that elaboration exists, but the
development would lose the stronger claim that the elaborator actually computes
from a well-formed program and that precision theorems compare concrete
compiled outputs.

## File Guide

The main files for the gradual development are:

- `FwPython/Gradual/Language.lean`
  public surface for the gradual language
- `FwPython/Gradual/ClassTable.lean`
  gradual methods, classes, and programs with direct `GTy` annotations
- `FwPython/Gradual/Contracts.lean`
  umbrella for `BoundaryContract`, label structure, compilation, and
  runtime-public-type semantics
- `FwPython/Gradual/Checked/Core/{Syntax,Runtime,Machine}.lean`
  checked syntax, runtime relations, and operational semantics
- `FwPython/Gradual/TypeSystem/Source/{Core,Typing,Precision}.lean`
  source environments, `GSrcInfer`, and source precision
- `FwPython/Gradual/TypeSystem/Source/Elaboration.lean`
  the `ElabCheck` graph and its checked-typing corollary
- `FwPython/Gradual/TypeSystem/Source/Compile.lean`
  umbrella for `compileCheck`, the `ElabCheck` graph, approximation
  helpers, label erasure, and site-analysis lemmas
- `FwPython/Gradual/TypeSystem/ClassTable/Compile.lean`
  checked class-table compilation and `ElaboratesProgramAt`
- `FwPython/Gradual/TypeSystem/StaticEmbeddingBridge.lean`
  packages static `HasType` derivations with the gradual-source bridges used
  to reuse checked elaboration
- `FwPython/Gradual/TypeSystem/ValueTyping.lean`
  exact checked runtime witnesses and positive view forms
- `FwPython/Gradual/TypeSystem/{Safety,Progress,Preservation,Soundness}.lean`
  checked-machine safety and end-to-end soundness
- `FwPython/Gradual/TypeSystem/Blame/{Correctness,Provenance}.lean`
  blame-origin existence, owner correctness, and uniqueness
- `FwPython/Gradual/TypeSystem/{StaticGG,RuntimePrecision,DynamicGG}.lean`
  static and dynamic gradual guarantees
- `FwPython/Static/TypeSystem/{Typing,TypingLemmas}.lean`
  definition-only static `HasType` core plus its theorem layer, which the
  embedding bridge consumes from the static side

## Summary

FwPython's gradual layer is a checked-target development with:

- a semantic source layer (`MoreStatic`, boundary precision, source/program
  annotation precision)
- explicit normalized checked-target syntax
- split checked/runtime precision relations: `CheckedTargetPrecision` for
  stored checked annotations and `CompileTargetPrecision` for compile-generated
  payloads such as normalized call-parameter targets
- a DGG-only `ElaboratedStatePrecision` wrapper on top of checked-state
  precision
- explicit boundary insertion by elaboration
- a checked runtime with only object-reference values
- shallow callable enforcement
- exact witness-based safety invariants
- blame provenance with unique origins
- one static GG theorem and one dynamic GG theorem

Well-typed gradual programs elaborate to a checked machine that either
returns a properly witnessed value or blames at a uniquely identified
compiled boundary. Precision-related programs are compared semantically at the
source level, structurally through checked-target images at the program root
and method signatures, and dynamically through the elaborated-state simulation
wrapper used by the final dynamic gradual guarantee.

#set page(
  paper: "us-letter",
  margin: (x: 0.9in, y: 0.85in),
)

#set text(size: 10.5pt)
#set par(justify: true, leading: 0.68em)
#set heading(numbering: "1.")

#let formal(body) = text(size: 10pt, style: "italic")[#body]

#let rule(name, premises, conclusion) = [
  #align(center)[
    #stack(
      dir: ttb,
      spacing: 0.12em,
      formal(premises),
      grid(
        columns: (17em, auto),
        column-gutter: 0.85em,
        align: center,
        box(width: 17em)[#line(length: 100%)],
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
    A Lean 4 development of a small object-oriented language with multiple
    inheritance, class-only negative facts, and a checked-target gradual
    metatheory
  ]
]

= Overview

FwPython is a small object-oriented language formalized in Lean 4. The
development has two halves. The first is a static core: a typed language with
multiple inheritance, behavioral callable types, and a carefully limited form
of negative typing. The second is a gradual layer that adds a dynamic type
`any`, elaborates it into explicit runtime checks, and proves the resulting
machine is sound.

The two halves share one runtime model. Every value is an object reference.
Ordinary objects live in the heap, and method values are represented by a
distinguished kind of heap object whose class is `BoundMethod`. Both the static
metatheory and the gradual metatheory reason about the same shapes, the same
class table, and the same continuation machine.

On the static side, class types are nominal and follow the C3 method
resolution order (MRO). Callable types are behavioral: a value has type
`P → R` when it can be invoked with at least `P` and returns at most `R`.
Unions and intersections are primitive type constructors. Negative reasoning
is intentionally narrow: a failed `isInstance(x, C)` test records one specific
exclusion fact, written `negClass(C)`, rather than an arbitrary set-theoretic
complement.

On the gradual side, the source language extends the static type language with
`any`. Where the source program permits dynamic behavior, the elaborator
inserts explicit boundaries into a checked target language. The checked
runtime then turns dynamic mistakes into blame at a known boundary rather than
into raw machine failure. The metatheory proves end-to-end soundness, traces
each blame back to a unique compiled origin, and proves both the static and
the dynamic gradual guarantees.

The development is constructive throughout. Subtyping is decidable on
well-formed inputs. The MRO search is an executable function on the gradual
side, not an existence proof. Elaboration is a plain definition, so the
precision theorems compare concrete compiled programs rather than abstract
witnesses.

= Shared Runtime Model

A FwPython program runs against three things: a class table whose MRO is
computed by C3 linearization; a heap holding ordinary objects and bound-method
objects; and a continuation machine that drives evaluation step by step.

Bound methods are not a separate semantic universe. They are heap objects with
a distinguished payload, sharing storage with ordinary objects. As a
consequence, the same object reference can simultaneously support a class view
and a callable view. The static side exploits this by routing all callable
reasoning through the nominal class `BoundMethod`. The gradual side exploits
it by treating callable checks, attribute access, and call execution as
uniform operations on object references.

This bound-method carrier is a deliberate simplification of Python's actual
callable hierarchy. Real Python realizes callability through many distinct
mechanisms — plain functions, lambdas, bound methods, classmethod and
staticmethod descriptors, built-in functions, callable user-defined instances
(anything with `__call__`), and class types themselves. FwPython collapses
all of these into a single runtime carrier: every callable value is a
bound-method heap object, and method binding — a fresh bound-method
allocation at attribute access — is the only way to obtain one. The benefit
is that the metatheory has a single nominal anchor for callability,
`class BoundMethod`, and only one operational story for every callable
interaction. The cost is that FwPython cannot capture patterns that depend
on Python's plurality of callable kinds, such as `__call__` on user-defined
classes or first-class functions distinct from methods.

= Static Core

== Judgments and Type Language

The static metatheory is built around four judgments. Expression typing is
written `HasType ct Γ e T`, runtime value typing is written
`ValueHasType ct h v T`, method-signature lookup is written
`FindMethodType ct cname methodName paramTy returnTy`, and declarative
subtyping is written `IsSubtype ct T U`. Each one assumes the class table
`ct` is well-formed (`WellFormedClassTable ct`), and the runtime judgments
also assume the heap is well-formed (`HeapWellFormed ct h`). These
assumptions are semantic invariants rather than checker artifacts: they
package the MRO, lookup, and shape facts that the soundness proof needs.
In the implementation, the definition-only `HasType` core lives in
`FwPython/Static/TypeSystem/Typing.lean`, while theorem support lives in
`FwPython/Static/TypeSystem/TypingLemmas.lean`; the split keeps the static
judgment available below the heavier proof imports without recreating the
old import cycle.

A single static type language `Ty` is used throughout — for method
annotations, expression typing, runtime value typing, declarative subtyping,
and the denotational semantics. The forms are summarized below.

#table(
  columns: (1.7fr, 2.4fr),
  inset: 6pt,
  stroke: luma(80%),
  [Type form], [Meaning],

  [`class C`], [Objects whose runtime class lies under `C` in the MRO.],
  [`negClass(C)`], [Objects whose runtime-class MRO excludes `C`.],
  [`P → R`], [Objects that can be invoked with at least `P` and return at most `R`.],
  [`T | U`], [Union type.],
  [`T & U`], [Intersection type.],
  [`bottom`], [The empty type.],
)

The universal supertype is `class Object`. `HasType` is the only public
static typing judgment. The static-to-gradual bridge and the algorithmic
completeness proofs may package extra lookup or dispatch witnesses
internally, but they do so over the same `Ty` rather than introducing a
parallel annotation language. Keeping one type language means the meaning of
an annotation is the same wherever it appears: in the typing rules, in the
runtime invariants, and in the semantic interpretation.

== Declarative Subtyping

`IsSubtype` is declarative: it is a syntactic relation closed under a fixed
set of rules, with no commitment to a particular search order. This matters
because the public theorem surface, including the runtime inversion lemmas,
should not depend on how an algorithm chooses to discharge a subtyping
obligation.

The relation combines several familiar pieces. There is a preorder, with
reflexivity and transitivity. There is a bounded distributive lattice over
unions and intersections, with `bottom` on the left, `class Object` on the
right, the usual elimination and introduction rules, and forward
distributivity of intersection over union. On top of that lattice sit the
nominal, behavioral, and negative fragments described next.

The nominal class rule reads class subtyping off the MRO:

#rule(
  "S-Class",
  stack(
    dir: ttb,
    spacing: 0.12em,
    [MRO(C) = M],
    [A ∈ M],
  ),
  [class C <: class A],
)

Callable types are behavioral. A callable subtype must accept at least as
much input and produce at most as much output:

#rule(
  "S-Callable",
  stack(
    dir: ttb,
    spacing: 0.12em,
    [P' <: P],
    [R <: R'],
  ),
  [P → R <: P' → R'],
)

Behavioral callable types still need to be reconciled with the runtime: every
callable value at runtime is a bound-method heap object. The next rule is the
one-way bridge that exposes this fact in the static system.

#rule(
  "S-Callable-BoundMethod",
  stack(
    dir: ttb,
    spacing: 0.12em,
    [ct(BoundMethod) is defined],
    [MRO(BoundMethod) = M],
  ),
  [P → R <: class BoundMethod],
)

The bridge goes only one way. Callables are always `BoundMethod` instances,
but the system does not assume every `BoundMethod` instance inhabits an
arbitrary callable type. Finally, intersections of callables can be combined
into a single callable with a unioned domain and an intersected codomain:

#rule(
  "S-Callable-InterUnion",
  [],
  [(P → R) & (Q → S) <: (P | Q) → (R & S)],
)

The codomain `R & S` may look too strong at first glance — calling the
function with a `P` input yields an `R`, not necessarily an `R & S`. The
rule is sound because FwPython reads callable types intensionally. A
bound-method object stores exactly one parameter type and one return
type, and inhabiting both `P → R` and `Q → S` forces that single stored
signature to be wider than `P` and `Q` in the parameter and narrower
than `R` and `S` in the return. The same object therefore inhabits the
unified `(P | Q) → (R & S)` directly. This is the rule that lets the
typing rules collapse an intersection of callable views into one
callable wherever a single one is expected.

== Class-Only Negative Fragment

Negative typing is the most carefully constrained part of the static design.
Most type systems either avoid negation entirely or admit a generic semantic
complement. FwPython does neither. It introduces a single negative form,
`negClass(C)`, whose meaning is anchored in a runtime fact that the system
can actually witness: the runtime class's MRO does not contain `C`.

Three primitive rules define the fragment. The first lifts a runtime
exclusion fact about a sealed built-in class into subtyping. The second
expresses that every object is either an instance of a class or an instance
of its negation. The third makes class membership and class exclusion mutually
exclusive at the type level.

#rule(
  "S-SealedClass-NegClass",
  stack(
    dir: ttb,
    spacing: 0.12em,
    [LeafBuiltin(B)],
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

The premise `LeafBuiltin(B)` is restricted to exactly three classes:
`Bool`, `NoneType`, and `BoundMethod`. This restriction is the open-world
boundary of the design. A user-defined class might be extended later with new
subclasses, so the fact that no shared subclass exists right now is not a
sound basis for a global non-overlap fact. The three designated built-ins are
sealed by `WellFormedClassTable`: the class table guarantees they cannot
acquire new descendants, so primitive global exclusion against them is safe.

What `negClass(C)` means is therefore exactly one thing: the runtime-class
MRO excludes `C`. It is not a generic semantic complement, not a non-overlap
claim about user-defined classes, and not a coarse callable / non-callable
summary type. The fragment intentionally stops short of those because there
is no runtime evidence to support them.

#theorem(
  "Theorem",
  "Class-Only Negative Helpers",
  [The library in `Negation.lean` exposes the callable-to-`BoundMethod`
   bridge, the leaf-built-in exclusion theorem, subtype-driven contradiction,
   antitonicity of `negClass`, the contradiction between callables and
   `negClass(BoundMethod)`, and the corollary that classes outside
   `MRO(BoundMethod)` are disjoint from all callables.],
)

The library deliberately offers no pseudocomplement law, no generic De Morgan
package, and no general negation-introduction rule. Every consequence is
derived from the three primitive rules above and from concrete MRO facts.

== Static Typing and Runtime Typing

The expression typing judgment

#align(center)[#formal([Γ ⊢ e : T])]

contains the rules one would expect from an object language with intersection
types: attribute access uses a class view of the receiver, calls consume
callable types, ordinary conditionals require a boolean test and return the
union of the two branch result types, and intersection introduction is general
at the term level so that a method value can be assigned a conjunction of
callable types.

The interesting rule is the specialized `isInstance` conditional. It keeps the
same union-shaped result as an ordinary conditional, but each branch of an
`isInstance(x, C)` test refines the type of `x` differently:

#rule(
  "T-IfIsInstance",
  stack(
    dir: ttb,
    spacing: 0.12em,
    [Γ(x) = T],
    [ct(C) is defined],
    [Γ[x ↦ T & class C] ⊢ e_t : R_t],
    [Γ[x ↦ T & negClass(C)] ⊢ e_f : R_f],
  ),
  [Γ ⊢ if isInstance(x, C) then e_t else e_f : R_t | R_f],
)

The positive branch records confirmed class membership. The negative branch
records exactly one nominal exclusion fact — not an arbitrary semantic
complement — and the overall conditional still reports the ordinary union of
the two branch results. This is the source of the design choice that pushed
`negClass(C)` into the type language in the first place.

Runtime typing is expressed by `ValueHasType ct h v T`. Because every value
is an object reference, this judgment offers several views of the same
underlying heap object: a class view (from the runtime class and its MRO);
a callable view (from a bound-method payload); a class-only negative view
(from a witness that the runtime MRO excludes a target class); and the
general subsumption and intersection-introduction rules.

The negative-typing constructor `ValueHasType.objRefNegClass` is what
operationally justifies the negative-branch refinement above. It requires a
heap lookup for the object, the existence and MRO of the target class, the
existence and MRO of the object's runtime class, and a proof that the target
class name is absent from the runtime MRO. The runtime rule therefore carries
exactly the same evidence — an MRO membership check — that the type-level
rule and the semantic interpretation will need.

== Semantic Foundation

To justify subtyping, FwPython gives types a denotational interpretation.
Rather than denoting types as classical sets, the development uses a small,
purpose-built semantic carrier:

#align(center)[#formal([SemObject ::= ordinaryCurrent(C, M) | ordinaryFresh(seeds) | boundMethod(P, R, M)])]

The first case represents an existing well-formed instance of class `C` with
MRO `M`. The second case represents a hypothetical instance of a fresh class
that is not yet in the table but whose MRO would respect a list of seed
ancestors. The third case represents a bound-method object with stored
parameter and return types. Types are interpreted pointwise:

- `class C` denotes objects whose runtime-class MRO contains `C`,
- `P → R` denotes bound-method objects whose stored signature is wider in the
  parameter and narrower in the return,
- `negClass(C)` denotes objects whose runtime-class MRO excludes `C`,
- and `union`, `intersection`, and `bottom` use the usual propositional
  clauses.

Semantic subtyping is then plain denotation preservation:

#align(center)[
  #formal([SemSubtype(ct, T, U) := ∀ obj, T.semDenotes(ct, obj) → U.semDenotes(ct, obj)])
]

The `ordinaryFresh` case is what makes the semantics open-world-sound. Proving
a subtyping claim wrong sometimes requires imagining a hypothetical class that
the current table does not yet contain. Rather than quantifying over all
possible extensions of the class table, FwPython packages those hypothetical
witnesses inside the semantic carrier itself. The benefit is that
`SemSubtype` stays pointwise in one class table, and the well-formedness
predicate on types stays local to that table as well. The decision procedure
can then operate on a single semantic universe rather than alternating between
syntax and an external extension relation.

#theorem(
  "Theorem",
  "Semantic Soundness of Subtyping",
  [If `T <: U`, then `SemSubtype(ct, T, U)`. In particular, every semantic
   object denoted by `T` in `ct` is also denoted by `U` in `ct`.],
  proof: [The positive cases are routine lattice and MRO transport. The
    negative cases compare positive and negative witnesses for the same runtime
    shape, use MRO determinism to align the witness lists, and derive the
    contradiction from stored MRO membership or exclusion facts.],
)

#theorem(
  "Theorem",
  "Constructive Characterization of Subtyping",
  [On well-formed inputs, declarative subtyping and semantic subtyping
   coincide: `IsSubtype ct T U` iff `SemSubtype ct T U`. The development also
   derives constructive decision procedures `isSubtype_decidable` and
   `semSubtype_decidable` from this equivalence.],
  proof: [Completeness searches over a shared decision space that either builds
    a declarative subtyping derivation or returns one `SemObject`
    counterexample witnessing semantic failure. The open-world cases are
    carried by `ordinaryFresh` objects rather than by a separate quantification
    over extended class tables.],
)

== Static Proof Architecture

Two engineering choices structure the static proofs. First, `IsSubtype` is
kept declarative, with transitivity as a primitive rule. Second, semantic
soundness is proved before the runtime metatheory, and the runtime proofs
recover their inversion lemmas from that semantic result.

Both choices serve the same goal: insulating the public theorem surface from
the choice of search algorithm. If transitivity were eliminated, the runtime
inversion lemmas would have to be phrased in terms of an algorithm's case
analysis, which would change every time the algorithm changed. By going
through semantic subtyping instead, the inversion lemmas can speak about the
meaning of a type rather than about the shape of a particular derivation.

The runtime preservation cases follow the runtime representation directly.
Attribute access allocates a fresh bound-method object. Calls recover
callable provenance from heap facts. The `isInstance` rule narrows the
typing environment with `class C` on one branch and `negClass(C)` on the
other. Each of these mirrors the corresponding small-step rule.

#theorem(
  "Theorem",
  "Static Type Soundness",
  [Assume a well-formed class table, a well-formed heap, a runtime
   environment matching the typing environment, and a derivation
   `Γ ⊢ e : T`. If the continuation machine terminates, then it finishes with a
   successful value `v` such that `ValueHasType ct h' v T`.],
  proof: [Safe states package heap well-formedness, environment typing,
    control typing, and continuation compatibility. Preservation shows that one
    safe state steps to another, progress rules out stuck safe states, and
    final-state inversion extracts the successful value case.],
)

= Gradual Layer

== From `any` to Boundaries

The gradual side starts from a single design tension. The source language
admits the type `any`, which represents a value the type system has lost
track of. Any sound treatment of `any` has to answer two questions. What
can the type system still guarantee about programs that contain `any`?
And what should happen, operationally, when an `any`-typed value reaches
a context that demanded something more specific?

A first instinct is to absorb `any` into the existing subtyping relation —
make `any` both a subtype and a supertype of every other type, and the
static system can keep doing what it always did. This does not work, for
two related reasons.

The first reason is that the move trivializes subtyping. With `any` both
above and below every type, transitivity gives `T <: U` for any `T` and
`U`: simply route through `any` in the middle. Subtyping collapses to the
trivial relation that holds between every pair of types, and nothing ever
fails to type-check. Gradual typing systems usually avoid this collapse by
replacing subtyping with a weaker, non-transitive relation called
*consistency*. Consistency lets `any` participate in compatibility checks
without turning every other check vacuous.

The second reason is deeper, and it survives the move to consistency.
Whatever the static system does or does not accept, *some operations will
still fail at runtime*. An `any`-typed value can flow into a context that
expected a callable, a class instance, or a particular intersection, and
sometimes the value will fit and sometimes it will not. Those failures are
not an optional feature — they are the only honest response to a source
program that declined to commit to a static contract. The real design
question is therefore not whether to defer checks to runtime, but how.

A naive answer is to compile `any` away by inserting implicit runtime
coercions and let the underlying machine raise an error when an operation
turns out to be impossible. This is operationally feasible, but it makes
both diagnostics and metatheory poor. When a failed `.foo` access on an
`any`-typed value crashes the runtime, no one can say which compile-time
decision is responsible. The type system declined to reject the access, but
it does not know *why* it declined or *where* in the source the mistake
ultimately lies.

FwPython takes the opposite stance. Every operation that the type system
admits *only* because of `any` is marked at compile time with an explicit
runtime check and a blame label. The check is performed at exactly the
moment the value crosses into a more demanding context. The label records
which compile-time decision is responsible for the cross. The runtime
never has to invent diagnostic information after the fact, because the
diagnostic information was attached to the program when the boundary was
inserted.

This refines what *soundness* can mean. A fully static type system can
promise that well-typed programs do not fail. A gradual system cannot
promise that, because the source language explicitly admits operations
whose safety is not statically decidable. What it can promise instead is
that failure is *localized*. A well-typed elaborated program in FwPython
finishes in one of exactly two ways. Either it succeeds, and the result
really does have the type the source typing claimed; or it fails with
blame at a specific boundary that the elaborator inserted. Crucially, it
does not get stuck in unchecked machine behavior — a compiled well-typed
run cannot reach a raw attribute-not-found, call-on-non-callable, or
similar primitive failure.

This localized form of soundness shapes the rest of the gradual layer. The
high-level strategy is the same one that runs through the gradual typing
literature, specialized to FwPython: keep the static type system honest
about what it really decides; defer the rest to runtime; make every
deferral explicit syntax rather than implicit coercion; track responsibility
so failures are diagnostic; and keep the runtime model uniform so that the
metatheory has only one operational story to reason about.

These informal commitments become formal theorems later in this layer,
and they fall into two groups. The first group formalizes the
localized-failure claim directly. _Gradual Soundness_ says that a compiled
well-typed run finishes either with a witnessed value or with blame —
never with raw machine failure. _Blame Correctness_ says that when a
final blame label appears, it really did come from a specific compiled
boundary, with the right party (provider versus context) held responsible.
_Unique Blame Origins_ says that the label is enough information to
identify the boundary unambiguously. Together these three theorems cash
out the promise that diagnostic information is attached at compile time
and remains recoverable at the end of execution.

The second group answers a different question: is the discipline
well-behaved as a development workflow? The _Static Gradual Guarantee_
says that elaboration respects type precision — making source annotations
less precise produces a less precise (but otherwise structurally similar)
compiled program, so the compiler does not panic when annotations are
weakened. The _Dynamic Gradual Guarantee_ says that execution respects
precision too: weakening an annotation toward `any` cannot turn a
previously successful run into a failing one. This is the formal
justification for treating `any` as a safe gradual retreat. A developer
who removes a precise annotation gives up some static checking, but they
are not introducing new ways for the program to fail. The reverse
direction is not symmetric — *adding* a precise annotation may introduce
new blame, because the tightened annotation can disagree with the values
that actually flow through it — and that asymmetry is itself part of the
intended contract: precision is added on purpose, blame for an incorrect
addition is the diagnostic.

The four subsections that follow instantiate this strategy. Source typing
decides which operations are statically certain and which require
deferral. Elaboration places the boundaries. The checked runtime executes
them and turns failures into blame. The metatheory then proves the
theorems above.

== Translation Pipeline

The gradual development is not a separate runtime. It is a translation
discipline on top of the static FwPython runtime. A gradual program goes
through four stages.

The first stage assigns a deterministic source type to each binding. This is
done by `GSrcInfer`, the gradual source typing judgment. The second stage,
`compileCheck`, takes a source typing derivation and an explicit expected
target type, and emits a checked term in which every dynamic obligation is
exposed as syntax: an `enforce` node, a dynamic attribute access, or an
explicit call boundary. The third stage runs that checked term on a
continuation machine designed for it; this machine carries explicit blame
labels and performs explicit boundary checks. The fourth stage proves the
whole pipeline correct: end-to-end soundness, blame provenance, and the
gradual guarantees.

Splitting the work into stages avoids a familiar trap. A direct metatheory
for a gradually typed surface language has to mix source typing, implicit
dynamic checks, blame assignment, and higher-order mediation in a single
operational model. By pushing all dynamic obligations into explicit syntax in
the checked target, FwPython can prove safety of a much smaller machine whose
control state always says exactly which boundary is being checked and which
labels would be blamed if it failed.

== Gradual Source Language

The source language is what the programmer writes. Its type language `GTy`
extends the static type language with a dynamic type:

- class types and callable types,
- the dynamic type `any`,
- unions, intersections, and class-only negation `negClass(C)`,
- `bottom`.

Method annotations are stored directly as `GTy`. The checked metatheory turns
them into explicit normalized checked targets only when they cross the
source/runtime boundary, through `checkedTargetOfRuntimePublicTy`. The old raw
helper `runtimePublicTy` survives only as the identity on `GTy` for
compatibility statements such as the end-to-end soundness theorem.

Source typing is expressed by `GSrcInfer`. It is deterministic, gives one
type per binding, and is deliberately confined to source-level information.
Two relations capture the source-level compatibility checks:

- `GradualSubtype` for one-way widening, and
- `AssignableTo` for assignment-like compatibility — the relation used at
  call sites and conditional branches.

The single-type discipline is intentional. Source typing is supposed to
explain what the programmer wrote and which source-level choices were made;
it is not supposed to precompute every checked approximation the runtime
might need. Checked approximations such as call-site target types and
boundary contracts are chosen later, where they are needed, by
`compileCheck`. If they were threaded through source environments instead,
every source theorem would have to talk about machine-facing artifacts
everywhere, even at sites where no boundary is involved.

The role of `any` in this layer is to be the gradual escape hatch. Where
the source program permits dynamic behavior — for example, accessing an
attribute on a value of type `any` — the source typing judgment admits the
operation and records that a runtime check will be needed. The exact
checked obligation is not chosen until elaboration.

The source summaries for attributes and calls are intentionally asymmetric.
Attribute lookup on a union succeeds if either branch provides the attribute
and unions the successful results. Attribute lookup on an intersection keeps
the unique successful branch if only one side provides the attribute and
returns an intersection only when both sides succeed. Calls behave dually:
calling a union succeeds only when both branches accept the argument, while
calling an intersection keeps a unique successful branch and collapses two
simultaneous successes to `any`.

That asymmetry carries into elaboration through the call-parameter target
helpers. `callParamTarget` and its checked-target image absorb `any`,
propagate `bottom`, remove duplicate intersections, and canonicalize the
order of the remaining branches. The checked/runtime proofs therefore compare
a stable concrete target tree rather than one that still remembers
source-level intersection ordering noise.

== Checked Target and Elaboration

The checked target layer uses an explicit machine-facing target syntax
`CheckedTarget` rather than reusing raw `GTy` annotations directly. Its core
operations are interpretation back to `GTy`, compilation to boundary
contracts, and the normalizer `coreNormalizeCheckedTarget`. Runtime-facing
checked targets are compared at this explicit syntax level, and checked
syntax stores boundary labels with direct indices
`BoundaryLabels (compileBoundaryTarget T)`.

There is no checked-target analogue of `runtimePublicTy`. Raw source
expectations enter the checked layer through `checkedTargetOfRuntimePublicTy`,
and the root-only structural premise at the public GG boundary is
`ProgramRootTargetInputPrecision` on those explicit checked-target images.

On top of that target syntax, the checked expression language extends the
static expression language with three forms that make dynamic obligations
syntactically explicit. The `enforce e target labels` form runs `e`, then
checks the resulting value against the compiled contract image of `target`,
blaming the indicated label tree on failure. The `dynAttrAccess e attrName ℓ`
form looks up an attribute on a value whose static type only guaranteed
`any`, blaming the label `ℓ` if the attribute is missing. The
`call callee arg paramTy returnTy returnLabels` form is the explicit call: it
stores the caller-side parameter and return checked targets, plus the label
tree that will own any return-side blame.

`compileCheck` produces these forms from a source typing derivation and an
explicit expected target. The expected target is what makes elaboration
target-relative: the same source expression compiles to different checked
terms depending on what the surrounding context expects.

The presence of `any` in the source forces dynamic uncertainty into the
runtime, but the design refuses to let that uncertainty become unchecked
machine failure. Wherever the source typing would otherwise rely on dynamic
behavior, elaboration emits a checked form whose failure mode is blame at a
specific label. The intent is that a well-typed elaborated program ends in
exactly two ways: it succeeds with a value witnessing the expected type, or
it blames at one of the boundaries the elaborator inserted. The checked
machine has a `runtimeError` case for engineering convenience, but the
soundness theorem rules it out for compiled well-typed runs.

#theorem(
  "Theorem",
  "Elaboration Typing",
  [`compileCheck_checked` proves that elaborating a `GSrcInfer` derivation
   against an expected target `P` yields a checked term typed at `P`, given an
   explicit checked typing environment together with
   `RuntimePublicAnnotation gct P` and `WellFormedGTy gct P`. The graph
   `ElabCheck` records that a checked expression/counter pair is the output of
   `compileCheck`; `compileCheck_elaborates` is its canonical witness and
   `elabCheck_checked` delivers checked typing from any such witness.],
  proof: [The proof is by induction on the source typing derivation. Each case
    compiles its subterms against the targets dictated by the elaboration
    scheme, then discharges the checked typing obligations with the local
    admissibility and well-formedness facts stored on the source derivation.],
)

== Checked Runtime and Enforcement

The checked runtime is a small-step continuation machine that runs over an
explicit heap. Its values are only object references — `CheckedValue.objRef
oid` — and its heap objects come in just two kinds: ordinary objects and
bound-method objects, where the latter carry a receiver OID and a checked
method.

Every callable value at runtime is therefore a bound-method heap object.
Both ordinary attribute lookup and dynamic attribute lookup allocate a fresh
bound-method object and return its reference. The same representation also
underpins callable witnesses and the call rules. This uniformity is what
allows the metatheory to reason about every callable interaction with the
same shape facts.

Boundary enforcement is expressed by `EnforceValue` over compiled
`BoundaryContract`s, not directly over `GTy`. Three properties of
enforcement matter for the proofs.

First, enforcement is heap-read-only. It performs no allocation and no
mutation. Second, callable enforcement is shallow: it asks only whether the
object reference points to a bound-method object. Higher-order obligations
about the callee's parameter and return contracts are not discharged here.
Third, when enforcement succeeds, it returns the same object reference it
was handed. Class checks, callable checks, negated-class checks, and the
unions and intersections built from them all preserve runtime value shape on
success.

Shallow callable enforcement is a deliberate choice. The natural
alternative — wrapping callable values to mediate higher-order contracts —
would manufacture new heap objects whose shape differs from the underlying
callee. That would complicate the dynamic gradual guarantee, which compares
two precision-related runs and needs the simulation to stay structural.
Keeping the callable check shallow leaves the higher-order obligations to
the explicit checked call syntax, where they can be discharged by the call
mechanism itself.

Calls are mediated by the checked call form and its supporting continuation
frames. Once evaluation reaches a bound-method callee, the machine performs
a fixed dance: evaluate the argument, enforce the method's stored parameter
contract, run the body in the `[param, receiver]` environment, enforce the
method's stored return contract, and finally enforce the caller's return
expectation using the call-site labels. The callee's own contract and the
caller's use-site expectation are two distinct checks, and they are both
explicit in the checked machine.

== Safe States, Labels, and Constructiveness

The central machine invariant is `CheckedStateSafe`. A safe state packages
the well-formedness of the checked heap, the well-formedness of the gradual
class table, the alignment of the gradual and checked class tables, the
typing of the runtime environment, the typing of the control component, and
the typing of the continuation. All six conditions hold simultaneously, and
preservation shows they continue to hold across each step.

Inside the progress and preservation proofs, the value-level invariant is
`CheckedValueWitness`. A witness records why a runtime value inhabits a
gradual type, with structure that mirrors the type itself: an `any` witness
records the value is a reachable object reference; a `class_` witness
records that the runtime MRO contains the class; a `callable` witness
records that the object is a reachable bound method whose receiver MRO
covers the callee class; and so on. Crucially, these witnesses are exact
rather than coarse — they record the same shape facts the operational rules
inspect, not a derived approximation.

Labels are part of the semantics, not anonymous debugging tokens. A label
records three things: the scope in which it was allocated, a site number,
and an owner. Ownership is determined by the polarity of the boundary it
guards. Positive boundaries blame the provider — the program that produced
the value. Negative boundaries blame the context — the program that
expected it. Recording ownership at compile time makes blame correctness
provable: a final blame label is enough information to identify both the
boundary and the party responsible for the failure.

The provenance layer packages the theorem-level origin through
`BoundaryOrigin` and `CompiledBoundaryOrigin`, while the dependent target and
label casts live in `BoundaryCast`. Cross-program blame comparison therefore
uses origin equivalence rather than literal equality of raw numeric
`Label.site` payloads.

The front end is constructive end to end. The MRO search `computeGMro?` is
an executable, fuel-bounded function, sound and complete with respect to
the inductive `GComputeMro` relation. Method-type lookup is built directly
on top of it. The well-formedness facts stored on each source derivation
supply the local decidability instances needed for the more complex
elaboration choices, including assignability, admissible targets, and
branch refinement. With those instances in scope, `compileCheck` is a
plain `def` rather than a classical existence proof. This matters because
the precision theorems compare concrete compiled outputs: if elaboration
were merely shown to exist, the theorems could only relate abstract
witnesses rather than the actual programs the compiler produces.

== Gradual Soundness

The first group of end-to-end theorems formalizes localized soundness for
the gradual layer: an elaborated program cannot fail in any way except by
reaching a boundary the elaborator inserted. Two theorems carry the
result. The first shows that elaboration produces a state that is safe to
start executing, and the second lifts that safety across the whole run.

#theorem(
  "Theorem",
  "Initial Safety of Elaborated Programs",
  [`compiled_initial_safe_at` and
   `compiled_initial_safe_from_elaboration_at` show that the initial checked
   state produced by elaboration is safe at `runtimePublicTy(P)`, equivalently
   at the interpretation of the recorded root checked target image.],
  proof: [`compileCheck_elaborates` produces the `ElabCheck` graph witness and
    `elabCheck_checked` delivers the typed control component. The
    initial-heap well-formedness lemma supplies the heap invariant, the empty
    runtime environment is trivially typed, and the record produced by
    elaboration packages the class-table alignment and runtime-public target
    admissibility facts needed to assemble one `CheckedStateSafe` state.],
)

#theorem(
  "Theorem",
  "Gradual Soundness",
  [`gradual_soundness_at` states that an elaborated well-typed gradual
   program either finishes with a value witnessing `runtimePublicTy(P)` or
   raises blame. It excludes raw `runtimeError` for compiled well-typed runs.],
  proof: [Initial safety comes from elaboration, preservation lifts safety
    across every checked step, progress rules out getting stuck in a safe
    non-final state, and final-state inversion shows that the only possible
    checked results are a success carrying a `CheckedValueWitness` or blame.],
)

== Blame Provenance

Soundness rules out unchecked failure, but it says nothing about how a
final blame relates to the source program that produced it. The
blame-provenance theorems answer that question. Together they show that
every final blame label can be traced back to one specific boundary in
the compiled program, with the right owner attached.

#theorem(
  "Theorem",
  "Blame Correctness",
  [`gradual_blame_correctness_at` shows that a final blame arises from a
   compiled boundary and that the boundary's expected owner matches the owner
   stored on the final blame label.],
  proof: [The provenance theorem first shows that every final blame label is a
    registered compiled label. Correctness then recovers the originating
    boundary from that label and appeals to the polarity-based owner
    calculation used during label construction.],
)

#theorem(
  "Theorem",
  "Unique Blame Origins",
  [`gradual_blame_provenance_origin_unique_at` shows that one final blame label
   determines one unique compiled origin.],
  proof: [Compilation assigns disjoint, scope-indexed label ranges to all
    boundary sites, and the provenance layer proves that the label-to-origin
    map is injective on registered labels. Two origin witnesses for the same
    final label therefore collapse to the same origin.],
)

== Precision and the Gradual Guarantees

The third group of theorems compares behavior across precision. The final
development uses three different layers, each for a different purpose.

At the source/annotation level, the semantic relation is `MoreStatic`.
Program-wide source comparison is expressed by `ProgramAnnotationPrecision`,
and source environments use the same-binding relation
`SemanticSourceEnvPrecision`. These theorems do not depend on literal
equality of compiled outputs.

At the checked/runtime level, structure is carried by explicit checked
targets. Two structural relations are used here. `CheckedTargetPrecision` is
constructor-directed on normalized `CheckedTarget`s and handles stored
checked annotations. `CompileTargetPrecision` is the slightly larger
compile-side relation used for generated payloads such as normalized
call-parameter targets. Together they lift to checked syntax, checked
programs, checked states, and final outcomes without quotienting checked
syntax by semantic target equivalence.

At the public static/DGG entry point, the surviving structural premises are
narrower:

- `ProgramTargetPrecision` fixes the same source skeleton while comparing
  method annotations through their explicit checked-target images;
- `ProgramRootTargetInputPrecision` is the separate root-only premise on the
  top-level expected target;
- `ElaboratedStatePrecision` is the DGG-only wrapper that extends checked
  state precision with elaboration and provenance alignment.

Outcome precision lifts the checked/runtime relation to final results.
Given two final results from related runs, `CheckedOutcomePrecision`
permits exactly three combinations:

- both runs succeed, with heaps and values that are themselves
  precision-related;
- the more precise run blames, while the less precise run succeeds;
- both runs blame.

The combination that is *not* permitted is the substantive content of the
theorem: a more precise run cannot succeed while a less precise run blames.
Equivalently, weakening an annotation toward `any` cannot turn a previously
successful run into a failing one. The intuition is that a more precise
type imposes tighter contracts at boundaries, so it can blame in places
where a looser type lets the value through; loosening cannot introduce
new failures that the tighter contracts did not already catch. This is the
monotonicity property that justifies treating `any` as a safe gradual
retreat. The reverse direction is not symmetric: *adding* precision can
introduce new blame, because the new annotation may disagree with the
values that actually flow through it.

#theorem(
  "Theorem",
  "Static and Dynamic Gradual Guarantees",
  [`static_gradual_guarantee` consumes `ProgramTargetPrecision`, a separate
   `ProgramRootTargetInputPrecision`, and two elaboration witnesses, and
   returns `CheckedProgramPrecision`; the companion corollary
   `static_gradual_guarantee_main_moreStatic` packages the surviving source
   `MoreStatic` fact for the main expression. `dynamic_gradual_guarantee`
   starts from the corresponding initial `ElaboratedStatePrecision` package
   and compares terminating executions with `CheckedOutcomePrecision`.],
  proof: [The static guarantee is a compilation theorem: it relates two
    same-skeleton source derivations and shows that their elaborated checked
    programs are related after erasing only the label payloads. The dynamic
    guarantee starts from those aligned initial elaborations and proves a
    simulation over `ElaboratedStatePrecision`. Its key enabling fact is that
    successful enforcement preserves runtime value shape, so the simulation is
    not derailed by wrapper allocation or other boundary-induced value
    transformations.],
)

The proof of the dynamic guarantee is structural. There is no appeal to a
back-translation, an erasure, or any external simulation argument. The
relation between the two runs is explicit at every step, and the simulation
is local because successful enforcement preserves runtime value shape.

= Limits and Design Boundaries

The recurring discipline of FwPython is that nothing enters the type
language unless the runtime can witness it. That discipline keeps the
development small, but it also excludes things other formalizations might
attempt. The most consequential omissions are worth naming explicitly so
the report does not overstate what is proved.

On the static side, the negative fragment stops at class exclusion. There
is no general semantic complement, no primitive negation over callable
types, and no negation over unions or intersections. The runtime can
witness that an object's runtime-class MRO excludes a particular class
name, and that is the only negative fact the type language admits. A
generic complement would justify reasoning the runtime cannot back up —
asserting that a value is "not callable" without committing to a specific
nominal class, for example — and that justification gap is exactly what
the design refuses to cross. The same reasoning explains why primitive
class exclusion is restricted to the three sealed built-ins: only those
classes are guaranteed not to acquire new descendants in any extension of
the table, so global exclusion against them remains safe in an open world.

Decidability of subtyping is conditional, not unconditional. The decision
procedures require the class table and both type operands to be
well-formed; ill-formed inputs are out of scope. And the static language
has no parametric polymorphism, no recursive types, and no first-class
mutable fields. Each of these would require new runtime evidence to
support a corresponding piece of static vocabulary.

On the gradual side, callable enforcement is shallow. A successful
callable check guarantees only that the value is a bound-method object
reference; it does not attach a wrapper or set up a longer-running
monitor. Higher-order obligations are discharged at the explicit checked
call form, not at the value itself. Wrapping callables would let FwPython
enforce richer interaction contracts across multiple call sites, but it
would also break the shape-preservation property that the dynamic gradual
guarantee depends on. The current design picks the guarantee.

The dynamic gradual guarantee is the binary outcome-precision form. It
relates the final results of two precision-related runs and nothing more.
There is no back-translation, no graduality reduction, and no equivalence
between executions at different precisions. Those stronger statements are
not theorems of this development.

The checked machine retains a `runtimeError` constructor for engineering
convenience. The soundness theorem rules it out for compiled well-typed
runs, but the constructor is still reachable from other transitions —
malformed inputs that bypass elaboration, for instance — and the
metatheory makes no promises about those runs. Concurrency, exceptions
other than blame, and side effects more broadly are outside the
formalization entirely.

What holding the boundary strictly buys is that every piece of vocabulary
in the static or gradual type language reduces to a fact about one
runtime model. The proofs do not have to mediate between competing
abstractions. Many properties that other gradually typed languages prove
are out of scope here, but everything FwPython does prove runs through one
continuation machine and one shape of value.

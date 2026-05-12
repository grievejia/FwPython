# FwPython

A Lean 4 formalization of a small object-oriented language and its gradual extension. The static development covers syntax, operational semantics, declarative subtyping, type checking, and soundness. The gradual layer adds the dynamic type `any`, an explicit elaboration into a checked target language with runtime boundaries, and an end-to-end metatheory of soundness, blame, and the gradual guarantees — all on top of the same runtime model.

The project is intended as a compact metatheory playground: small enough to reason about directly, but rich enough to study subtyping, branch narrowing, gradual elaboration, and blame in an object-oriented setting.

## What's Formalized

**Static core.** A typed object language with multiple inheritance via C3 linearization, behavioral callable types, primitive unions and intersections, and a deliberately narrow class-only negative fragment (`negClass C`). Subtyping is given a denotational interpretation over a custom semantic carrier and is decidable on well-formed inputs. Type soundness is proved against a small-step continuation machine.

**Gradual layer.** A source language extending the static type system with `any`, an executable elaborator (`compileCheck`) that compiles source programs into a checked target where every dynamic obligation is explicit syntax, a proof-level graph (`ElabCheck`) that exposes the compiler's input/output as a Prop, and a checked runtime that turns dynamic failures into blame at known compiled boundaries. The metatheory establishes:

- *Gradual Soundness* — for programs whose top-level type lies in the runtime-public target fragment, any compiled well-typed run that reaches a final state does so with either a witnessed value or a blame label; raw machine failure is excluded.
- *Blame Correctness* and *Unique Blame Origins* — each final blame label traces back to one specific compiled boundary with the right party (provider vs. context) held responsible.
- *Static and Dynamic Gradual Guarantees* — elaboration respects type precision; for two precision-related programs that both reach a final state, the more-precise side cannot terminate with a value while the less-precise side terminates with blame, so weakening an annotation toward `any` never turns a previously successful terminating run into one that blames.

The whole development is constructive: the MRO search and the elaborator are plain executable definitions, and the precision theorems compare concrete compiled programs rather than abstract witnesses.

## Building

Install [`elan`](https://github.com/leanprover/elan) (the Lean version manager). The pinned toolchain is recorded in `lean-toolchain` and will be fetched automatically the first time you build:

```bash
lake build
```

The `lakefile.toml` exposes two libraries that are both built by default:

- `FwPython` — the main metatheory development. Building it means typechecking every definition and proof in `FwPython/`.
- `FwPythonExamples` — the regression suite under `FwPython/Examples/`. Each entry is a small `example :` lemma that pins down a concrete instance of the metatheory (typing rules, subtyping shapes, blame correctness, evaluation steps, …). There is nothing to run: the Lean elaborator is the test runner, and a successful build means every regression still typechecks.

To build only the regression suite (e.g. while iterating on a proof and wanting fast feedback), use:

```bash
lake build FwPythonExamples
```

Note that this still requires the `FwPython` library to be built first, because the examples import from it.

## Provenance

This repository was developed primarily with AI coding assistants under human
direction and review. The design, theorem statements, and accepted changes were
selected by the author, while Lean's checker remains the final authority on the
formal claims in the codebase. Readers may notice some stylistic unevenness
typical of AI-assisted proof development, but the intended artifact is the
checked development produced by `lake build`.

## Repository Layout

- `FwPython/Common/` — shared scaffolding used by both the static and gradual layers: `Identifier`, the class-table data model, named environments, the heap container, list relations, small-step closures, and the payload-parameterized MRO machinery under `FwPython/Common/MRO/`. `FwPython/Common.lean` is the umbrella import that re-exports the subtree.
- `FwPython/Builtins.lean` — built-in class names and their pre-allocated object IDs.
- `FwPython/Static/` — the static type system, organized into AST, class table, MRO, subtyping, semantics, type system, and soundness. `FwPython/Static/Language.lean` is the public surface.
- `FwPython/Gradual/` — the gradual layer: gradual source language, checked target, checked runtime, elaboration, soundness, blame, and precision. `FwPython/Gradual/Language.lean` is the public surface.
- `FwPython/Examples/` — regression examples and executable proof demos.
- `docs/` — natural-language documentation for the language and metatheory.

## Documentation

The prose docs in `docs/` are maintained alongside the Lean development:

- `docs/syntax.md` — language syntax reference, kept in sync with `FwPython/Static/Ast.lean` and `FwPython/Static/ClassTable.lean`.
- `docs/type_system.md` — static type system design: subtyping rules, the inversion problem, the semantic carrier, and decidability.
- `docs/gradual.md` — gradual layer: glossary, architecture, checked target, enforcement, blame, and the gradual guarantees.
- `docs/report.typ` — a self-contained Typst report covering the whole development end to end, including the design rationale behind the gradual setup.

The first three files render directly on GitHub. The Typst report is the only optional artifact: it is distributed as source (`docs/report.typ`) rather than as a PDF, since the rendered output is a generated binary and is not checked in.

To build the PDF locally, install [Typst](https://github.com/typst/typst) (e.g. `cargo install --locked typst-cli`, `brew install typst`, or a release binary from the project page), then run:

```bash
typst compile docs/report.typ docs/report.pdf
```

The output is written to `docs/report.pdf`, which is `.gitignore`d.

## License

This project is licensed under the MIT License — see [LICENSE](LICENSE) for the full text.

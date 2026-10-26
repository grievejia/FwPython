# FwPython

FwPython specifies a small object-oriented language and proves its type safety
in Lean 4. The language supports multiple inheritance, method values, and class
tests that refine variable types inside branches.

The static type system includes class types, function types, unions,
intersections, and class exclusion. Subtyping follows from equations between
types. Its checker is proved to accept exactly the pairs related by subtyping.

The gradual type system adds `any` for unknown type information. The compiler
inserts runtime checks when the program needs information that its annotations
do not provide. A failed check produces a report linked to its source location,
called *blame*.
For a correctly compiled program that finishes, the result satisfies the
expected type or is blame. The soundness theorem excludes unchecked runtime
errors; it does not require termination.

The development is constructive and has no external library dependencies.
Executable definitions for method resolution, subtype checking, and compilation
have correctness proofs.

## Build

Install [elan](https://github.com/leanprover/elan), the Lean version manager,
then run:

```bash
lake build
```

The file `lean-toolchain` selects the Lean version. Elan downloads that version
when needed. The build checks two libraries:

- `FwPython`: the language definitions and proofs.
- `FwPythonExamples`: regression examples, each expressed as a Lean lemma.

A successful build means the definitions, proofs, and examples all typecheck.
To build the examples and their required imports, use:

```bash
lake build FwPythonExamples
```

## Read the documentation

| Document | Purpose |
| --- | --- |
| [Syntax](docs/syntax.md) | Reference for programs, declarations, and expression forms. |
| [Static type system](docs/type_system.md) | Reasons for the type rules, subtype checker, and safety proof. |
| [Gradual typing](docs/gradual.md) | How unknown types affect source checking, compilation, runtime checks, and safety. |
| [Report](docs/report.typ) | Self-contained academic account for programming language researchers, with formal rules, examples, and proof arguments. |

The report uses [Typst](https://github.com/typst/typst). To generate its PDF, run:

```bash
typst compile docs/report.typ docs/report.pdf
```

The generated PDF is excluded from version control.

## Find the code

- `FwPython/Common/`: definitions shared by the static and gradual systems.
- `FwPython/Builtins.lean`: builtin class names and initial object identifiers.
- `FwPython/Static/`: static language, evaluation, typing, and proofs.
- `FwPython/Gradual/`: gradual source language, compiler, checked runtime, and proofs.
- `FwPython/Examples/`: regression examples and proof demonstrations.

Import the language definitions through `FwPython.Static.Language` or
`FwPython.Gradual.Language`. The `FwPython.Static` and `FwPython.Gradual` imports
include each system's type rules and proofs.

## Authorship and license

AI coding assistants contribute under the author's direction and review.
Lean checks the formal definitions and proofs.

The project uses the MIT License. See [LICENSE](LICENSE).

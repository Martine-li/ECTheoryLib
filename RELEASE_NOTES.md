# ECTheoryLib v0.1.0

The initial public release provides reusable Lean 4 tools for the
runtime analysis of evolutionary algorithms. Its first development phase follows
Chapters 1 and 2 of *Theory of Evolutionary Computation*, with a current emphasis
on drift analysis and its probability prerequisites. Full textbook and chapter
attribution is maintained in [SOURCES](docs/SOURCES.md).

## Tools provided by this version

- [Abstract drift tools](ECTheoryLib/Tools/Drift/README.md): additive, variable
  and multiplicative expectation bounds, lower bounds, tails, geometric-jump
  bounds and interval-local negative drift. Each interface retains its own
  range, absorption and conditioning premises.
- [Probability tools](ECTheoryLib/Probability/README.md): waiting-time and
  tail-to-mean interfaces, stochastic domination and couplings, concentration,
  sampling, negative dependence and conditional expectations. These include
  direct Mathlib reuse, bridges and further formalized tools, with attribution
  in the textbook map and source modules.
- [Runtime bridges](ECTheoryLib/Tools/Runtime/README.md): connect supplied
  transition PMFs, initial laws, targets, invariants, potentials and proved local
  inequalities to trajectories and hitting-time conclusions. Fixed evaluation
  costs are handled separately from update counts.
- [Modeling components](docs/ARCHITECTURE.md): search spaces, objective functions,
  operators and algorithm kernels, with model-specific invariants and selected
  problem-specific runtime analyses.

## Reading and using the release

Start with the [README](README.md) to choose a tool by task and see the premises
the user supplies. The [dependency guide](docs/QUICKSTART.md#use-in-your-own-lean-project)
explains the `ec-theory-lib` package name, `ECTheoryLib` imports, local-path and
pinned Git requirements, and Lean/Mathlib compatibility. The repository is
[Martine-li/ECTheoryLib](https://github.com/Martine-li/ECTheoryLib), with planned
tag `v0.1.0`. The tagged Git instructions become usable after the regular Release
and its tag have been created.

[Quickstart](Examples/Quickstart.lean) calls existing results;
the [local-drift tutorial](docs/LOCAL_DRIFT.md) explains how to organize an analysis
with general interfaces. Worked cases such as
[RLS–OneMax](ECTheoryLib/Analysis/OneMax/RLS/ExactRuntime.lean) and the
[positive-linear EA](ECTheoryLib/Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean)
show how models, potentials and probability tools combine. Their initialization,
algorithm variants and update-count conventions are stated in the linked
declarations and textbook map.

[COVERAGE](docs/COVERAGE.md) complements this task-based route with textbook
numbers, exact declarations, implementation status and source relations. The
[content guide](docs/CONTENTS.md) contains the full file index.

The distribution contains formal sources, fixed dependency configuration,
documentation and a small set of executable examples and useful counterexamples.
It omits the full internal test suite, acceptance tools and process logs.
The public `check.ps1` builds the library and checks the published examples.
[VALIDATION](docs/VALIDATION.md) states the scope of the existing build, internal
regression and axiom-audit evidence, and its reproduction limits.

## Scope and dependencies

Several numbered examples, the general population level-based theorem, signed
linear-weight normalization and broader mutation-rate/sharp-constant results are
unfinished. Some source displays have revised formal counterparts; the
[source notes](docs/SOURCE_NOTES.md) explain the conditions and finite examples.
The textbook is a construction and checking guide, not a limit on where the
tools can be applied. ECTheoryLib remains under active development: this release
does not imply complete chapter coverage, reproduction of every source proof
route or a stable public API.

- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All transitive dependency revisions are locked in `lake-manifest.json`.

The software author is **Mingfeng Li**, and the license is **Apache-2.0**.
Software attribution, license terms and mathematical sources are recorded in
[CITATION.cff](CITATION.cff), [NOTICE](NOTICE) and [SOURCES](docs/SOURCES.md).
The [publication steps](CONTRIBUTING.md#publishing-the-initial-release) use tag
`v0.1.0` and a regular GitHub Release. This preparation changes version, citation,
license-status and release documentation; the Lean sources, fixed dependencies
and previous verification records retain their existing content and scope.

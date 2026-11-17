# ECTheoryLib

**A Lean 4 library for the runtime analysis of evolutionary algorithms.**

Initial public release: **v0.1.0**.

ECTheoryLib formalizes probability tools, drift arguments and algorithm runtime
analyses. Its first development phase follows Benjamin Doerr and Frank Neumann
(eds.), *Theory of Evolutionary Computation: Recent Developments in Discrete
Optimization*, Springer, 2020
([DOI: 10.1007/978-3-030-29414-4](https://doi.org/10.1007/978-3-030-29414-4)):

- Chapter 1, *Probabilistic Tools for the Analysis of Randomized Optimization
  Heuristics*, by Benjamin Doerr.
- Chapter 2, *Drift Analysis*, by Johannes Lengler.

Current work emphasizes drift analysis and its probability prerequisites.
ECTheoryLib is under active development, with partial coverage of the first two
chapters of *Theory of Evolutionary Computation*. Code is organized by mathematical
dependencies for reuse beyond the textbook. Full chapter references are in
[SOURCES](docs/SOURCES.md).

## What you can use

| Task | Tools and starting point |
| --- | --- |
| Use probability estimates | [Probability](ECTheoryLib/Probability/README.md): waiting times, random processes, conditional expectations, stochastic domination, couplings and concentration. Includes direct Mathlib reuse, library bridges and further formalized tools. |
| Apply drift analysis | [Tools/Drift](ECTheoryLib/Tools/Drift/README.md): additive, variable, multiplicative and interval-local negative drift, with expectation and tail bounds under the respective hypotheses. |
| Derive runtime from local progress | [Tools/Runtime](ECTheoryLib/Tools/Runtime/README.md) and the [local-drift tutorial](docs/LOCAL_DRIFT.md): supply the actual transition law, initialization, target, potential, invariants and proved local conditions; reuse the trajectory and hitting-time deductions. |
| Build or study an algorithm analysis | [Architecture](docs/ARCHITECTURE.md), [models](ECTheoryLib/Algorithms/README.md) and [analyses](ECTheoryLib/Analysis/README.md): reuse search spaces, objectives and operators, and distinguish model definitions, proved properties and runtime results for particular problems. |

Follow the linked statements for their domains, including absorption, range and
conditioning assumptions. Runtime results count updates after initialization;
[fixed evaluation costs](ECTheoryLib/Tools/Runtime/Cost.lean) are modeled separately.

## Install and use

Install [Elan](https://github.com/leanprover/elan). In a local checkout or extracted
source package, use:

```sh
lake exe cache get
lake build
lake env lean Examples/Quickstart.lean
```

To use ECTheoryLib in **your own Lean project**, follow the
[dependency guide](docs/QUICKSTART.md#use-in-your-own-lean-project). The Lake
package is `ec-theory-lib`; Lean imports start with `ECTheoryLib`, for example
`import ECTheoryLib.Analysis.OneMax.RLS`. The guide provides local-path and pinned
Git dependency templates and the required Lean/Mathlib versions.

## Documentation and examples

- [Textbook coverage](docs/COVERAGE.md): find declarations and conditions by book
  number, with implementation status and source differences.
- [Quickstart](Examples/Quickstart.lean): minimal calls to existing theorems.
  [Analysis](ECTheoryLib/Analysis/README.md) leads to complete worked cases;
  [Examples](Examples/README.md) also includes mathematical counterexamples.
- [Content guide](docs/CONTENTS.md): browse by topic and find every formal module.
- [Source notes](docs/SOURCE_NOTES.md) and [validation](docs/VALIDATION.md): source
  comparisons, existing checking evidence and reproduction limits. The public
  check covers the library and published examples; the full internal suite is
  maintained separately. `lake build` alone does not run the examples.

## Contributing, citation and license

See [CONTRIBUTING](CONTRIBUTING.md) for feedback, proof contributions and release
publication steps. Cite the software using [CITATION.cff](CITATION.cff) and the
relevant mathematical [sources](docs/SOURCES.md). The software author is Mingfeng
Li, and ECTheoryLib is licensed under [Apache-2.0](LICENSE). Development uses AI
assistance, including OpenAI Codex; Lean checks formal proofs, while source and
model fidelity require separate review.

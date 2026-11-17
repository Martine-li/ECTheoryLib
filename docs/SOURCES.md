# Sources and attribution

The first development phase follows the first two chapters of Benjamin Doerr
and Frank Neumann (eds.), *Theory of
Evolutionary Computation: Recent Developments in Discrete Optimization*,
Springer, 2020, [book DOI](https://doi.org/10.1007/978-3-030-29414-4).

- Benjamin Doerr, *Probabilistic Tools for the Analysis of Randomized
  Optimization Heuristics*, Chapter 1, pp. 1–87,
  [chapter DOI](https://doi.org/10.1007/978-3-030-29414-4_1).
- Johannes Lengler, *Drift Analysis*, Chapter 2, pp. 89–131,
  [chapter DOI](https://doi.org/10.1007/978-3-030-29414-4_2).

Current work emphasizes drift analysis and its probability prerequisites. This
is a formalization organized by mathematical dependencies, with reusable tools
that can also serve analyses beyond the textbook. The current number-to-code map
is [COVERAGE](COVERAGE.md); it records partial coverage and the relation of each
listed interface to the source. Material differences from this edition are
described in [SOURCE_NOTES](SOURCE_NOTES.md). Other mathematical and algorithm
sources are cited in the corresponding Lean modules.

[CITATION.cff](../CITATION.cff) is the software citation for ECTheoryLib.
Mathematical attribution belongs in citations to the relevant chapters and
source papers.

Mathlib is a fixed external dependency. Its measure, probability, analysis and
algebra results are reused through imports and bridges; they are not presented
as original results of ECTheoryLib. The lock file identifies Mathlib and all
transitive dependencies by exact Git revisions. Their own upstream license files
remain authoritative. The dependency sources are fetched separately, not vendored
in this package. Textbook PDFs and reading snapshots are not distributed.

The maintainer has confirmed **Mingfeng Li** as the software author and
**Apache-2.0** as the license for **v0.1.0**. These decisions are recorded in
[PROVENANCE](../PROVENANCE.json). Software citation information is provided for
scholarly attribution; it does not add a paper-citation condition to the license.
Publication URL, date and DOI are added only when established. The textbook
editors and chapter authors are credited as mathematical sources, separately
from software authorship. Dependencies retain their own licenses and attribution.

AI-assisted tools, including OpenAI Codex, were used in formalization, proof
development, documentation and source-correspondence work. Lean checks the formal
statements and proofs under their definitions and assumptions; correspondence to
the textbook or intended algorithm model requires separate review. No independent
human audit of all source comparisons is recorded here. AI tools are disclosed
as development assistance, separately from software authorship.

## Historical references

Some unchanged source comments name development reports under `docs/reports/`
or earlier coverage ledgers. Those are archival references to internal acceptance
work, not additional current documentation shipped in this package. The original
reports and complete regression evidence remain in the internal development
archive. [SOURCE_NOTES](SOURCE_NOTES.md) supplies the current reader-facing
comparisons, with executable mathematical examples included where referenced.

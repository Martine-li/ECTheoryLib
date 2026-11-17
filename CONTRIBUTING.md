# Contributing

The public repository is intended to receive questions, bug reports and pull
requests. Include the relevant source entry or Lean module, the expected behavior
or statement, and a small reproducer where applicable. Keep a PR focused on one
change and describe its mathematical and interface effects.

The maintainer still needs to confirm how accepted public PRs reach the internal
development mainline and how reviewed internal changes return to the public
repository. The canonical branch and merge/cherry-pick/export procedure are
pending decisions; no automatic synchronization is configured.

Choose an open or partly proved entry in [COVERAGE](docs/COVERAGE.md), or a
concrete reusable interface needed by an existing analysis. Chapter 2 drift and
its probability prerequisites are the current priority.

Before a proof, state the intended theorem, textbook edition/number and exact
parameter, initialization, conditioning and time conventions. Separate an
original conclusion, an explicit convention, a restricted scope and a substantive
revision. A new proof route can establish the same conclusion; a changed formula
needs its own source explanation and, when relevant, a counterexample.

Reuse the existing layers and public interfaces. Put objective definitions in
`Problems/`, operators in `Operators/`, algorithm kernels in `Algorithms/`, and
runtime applications in `Analysis/`. Keep public names and paths stable where
possible; explain any mathematical or interface change.

Include a small client or semantic check that exercises the new interface,
initialization or boundary condition. Run the library build and relevant checks;
maintainers also run the internal semantic regression and transitive axiom audit
before integrating mathematical changes. The public `check.ps1` checks only the
distributed library and examples. No new `sorry`, `admit`, extra axioms, weakened
statements or relaxed audit policy may replace a proof.

Update the current map and any affected source notes. Describe what was checked
and keep source interpretation separate from Lean acceptance. Do not replace
historical validation records with results for changed code.

## Publishing the initial release

Repository: `https://github.com/Martine-li/ECTheoryLib`.
Git clone URL: `https://github.com/Martine-li/ECTheoryLib.git`.
Confirmed version and tag: `v0.1.0`. The maintainer has confirmed Mingfeng Li as
the software author, Apache-2.0 as the license and a **regular GitHub Release**.
The installation and citation metadata contain these confirmed coordinates.
The `v0.1.0` tag is an intended release ref until the tag and regular Release
are actually created.

1. Finish the documentation and metadata first: verify the repository and clone
   URLs, `v0.1.0` dependency ref, software citation, author and license. Include
   these final installation instructions in the commit to be released. Omit an
   unknown publication date or DOI.
2. After explicit publication authorization, commit and push the finalized
   distribution to the repository above. Publish the source package rather than
   the internal workspace, its private history, full tests or process logs.
3. Confirm successful GitHub Actions for that exact final commit. If documents
   or metadata need another change, commit and push it and confirm CI for the new
   commit before tagging; existing local records do not establish remote CI.
4. On the same CI-passed commit, create tag `v0.1.0` and a **regular GitHub
   Release**, leaving the pre-release option disabled. Do not defer installation
   or citation edits until after tagging. Keep the published tag immutable.
5. On the maintainer's GitHub profile, use **Customize your pins** to pin the
   public repository.

GitHub's guides cover [creating a release](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)
and [pinning a repository](https://docs.github.com/en/account-and-profile/setting-up-and-managing-your-github-profile/customizing-your-profile/pinning-items-to-your-profile).

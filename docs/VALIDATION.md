# Validation and reproduction

## Recorded candidate evidence

The checks below were recorded for the internal candidate
**v0.1.0-preview.2**. The initial public release **v0.1.0** changes version,
citation, license confirmation and release documentation while retaining the
formal sources, examples and fixed dependencies. These are existing results,
not a new Lean verification run for the release metadata.

The local distribution check on **2026-11-16** strictly built the formal library
and checked all **six** published Lean example files: seven checks in total, all
passed, with source hashes unchanged during the run. The check used Lean 4.33.0
and the locked Mathlib revision. The internal transitive axiom audit was also
rerun against the unchanged library and passed for **4,619 environment
declarations**, including generated auxiliaries. This is not a count of
independent mathematical theorems. The allowed axioms remain exactly `propext`,
`Classical.choice` and `Quot.sound`.

The [unchanged candidate verification summary](../validation/release.json)
records the original version, dates and scopes. Its relative file references
belong to that candidate-era record; the original candidate package and manifest
remain in the maintainer's archive. The current [FILES.json](../FILES.json)
inventories the v0.1.0 files and SHA-256 hashes, excluding its own entry to avoid
a circular self-hash. The ZIP has a separate checksum.

The candidate documentation checks covered local links/anchors, the complete
formal-file index, named API references, executable README/local-drift snippets,
CFF 1.2.0 metadata, PowerShell syntax, CI configuration and dependency revisions.
The v0.1.0 preparation uses only lightweight static metadata and link checks.
Neither establishes mathematical source interpretation or an independent human
review.

An independent downstream project also successfully imported the public additive
drift module and compiled the Quickstart call to `FixedRuntimeExact`, using a
local path to the candidate and fixed-version public dependency/build caches.
This is local-path integration evidence, not verification of a fresh network or
GitHub installation. That client and its logs remain separate from the release.

## Reproduce the public checks

For first installation, fetch the dependencies/cache and build:

```sh
lake exe cache get
lake build
```

`lake build` checks the formal library target. To also check all published
examples with warnings as errors, run the PowerShell helper:

```powershell
./check.ps1
```

Or use a POSIX shell:

```sh
set -eu
lake --wfail build
for example in Examples/*.lean; do
  lake env lean -DwarningAsError=true "$example"
done
```

The helper writes `validation/latest-check.json` for the user’s own run.
Neither command invokes the full internal regression or an internal axiom-audit
tool: those files are deliberately absent from this distribution.

## Internal and historical evidence

The frozen mathematical baseline is E07bv (source commit
`efc736718620718acfeccc26d66a0d0c0ff80dfb`). All **432 formal Lean files**,
including the root import, retain their accepted content. The **193 internal
test files**, complete regression script, transitive axiom audit and necessary
validation records remain in the internal development copy.

The prior isolated run finished on **2026-11-15** with **195 checks passed**:
one formal library build, 193 internal test files (including the axiom audit),
and the earlier Quickstart client. Its immutable historical record is identified
by hash in [PROVENANCE](../PROVENANCE.json); the full log and original records
remain internal. It is not relabeled as a run of the modified distribution.

No internal test was removed on an unverified assumption of redundancy. The
public examples extract coherent mathematical families needed by the current
documentation; diagnostic `#check`/`#print axioms` commands are omitted from the
extractions while their internal originals remain intact. The release therefore
has a deliberately smaller executable check scope, not the same 193-file suite
under a new name. The unchanged internal suite was not rerun solely for this
packaging change. Library and examples share one library build in the public
check, and dependency setup does not repeat that build.

## Dependency and CI reproduction limits

All nine dependency revisions remain fixed. Local checking used independent
source exports at those revisions and existing compiled caches; private path
overrides selected those copies without changing the published Git configuration.
This verifies the distribution’s library/example build without `Tests/`, but
does **not** establish a clean first-time network installation or a completely
cold recompile. A native Git probe could not reach GitHub through the configured
local proxy, so dependency fetching from an empty cache was not completed.

The [CI workflow](../.github/workflows/lean.yml) fetches the fixed dependencies,
then runs the distribution check once. It has no dependency on the excluded
suite. Its two action revisions and supported inputs were checked against their
upstream files at the exact pinned commits. No remote CI run was performed; its
status is unverified, rather than passed.

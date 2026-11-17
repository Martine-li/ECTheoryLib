# Getting started

Install Elan and a Lean-capable editor (normally VS Code with the Lean 4
extension). Open the project directory, not an isolated `.lean` file. Elan reads
`lean-toolchain`; Lake reads `lakefile.toml` and `lake-manifest.json`.

## First use

From the project directory:

```sh
lake exe cache get
lake build
lake env lean Examples/Quickstart.lean
```

Dependency setup needs network access on a new machine. Use the committed lock
file; `lake update` is not part of this installation procedure. The equivalent
PowerShell dependency helper is `./setup.ps1`; it fetches the cache and checks
that setup did not change the lock. It does not build the library.

The three [Quickstart examples](../Examples/Quickstart.lean) show fixed-state
RLS–OneMax, uniformly initialized RLS–LeadingOnes and an arbitrary-initial-law
positive-linear EA bound. Importing a result brings in its dependencies. Import
`ECTheoryLib` when the full API is convenient.

## Use in your own Lean project

The package and import names serve different purposes:

| Name | Where it is used |
| --- | --- |
| `ec-theory-lib` | Lake dependency name in `lakefile.toml` and `lake update ec-theory-lib`. |
| `ECTheoryLib` | Lean library and import prefix, such as `ECTheoryLib.Analysis.OneMax.RLS`. |

Use `leanprover/lean4:v4.33.0` in your project's `lean-toolchain`. Version 0.1.0
pins Mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d`. If your project also
requires Mathlib directly, align that requirement with the same revision. Other
Lean/Mathlib combinations are outside the recorded compatibility evidence.

### Local dependency

This works before a public repository is available. If your project and a source
checkout named `ECTheoryLib` are sibling directories, add to your project's
`lakefile.toml`:

```toml
[[require]]
name = "ec-theory-lib"
path = "../ECTheoryLib"
```

Adjust `path` to the actual checkout or extracted source directory. It is relative
to the requiring project's directory. This uses the source package as a dependency;
building inside ECTheoryLib itself is the separate first-use procedure above.

### Git dependency after publication

The repository is [Martine-li/ECTheoryLib](https://github.com/Martine-li/ECTheoryLib),
and the planned release tag is `v0.1.0`. Use the Git instructions below only after
the regular Release and its `v0.1.0` tag have been created. Until the tag exists,
this version cannot be fetched by that ref; use the local-path method before
that step.

```toml
[[require]]
name = "ec-theory-lib"
git = "https://github.com/Martine-li/ECTheoryLib.git"
rev = "v0.1.0"
```

For a separate clone after the Release is published:

```sh
git clone --branch v0.1.0 https://github.com/Martine-li/ECTheoryLib.git ECTheoryLib
cd ECTheoryLib
```

Then use the first-use commands above. The
[maintainer publication steps](../CONTRIBUTING.md#publishing-the-initial-release)
put final documentation and metadata before the commit, CI check and release tag.

### Resolve the dependency and call a theorem

After adding one of the requirements above, run in **your own project**:

```sh
lake update ec-theory-lib
lake exe cache get
lake build
```

Keep the resolved `lake-manifest.json` in your project so its complete dependency
graph is reproducible. Use a fixed release tag or full commit instead of a moving
branch; do not replace your project's lock file with ECTheoryLib's lock file.
The syntax follows the [Lake 4.33 dependency documentation](https://github.com/leanprover/lean4/blob/v4.33.0/src/lake/README.md#toml-require).

The following existing Quickstart call can be placed in a Lean file in your
project. It applies the fixed-state RLS–OneMax theorem for n>0; k is the initial
zero count, and runtime counts updates after initialization.

```lean
import ECTheoryLib.Analysis.OneMax.RLS

open ECTheoryLib

example {n : Nat} (PositiveLength : 0 < n) (InitialState : Bits n) :
    Analysis.RLSOnOneMax.ExpectedRuntime PositiveLength InitialState =
      ENNReal.ofReal ((n : Real) *
        (harmonic (Analysis.RLSOnOneMax.ZeroCount InitialState) : Real)) := by
  exact Analysis.RLSOnOneMax.FixedRuntimeExact PositiveLength InitialState
```

This calls an existing result. For a new algorithm analysis, follow
[LOCAL_DRIFT](LOCAL_DRIFT.md) to supply a model and prove its local hypotheses.

## Check the distribution

On Windows PowerShell or PowerShell 7:

```powershell
./check.ps1
```

This strictly builds the formal library and checks every published Lean example
with warnings treated as errors. It writes `validation/latest-check.json`.
If local Windows policy blocks a reviewed script, the commands may also be run
directly in a terminal; the [validation guide](VALIDATION.md) gives the portable
shell equivalent. The public check does not require `Tests/` or internal audit
tools. It does not reproduce the complete internal semantic regression.

## Choose an entry point

| You have… | Start here |
| --- | --- |
| A textbook number | [COVERAGE](COVERAGE.md) |
| A random process and drift hypotheses | [Tools/Drift](../ECTheoryLib/Tools/Drift/README.md) |
| A transition PMF, target and local inequality | [Local drift to runtime](LOCAL_DRIFT.md) |
| An algorithm/problem pair to study | [Analysis](../ECTheoryLib/Analysis/README.md) |
| A probability estimate to reuse | [Probability](../ECTheoryLib/Probability/README.md) |

For exact parameter domains, follow the linked declarations. In particular,
initial distributions, conditioning information and time units are arguments of
the results, rather than interchangeable defaults.

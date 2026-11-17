# Algorithm models

These modules define initialization, transition kernels, trajectory laws and
structural invariants. Runtime conclusions belong in the linked analysis layer.
Comparisons are passed as **candidate-to-parent** relations; weak elitism accepts
ties. Every analysis fixes the direction and the initial law it needs.

| Family / entry | Formalized variant | Current result level and case |
| --- | --- | --- |
| [RLS](RLS.lean) | One uniformly chosen bit flip, supplied acceptance rule; uniform default initialization or explicit PMF | Model and preservation laws; exact [OneMax](../Analysis/OneMax/RLS/ExactRuntime.lean) and uniformly initialized [LeadingOnes](../Analysis/LeadingOnes/RLS/ExactRuntime.lean) runtimes. |
| [Standard (1+1) EA](OnePlusOneEA.lean) | Independent mutation 1/n, supplied acceptance rule, uniform default or explicit PMF | Model and preservation laws; [positive-linear minimization](../Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean) and other specified cases. |
| [Multi-valued RLS](MultivalRLS.lean) | Uniform coordinate and a uniform different alphabet value, supplied acceptance | Model and [Hamming/OneMax runtime analysis](../Analysis/MultivalOneMax/RLS/ExactRuntime.lean). |
| [Fixed-size RLS](FixedSizeRLS.lean), [coordinate search](CoordinateSearch.lean) | k distinct flips, or a supplied state-dependent coordinate policy | Kernel identities and selected [OneMax analyses](../Analysis/OneMax/); no all-policy runtime claim. |
| [Random search](RandomSearch.lean) | Replace by an independent fresh sample, without selection or freezing at success | Model and [exact geometric runtime analyses](../Analysis/RandomSearch/ExactRuntime.lean) at the stated positive-success conditions. |
| [Archive search](ArchiveSearch.lean), [SEMO](SEMO.lean), [GSEMO](GSEMO.lean) | Generic supplied parent/mutation policies; SEMO/GSEMO use uniform archive parents and respectively one-bit/standard bit mutation, with tie-replacing Pareto archive update | Models and invariants; selected [OneMinMax](../Analysis/OneMinMax/) and [LOTZ](../Analysis/LOTZ/) runtime results with their own initialization and parameter conditions. |
| [NSGA-II](NSGAII.lean) | Uniform parent occurrences, no crossover, independent offspring, classical crowding distance and randomized positional ties | Model and size invariants; specified [OneMinMax case](../Analysis/OneMinMax/NSGAII/RuntimeBounds.lean), not general NSGA-II runtime theory. |
| [NSGA-III](NSGAIII.lean) | Uniform reproduction without crossover; revised normalization history and reference niching | Kernel/state and structural properties; a general runtime bound is not asserted. |
| [SMS-EMOA](SMSEMOA.lean) | Uniform parent occurrence, standard mutation, randomized minimum hypervolume-contribution deletion | Model and structural properties; no general runtime bound is asserted. |
| [SPEA2](SPEA2.lean) | Separate population/archive, strength/density/truncation and binary tournaments; no crossover | Model and structural properties; no general runtime bound is asserted. |

[Population](Population.lean), [fixed-population](FixedPopulation.lean) and
[sampling](PopulationSampling.lean) modules supply shared representations and
probability identities. Lists preserve occurrences and duplicates; uniform parent
sampling is by occurrence rather than by distinct genotype. Generational models
count generations; the one-offspring models count updates. Evaluations require
the corresponding cost convention.

Use the [complete file index](../../docs/CONTENTS.md#algorithms) for all modules,
including the shortcut RLS kernel. The [textbook map](../../docs/COVERAGE.md)
separately states which source examples have runtime conclusions.

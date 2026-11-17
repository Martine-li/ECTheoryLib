# Textbook coverage

This is the current public map for the 2020 Springer edition of *Theory of
Evolutionary Computation: Recent Developments in Discrete Optimization*.
Chapter 2 (Johannes Lengler, *Drift Analysis*, pp. 89–131) is the main construction
line; Chapter 1 (Benjamin Doerr, *Probabilistic Tools for the Analysis of
Randomized Optimization Heuristics*, pp. 1–87) supplies a substantial probability
toolkit. Bibliographic details and attribution are in [SOURCES](SOURCES.md).

Use the source numbers below to find code; use the [content guide](CONTENTS.md)
to browse by mathematical task. This map describes this release, not the latest
development branch. Earlier coverage ledgers remain historical records in the
development archive and are not competing current maps.

**Implementation** records whether the indicated result is proved, partly proved
or not implemented. **Source relation** separately records original conclusions,
explicit conventions, restricted scope or revised statements. “Proved” refers to
the stated Lean interface, including its hypotheses. A different proof route does
not reduce completion of the same conclusion. We use no whole-chapter completion
percentage: a row can contain several conclusions and variants.

The conditioning distinctions and substantive source comparisons are collected
once in [SOURCE_NOTES](SOURCE_NOTES.md). Mathlib reuse counts as usable coverage
and is attributed to Mathlib, not as a new proof by this library.

## Chapter 2: ten main theorems

### 2.3.1 — Additive drift

**Implementation:** Proved (stated interfaces). **Source relation:** Restricted version / explicit conventions.

Upper and lower bounds by the initial expected potential divided by a positive drift constant.

**Lean:** [`ECTheoryLib.Tools.Drift.AdditiveDriftUpperBound`](../ECTheoryLib/Tools/Drift/Additive.lean#L70); [`ECTheoryLib.Tools.Drift.AdditiveDriftLowerBound`](../ECTheoryLib/Tools/Drift/Additive.lean#L138); [`ECTheoryLib.Tools.Drift.AdditiveDriftUpperBoundOfSurvivingStateDrift`](../ECTheoryLib/Tools/Drift/NonabsorbingAdditive.lean#L91); [`ECTheoryLib.Tools.Drift.AdditiveDriftLowerBoundOfSurvivingStateDrift`](../ECTheoryLib/Tools/Drift/NonabsorbingAdditive.lean#L132)

The raw-level interfaces require absorption at zero. Nonabsorbing interfaces use full history or explicitly condition on survival **and** the current level; those hypotheses differ. A common finite nonnegative range is retained. Random initialization, initial success and infinite hitting times are represented. The bare raw-level hypothesis without absorption does not suffice; see [conditioning notes](SOURCE_NOTES.md#conditioning).

### 2.3.3 — Variable drift, upper bound

**Implementation:** Proved (stated interfaces). **Source relation:** Restricted version / explicit conventions.

Bounds the mean hitting time using the reciprocal integral of a positive nondecreasing drift function.

**Lean:** [`ECTheoryLib.Tools.Drift.VariableDriftUpperBound`](../ECTheoryLib/Tools/Drift/Variable.lean#L162); [`ECTheoryLib.Tools.Drift.VariableDriftUpperBoundOfPositiveInitial`](../ECTheoryLib/Tools/Drift/Variable.lean#L192); [`ECTheoryLib.Tools.Drift.VariableDriftUpperBoundOfSurvivingStateDrift`](../ECTheoryLib/Tools/Drift/NonabsorbingVariable.lean#L95)

Common finite nonnegative range and a positive minimum level; positivity and `MonotoneOn` for the drift function. Raw-level conditioning requires absorption; the surviving-level and full-history versions allow a nonabsorbing original process. The displayed integral form assumes positive initial potential; the general potential is zero at initial success.

### 2.3.11 — Multiplicative drift, upper bound

**Implementation:** Proved (stated interfaces). **Source relation:** Restricted version / explicit conventions.

A drift of at least δ times the current potential gives a logarithmic mean hitting-time bound.

**Lean:** [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperBound`](../ECTheoryLib/Tools/Drift/Multiplicative.lean#L57); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperBoundOfPositiveInitial`](../ECTheoryLib/Tools/Drift/Multiplicative.lean#L90); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperBoundOfSurvivingStateDrift`](../ECTheoryLib/Tools/Drift/NonabsorbingMultiplicative.lean#L76)

Positive δ, common finite nonnegative range and a positive gap above zero. The same conditioning distinction as 2.3.1 applies. The logarithmic display assumes positive initialization; the general result includes an atom at zero.

### 2.4.1 — Variable drift, lower bound

**Implementation:** Proved (stated interfaces). **Source relation:** Explicit conventions / restricted version.

A nonincreasing process, an upper drift function and a bound on adjacent drift-function ratios yield an integral lower bound.

**Lean:** [`ECTheoryLib.Tools.Drift.VariableDriftLowerBound`](../ECTheoryLib/Tools/Drift/VariableLower.lean#L75); [`ECTheoryLib.Tools.Drift.VariableDriftLowerBoundOfPositiveInitial`](../ECTheoryLib/Tools/Drift/VariableLower.lean#L117); [`ECTheoryLib.Tools.Drift.VariableDriftLowerBoundNonabsorbing`](../ECTheoryLib/Tools/Drift/NonabsorbingVariableLower.lean#L20)

Common finite range; positive drift function and ratio constant. The nonabsorbing interface restricts nonincrease and drift to active positive states and uses full history. The display assumes positive initialization; the zero-safe interface allows initial success and infinite mean.

### 2.4.2 — Variable drift with a jump floor

**Implementation:** Proved. **Source relation:** Original conclusion / explicit conventions.

A floor ξ on the next level and a history-conditional drift bound at ξ give the reciprocal-integral lower bound.

**Lean:** [`ECTheoryLib.Tools.Drift.VariableDriftLowerBoundOfJumpFloorCondExp`](../ECTheoryLib/Tools/Drift/VariableJumpLower.lean#L156); [`ECTheoryLib.Tools.Drift.VariableDriftLowerBoundOfJumpFloorNonabsorbing`](../ECTheoryLib/Tools/Drift/NonabsorbingVariableJumpLower.lean#L19)

Nonincrease before the hit, a nonnegative jump floor on reachable positive levels, and a positive drift function including its value at zero. Initial zero mass is retained. The nonabsorbing version only constrains the process before the first hit.

### 2.4.3 — Multiplicative drift, lower bound

**Implementation:** Proved (stated interfaces). **Source relation:** Explicit conventions / restricted version.

An upper multiplicative drift and control of large relative jumps give a logarithmic lower bound with the factor (1−β)/(1+β).

**Lean:** [`ECTheoryLib.Tools.Drift.MultiplicativeDriftLowerBound`](../ECTheoryLib/Tools/Drift/MultiplicativeLower.lean#L195); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftLowerBoundOfCondExp`](../ECTheoryLib/Tools/Drift/MultiplicativeLower.lean#L327); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftLowerBoundNonabsorbing`](../ECTheoryLib/Tools/Drift/NonabsorbingMultiplicativeLower.lean#L19); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftLowerBoundOfReferenceLevels`](../ECTheoryLib/Tools/Drift/Multiplicative/PositivePartLower.lean#L305)

Full-history conditioning, nonincrease on active positive states, positive drift scale and the stated large-jump bound are essential. The reference-level/positive-part extension is a separate interface for the discussion after (2.13). Zero-safe and positive-initial displays have different domains; β endpoints are handled explicitly.

### 2.4.5 — Multiplicative drift, upper tail

**Implementation:** Proved (stated interfaces). **Source relation:** Restricted version / explicit conventions.

For fixed positive s₀, the tail after ceil((r+log(s₀/s_min))/δ) updates is at most exp(−r).

**Lean:** [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperTail`](../ECTheoryLib/Tools/Drift/MultiplicativeTail.lean#L173); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperTailNonabsorbing`](../ECTheoryLib/Tools/Drift/NonabsorbingMultiplicativeTail.lean#L47); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperTailOfSurvivingStateDrift`](../ECTheoryLib/Tools/Drift/SurvivingStateMultiplicativeTail.lean#L20); [`ECTheoryLib.Tools.Drift.MultiplicativeDriftUpperTailOfIntegrableStoppedLevel`](../ECTheoryLib/Tools/Drift/IntegrableMultiplicativeTail.lean#L122)

Here r≥0 and δ,s_min>0. Raw-level conditioning requires absorption. The full-history and surviving-level interfaces avoid that requirement. A further proved interface replaces a common finite range by integrability of every stopped level; it still requires a positive gap. Its hypotheses should be read as a separate variant, not as validation of the bare printed raw-level condition.

### 2.4.7 — Additive drift, tails

**Implementation:** Proved (replacement bounds); printed constants not reproduced. **Source relation:** Revised version.

Both upper and lower hitting-time tails are proved with explicit geometric-jump constants. A bounded-jump upper-tail interface is also available.

**Lean:** [`ECTheoryLib.Tools.Drift.GeometricAdditiveDriftUpperTailOfCondExp`](../ECTheoryLib/Tools/Drift/GeometricAdditiveTail.lean#L25); [`ECTheoryLib.Tools.Drift.GeometricAdditiveDriftLowerTailOfCondExp`](../ECTheoryLib/Tools/Drift/GeometricAdditiveLowerTail.lean#L23); [`ECTheoryLib.Tools.Drift.GeometricAdditiveDriftLowerTailOfStrictJumpTail`](../ECTheoryLib/Tools/Drift/GeometricAdditiveLowerTail.lean#L266)

Common finite real range, fixed s₀>a, full-history drift on active states, η>0 and r≥1. The two directions use opposite drift inequalities. The closed integer jump-tail interface includes k=0; converting a strict jump tail changes the envelope constant. Lower tails require t>0 and δt≤s₀−a. The proved q/M constants replace the printed formula; see [source notes and a finite counterexample](SOURCE_NOTES.md#additive-tails).

### 2.4.8 — General exponential drift, tails

**Implementation:** Proved (replacement bounds); printed statement not reproduced verbatim. **Source relation:** Revised version.

Exponential conditional-moment certificates give upper tails and lower hitting-time tails at a real target.

**Lean:** [`ECTheoryLib.Tools.Drift.GeneralExponentialDriftUpperTailOfCondExp`](../ECTheoryLib/Tools/Drift/GeneralExponentialUpperTail.lean#L19); [`ECTheoryLib.Tools.Drift.StrictGeneralExponentialDriftUpperTailOfFixedInitial`](../ECTheoryLib/Tools/Drift/GeneralExponentialUpperTail.lean#L58); [`ECTheoryLib.Tools.Drift.ExponentialDriftLowerTailProductOfFixedInitial`](../ECTheoryLib/Tools/Drift/GeneralExponentialLowerTail.lean#L388)

Common finite real range and full history; no absorption is required of the original process. The upper bound with weak potential separation is non-strict; a strict display needs strict separation and positive parameters. Lower-tail results use an upper exponential-moment bound, control of the potential inside the target, and prefix-sum or β≥1 product hypotheses. These changes are substantive; [finite examples](SOURCE_NOTES.md#general-tails) separate them.

### 2.4.9 — Negative drift

**Implementation:** Proved (interval-local replacement); literal finite global model not used. **Source relation:** Revised version.

Drift away from a target within a barrier interval, together with geometric absolute-jump tails, makes an early crossing exponentially unlikely.

**Lean:** [`ECTheoryLib.Tools.Drift.GeometricJumpNegativeDriftTailOfActiveIncrement`](../ECTheoryLib/Tools/Drift/GeneralGeometricJumpNegative.lean#L22); [`ECTheoryLib.Tools.Drift.GeometricJumpTailEventuallyDyadic`](../ECTheoryLib/Tools/Drift/GeometricJumpAsymptotics.lean#L186)

The replacement works without a common finite range or absorption. It uses interval-local drift, localized conditional increments and the stated jump-tail envelope. The asymptotic scale is quantified separately. A finite-range process cannot sustain the printed global positive drift away from the target at every exterior state forever; see the [finite-range obstruction](SOURCE_NOTES.md#negative-drift).

## Chapter 2: twelve numbered examples

### 2.3.2 — RLS on LeadingOnes

**Implementation:** Proved (exact expectation). **Source relation:** Original conclusion / explicit conventions.

The exact mean under uniform initialization is n²/2 updates, for n>0.

**Lean:** [`ECTheoryLib.Analysis.RLSOnLeadingOnes.UniformRuntimeExact`](../ECTheoryLib/Analysis/LeadingOnes/RLS/ExactRuntime.lean#L23); [`ECTheoryLib.Analysis.RLSOnLeadingOnes.UniformRuntimeExactReal`](../ECTheoryLib/Analysis/LeadingOnes/RLS/ExactRuntime.lean#L85)

RLS flips one uniformly chosen bit and accepts non-worsening moves, including neutral ones. The initialization is the actual uniform bit-string law `RLSInit n`. Conditional level laws and suffix symmetry support the calculation; this is not a fixed-state n²/2 claim.

### 2.3.4 — Coupon collector and RLS–OneMax

**Implementation:** Proved. **Source relation:** Original conclusion / explicit conventions.

Uniform coupon collection has exact expectation nHₙ; RLS–OneMax from a fixed state with k zeros has exact expectation nH_k.

**Lean:** [`ECTheoryLib.Analysis.CouponCollector.ExpectedDrawsExact`](../ECTheoryLib/Analysis/CouponCollector/ExactRuntime.lean#L56); [`ECTheoryLib.Analysis.CouponCollector.ExpectedDrawsAsymptotic`](../ECTheoryLib/Analysis/CouponCollector/ExactRuntime.lean#L87); [`ECTheoryLib.Analysis.RLSOnOneMax.FixedRuntimeExact`](../ECTheoryLib/Analysis/OneMax/RLS/ExactRuntime.lean#L60)

Actual coupon-drawing and weak-elitist RLS kernels are used. The exact RLS theorem requires n>0 and includes k=0; k counts initially missing one bits. Coupon draws and RLS updates are distinct processes linked by their analyses.

### 2.3.5 — Genetic programming

**Implementation:** Not implemented. **Source relation:** No corresponding result.

The tree-based model and the runtime analysis in this example are not in this release.

**Lean:** No corresponding library theorem in this release.

The existing bit-string algorithms do not instantiate this example.

### 2.3.6 — RLS with shortcuts

**Implementation:** Proved (runtime order and bound comparison). **Source relation:** Original conclusion / explicit conventions.

The uniform-initialization runtime is Θ(n), while the displayed drift bound overestimates it by a Θ(log n) factor.

**Lean:** [`ECTheoryLib.Analysis.RLSWithShortcuts.UniformRuntimeFamilyIsTheta`](../ECTheoryLib/Analysis/OneMax/RLSWithShortcuts/RuntimeLowerBounds.lean#L145); [`ECTheoryLib.Analysis.RLSWithShortcuts.UniformBoundRuntimeRatioFamilyIsTheta`](../ECTheoryLib/Analysis/OneMax/RLSWithShortcuts/RuntimeLowerBounds.lean#L204)

One update jumps to the prescribed all-false optimum with probability 1/n; otherwise it performs a complete ordinary weak-minimizing RLS step. Finite-size bounds and the one-bit starting case are proved separately. The analysis fixes the source boundary conventions rather than dropping the ordinary branch.

### 2.3.7 — RLS on BinVal

**Implementation:** Partly proved as a full example; drift and runtime conclusions proved. **Source relation:** Original conclusions for listed results / explicit conventions.

Fitness and one-count drift, zero-safe variable/multiplicative upper bounds, rescaling comparisons and fixed-time conditional laws are available. The positive-weight RLS theorem also gives exact fixed-state mean nH_k for this kernel, where k is the initial one-count.

**Lean:** [`ECTheoryLib.Analysis.RLSBinVal.FitnessVariableUpperBound`](../ECTheoryLib/Analysis/Linear/RLS/BinVal.lean#L143); [`ECTheoryLib.Analysis.RLSBinVal.CountVariableUpperBound`](../ECTheoryLib/Analysis/Linear/RLS/BinVal.lean#L154); [`ECTheoryLib.Analysis.RLSBinVal.CountConditionalDrift`](../ECTheoryLib/Analysis/Linear/RLS/BinVal.lean#L59); [`ECTheoryLib.Analysis.RLSLinear.FixedRuntimeExact`](../ECTheoryLib/Analysis/Linear/RLS/PositiveWeights.lean#L171)

The actual weak-minimizing RLS kernel is used; specialize the exact theorem to `Problems.Linear.BinVal.Weights` and `WeightPositive`. A quadratic upper-bound expression is not a quadratic lower bound on the actual runtime. The remaining source-exposition gap concerns the random last surviving bit at its stopping time; fixed-time laws do not prove that statement. It is not a gap in the mean-runtime conclusion.

### 2.3.8 — Random decline

**Implementation:** Partly proved. **Source relation:** Restricted version / explicit boundary conventions.

The finite truncated kernel has multiplicative count-drift bounds and logarithmic-potential runtime upper bounds.

**Lean:** [`ECTheoryLib.Analysis.RandomDecline.FixedMultiplicativeRuntimeUpper`](../ECTheoryLib/Analysis/RandomDecline/RuntimeBounds.lean#L78); [`ECTheoryLib.Analysis.RandomDecline.FixedLogarithmicRuntimeUpper`](../ECTheoryLib/Analysis/RandomDecline/RuntimeBounds.lean#L113)

The count bound uses 0<a<2; the logarithmic argument uses 0<a<e and a potential zero at success. The a≥e regime, the source choice of N(n), and matching lower/tightness statements remain open here.

### 2.3.9 — (1+λ) EA on OneMax

**Implementation:** Not implemented. **Source relation:** No corresponding result.

The six-regime variable-drift analysis and the population-size-dependent runtime conclusion are not formalized.

**Lean:** No corresponding library theorem in this release.

The standard (1+1) EA file does not supply this population result.

### 2.3.10 — Island model on OneMax

**Implementation:** Not implemented. **Source relation:** No corresponding result.

The synchronized migration model and its phase-dependent runtime analysis are not formalized.

**Lean:** No corresponding library theorem in this release.

Independent-run tools do not by themselves establish the migration theorem.

### 2.3.12 — (1+1) EA on linear functions

**Implementation:** Partly proved as a whole example; positive-weight runtime conclusion proved. **Source relation:** Original positive-weight conclusion / restricted overall scope.

For every strictly positive real weight vector and every initial PMF, the standard weak-minimizing (1+1) EA satisfies E[T]≤4en(1+log(2n)). Uniform-initialization lower bounds and asymptotic interfaces are also available.

**Lean:** [`ECTheoryLib.Analysis.EALinearMinimization.RankRuntimeUpperBound`](../ECTheoryLib/Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean#L100); [`ECTheoryLib.Analysis.EALinearMinimization.UniformRankRuntimeBounds`](../ECTheoryLib/Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean#L130)

Here n>0 and independent mutation uses probability 1/n per bit. Weights may repeat and need not be sorted. A rank potential proves the O(n log n) conclusion for this class; choosing this proof does not make that conclusion incomplete. This release does not include a signed-weight normalization theorem, the source coupling argument for unweighted OneMax potential, all other illustrated potentials, or the general c/n and sharp-leading-constant results.

### 2.3.13 — Minimum spanning trees

**Implementation:** Not implemented. **Source relation:** No corresponding result.

The graph encoding, tree-preserving analysis and displayed MST runtime bound are not formalized.

**Lean:** No corresponding library theorem in this release.

Generic multiplicative drift is available, but the required MST model and local inequalities are not.

### 2.4.4 — Jump-floor lower bound for RLS–OneMax

**Implementation:** Proved. **Source relation:** Original conclusion / explicit conventions.

The jump-floor theorem yields the displayed logarithmic lower bound; the same kernel also has exact expectation nH_k.

**Lean:** [`ECTheoryLib.Analysis.RLSOnOneMax.FixedRuntimeJumpLowerBound`](../ECTheoryLib/Analysis/OneMax/RLS/RuntimeJumpLowerBounds.lean#L94); [`ECTheoryLib.Analysis.RLSOnOneMax.FixedRuntimeExact`](../ECTheoryLib/Analysis/OneMax/RLS/ExactRuntime.lean#L60)

Weak-elitist RLS, n>0, fixed initial state; the displayed lower bound requires k>0. Initial success is handled by the exact/zero-safe interfaces rather than by a logarithm at zero.

### 2.4.6 — A weak-drift walk with an atypical mean

**Implementation:** Proved for the stated completed kernel. **Source relation:** Revised mean / explicit boundary convention.

Starting at n with drift 1/n⁴ gives exact mean n⁵, and an O(n³) high-probability hitting-time bound is proved.

**Lean:** [`ECTheoryLib.Analysis.FiniteBiasedWalk.WeakDriftExpectedRuntime`](../ECTheoryLib/Analysis/RandomWalk/WeakDriftRuntime.lean#L40); [`ECTheoryLib.Analysis.FiniteBiasedWalk.WeakDriftCubicTailRealSqrt`](../ECTheoryLib/Analysis/RandomWalk/WeakDriftTail.lean#L138); [`ECTheoryLib.Analysis.FiniteBiasedWalk.WeakDriftCubicHighProbability`](../ECTheoryLib/Analysis/RandomWalk/WeakDriftTail.lean#L155)

The finite walk is absorbing at zero. At its upper boundary N it moves down with probability 1/n⁴ and otherwise holds, preserving the drift. The exact mean needs n>0 and N≥n; the tail uses n≥2 and N≥n⌊√n⌋. The printed mean n⁴ is replaced by n⁵. The library proves the tail by its own argument; it does not reproduce every coupling step in the text.

## Chapter 2: unnumbered constructions and discussions

### §2.2 — Processes, conditioning and time

**Implementation:** Proved (infrastructure). **Source relation:** Explicit conventions.

Transitions generate infinite path laws; hitting time includes time zero and nontermination. Separate interfaces expose the conditioning information used by drift theorems.

**Lean:** [`ECTheoryLib.Probability.FirstHittingTime`](../ECTheoryLib/Probability/HittingTimes/HittingTime.lean#L17); [`ECTheoryLib.Probability.ExpectedHittingTime`](../ECTheoryLib/Probability/HittingTimes/Expectation.lean#L49); [`ECTheoryLib.Tools.Runtime.ExpectedEvaluationCostEq`](../ECTheoryLib/Tools/Runtime/Cost.lean#L29)

The headline algorithm results count completed updates after initialization. Fixed evaluation costs are `initial cost + per-step cost × T` on the same path law; early stopping inside a generation and random evaluation costs need another model. Raw-level, surviving-level and full-history assumptions must not be interchanged.

### §2.5 — Constructing a potential

**Implementation:** Proved (canonical remaining-time construction); discussion partly implemented. **Source relation:** Original construction / explicit conventions.

Conditional expected remaining time defines a potential with unit drift before the stopping time and the intended first-zero/initial-mean properties.

**Lean:** [`ECTheoryLib.Tools.Drift.CanonicalRemainingPotentialDrift`](../ECTheoryLib/Tools/Drift/Potential/Canonical.lean#L110); [`ECTheoryLib.Tools.Drift.CanonicalRemainingPotentialFirstZero`](../ECTheoryLib/Tools/Drift/Potential/Canonical.lean#L273); [`ECTheoryLib.Tools.Drift.CanonicalRemainingPotentialInitialMean`](../ECTheoryLib/Tools/Drift/Potential/Canonical.lean#L164)

An adapted stopping-time setting with finite expected stopping time is required; no finite-state or bounded-time assumption is added. The expression E[T|F_t]−t describes the pre-hit potential. The chapter’s broader heuristics are illustrated by harmonic, logarithmic and rank potentials, rather than implemented as an automatic construction procedure.

### §2.4.4 — Population drift discussion

**Implementation:** Partly proved (models and sampling tools); level-based theorem not implemented. **Source relation:** Selected components.

Population, fixed-population and sampling definitions, negative-dependence tools and several concrete archive/population analyses are present.

**Lean:** [`ECTheoryLib.Probability.UniformSubsetUnion.IndependentUniformSubsetsNegativelyCorrelated`](../ECTheoryLib/Probability/Sampling/UniformSubsetUnion.lean#L33)

See the [algorithm guide](../ECTheoryLib/Algorithms/README.md) for the variant and completion level of each family. These components are not a formalization of a general population level-based theorem or of all crossover/population dynamics in the discussion.

## Chapter 1: available probability tools

The table groups closely related source items to keep the entry points usable.
Each linked module contains the exact hypotheses and, where applicable, stronger
intermediate formulas. Direct upstream calls have a runnable client or a concrete
library application. Distribution examples are checked separately from `lake build`.

| Source | Content | Implementation | Source relation | Lean entry / reuse | Conditions and extent |
| --- | --- | --- | --- | --- | --- |
| 1.4.1 | 1+x≤exp(x) | Proved | Original conclusion | `Real.add_one_le_exp`; [Mathlib client](../Examples/ProbabilityTools.lean) | Direct Mathlib reuse for every real x; no new exponential theorem is claimed. |
| 1.4.6 | Mutation-probability exponential constants | Partly proved | Restricted version | [`ECTheoryLib.StandardOneBitProbabilityInverseBound`](../ECTheoryLib/Operators/Mutation/IndependentBitBounds.lean#L42) | An integer-length one-bit mutation constant is available; the entire family with real r,s is not mapped. |
| 1.5.1 | Finite union bound | Proved | Original conclusion | `measure_biUnion_finset_le`; [Mathlib client](../Examples/ProbabilityTools.lean) | Direct Mathlib reuse; neither independence nor disjointness is required. |
| 1.6.1 | Expectation as a tail sum, including a signed extension | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.ExpectedWithTopNatEqTailSum`](../ECTheoryLib/Probability/HittingTimes/ScalarHittingTime.lean#L105); [`ECTheoryLib.Probability.ExpectedRealLeNatUpperTailSum`](../ECTheoryLib/Probability/Moments/SignedTailSum.lean#L72) | Nonnegative integer/extended hitting times retain infinity. The signed real interface requires measurability, integrability and values almost surely in (−∞,0]∪ℕ; its positive tails start at 1. |
| 1.6.2 | Exponential tails imply mean bounds | Partly proved | Revised version / explicit conventions | [`ECTheoryLib.Probability.ExpectedWithTopNatLeOfExponentialTail`](../ECTheoryLib/Probability/Moments/ExponentialTailExpectation.lean#L131); [`ECTheoryLib.Probability.ExpectedRealLeOfContinuousExponentialTail`](../ECTheoryLib/Probability/Moments/ContinuousExponentialTailExpectation.lean#L77); [`ECTheoryLib.Probability.ExpectedRealGeOfMultiplicativeExponentialLowerTail`](../ECTheoryLib/Probability/Moments/ContinuousExponentialTailExpectation.lean#L160) | Discrete-center versions require natural centers; lower-mean versions require nonnegative variables. Continuous upper-tail and repaired nonnegative lower-tail forms are available. See SOURCE_NOTES and the expectation counterexamples; the arbitrary-real-center and signed lower-tail displays are not claimed. |
| 1.6.3 | Mean of a geometric waiting time | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.GeometricWaitingExpectation`](../ECTheoryLib/Probability/Distributions/GeometricWaiting.lean#L61); [`ECTheoryLib.Probability.GeometricWaitingExpectationOfLaw`](../ECTheoryLib/Probability/Distributions/GeometricWaiting.lean#L88) | Mathlib’s failures-before-success law is shifted by one to support {1,2,…}; p∈(0,1]. Integrability is proved from the law. |
| 1.6.4 | Linearity of expectation | Proved | Explicit conventions | `integral_finsetSum`, `integral_const_mul`; [Mathlib client](../Examples/ProbabilityTools.lean) | Finite sums of integrable variables and arbitrary real coefficients; variables may be dependent. |
| 1.6.5 | Binomial mean np | Proved | Original conclusion | [`ECTheoryLib.Probability.BinomialExpectation`](../ECTheoryLib/Probability/Distributions/BinomialExpectation.lean#L23); [`ECTheoryLib.Probability.BinomialNatExpectationOfLaw`](../ECTheoryLib/Probability/Distributions/BinomialExpectation.lean#L74) | Bridges Mathlib’s binomial integral/mass identities to distribution-law clients and proves integrability; n=0 and p=0,1 are included. |
| 1.6.6 | Mutation and crossover Hamming means | Proved | Original numbered formulas / explicit conventions | [`ECTheoryLib.Analysis.BitMutation.MutationHammingExpectation`](../ECTheoryLib/Analysis/BitMutationConcentration.lean#L38); [`ECTheoryLib.Analysis.Crossover.UniformCrossoverHammingExpectation`](../ECTheoryLib/Analysis/Crossover/UniformExpectation.lean#L23); [`ECTheoryLib.Analysis.Crossover.SinglePointHammingExpectation`](../ECTheoryLib/Analysis/Crossover/SinglePointExpectation.lean#L22) | Actual independent-bit mutation for any target and p∈[0,1]; uniform crossover and the library’s symmetric single-point crossover law. All cut positions are included; standard mutation requires n>0. A source prose issue does not alter the displayed mean formulas. |
| 1.6.7–1.6.8 | Markov and the first-moment method | Proved | Explicit conventions | `mul_meas_ge_le_integral_of_nonneg`, `mul_meas_ge_le_lintegral₀`; [Mathlib client](../Examples/ProbabilityTools.lean) | Positive threshold and nonnegative variable; the normalized display needs positive mean. The nonnegative extended integral allows infinite mean. |
| 1.6.9 | Chebyshev’s inequality | Proved | Explicit conventions | `ProbabilityTheory.meas_ge_le_variance_div_sq`; [a library application](../ECTheoryLib/Analysis/MultivalOneMax/RLS/InitializationConcentration.lean) | Direct Mathlib reuse under a finite second moment (`MemLp 2`); a positive deviation. Normalization by variance requires positive variance. |
| 1.6.10 | Cantelli’s one-sided variance bounds | Proved | Explicit conventions | [`ECTheoryLib.Probability.CantelliUpperTail`](../ECTheoryLib/Probability/Concentration/Cantelli.lean#L65); [`ECTheoryLib.Probability.CantelliLowerTail`](../ECTheoryLib/Probability/Concentration/Cantelli.lean#L85) | Finite second moments; positive deviation. The raw form permits zero variance; standardized forms require positive variance. |
| 1.6.11 | The second-moment method | Partly proved | Revised version / explicit conventions | [`ECTheoryLib.Probability.ZeroProbabilitySecondMoment`](../ECTheoryLib/Probability/Concentration/SecondMoment.lean#L27); [`ECTheoryLib.Probability.NonpositiveProbabilityOfPositiveMean`](../ECTheoryLib/Probability/Concentration/SecondMoment.lean#L62) | Zero/nonzero events use nonzero mean; a nonpositive-event bound additionally needs positive mean. Finite second moments are explicit; the omitted sign condition cannot be inferred from a nonzero mean. |
| 1.7.1 | Total probability and expectation | Proved | Explicit conventions | [`ECTheoryLib.Probability.FinitePartitionTotalProbability`](../ECTheoryLib/Probability/Conditioning/FiniteConditioning.lean#L69); [`ECTheoryLib.Probability.FinitePartitionTotalExpectation`](../ECTheoryLib/Probability/Conditioning/FiniteConditioning.lean#L83) | Bridges Mathlib conditional measures (`sum_meas_smul_cond_fiber`) to finite measurable partitions on an arbitrary space; signed integrable variables and zero-mass blocks are included. |
| 1.7.2 | Conditioning away a rare event | Proved | Explicit conventions | [`ECTheoryLib.Probability.ConditionalEventBounds`](../ECTheoryLib/Probability/Conditioning/RareEventConditioning.lean#L27); [`ECTheoryLib.Probability.ConditionalEventAdditiveBounds`](../ECTheoryLib/Probability/Conditioning/RareEventConditioning.lean#L50) | The retained event has positive probability. Both directions and the additive constant 2 for removed mass at most 1/2 are retained; independence is not assumed after conditioning. |
| 1.7.3 | Conditional binomial means | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.ConditionalBinomialExpectationBounds`](../ECTheoryLib/Probability/Distributions/ConditionalBinomialExpectation.lean#L94) | E[X\|X≥k]≤k+(n−k)p≤k+E[X], with a positive conditioning event and integrability derived from the law. p=0 is valid only for the appropriate nonempty event. |
| 1.8.1 | Stochastic domination and CDF order | Proved | Original conclusion | [`ECTheoryLib.Probability.StochasticDominated`](../ECTheoryLib/Probability/StochasticOrder/StochasticDomination.lean#L29); [`ECTheoryLib.Probability.StochasticDominatedIffCDF`](../ECTheoryLib/Probability/StochasticOrder/StochasticDomination.lean#L160) | Uses probability laws, with measurable-variable bridges; variables may be on different sample spaces and have atoms. |
| 1.8.2–1.8.3 | Monotone expectations and mean order | Proved | Explicit conventions | [`ECTheoryLib.Probability.StochasticDominatedIffMonotoneIntegrals`](../ECTheoryLib/Probability/StochasticOrder/StochasticMonotone.lean#L83); [`ECTheoryLib.Probability.StochasticDominatedExpectationLE`](../ECTheoryLib/Probability/StochasticOrder/StochasticExpectation.lean#L120) | Transformed real variables are integrable; the nonnegative extended-integral interfaces permit infinity. Continuity or strict monotonicity of the transformation is not required. |
| 1.8.4–1.8.5 | Independent sums, pointwise order and equal laws | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.StochasticDominatedIndependentSum`](../ECTheoryLib/Probability/StochasticOrder/StochasticSum.lean#L75); [`ECTheoryLib.Probability.StochasticDominatedOfAELe`](../ECTheoryLib/Probability/StochasticOrder/StochasticDomination.lean#L79); [`ECTheoryLib.Probability.StochasticDominatedOfIdentDistrib`](../ECTheoryLib/Probability/StochasticOrder/StochasticDomination.lean#L53) | Mathlib convolution/independent-sum laws are reused. Each reference family is internally independent; cross-family independence and finite means are not required. Pointwise order has an almost-everywhere interface. |
| 1.8.6 | Fitness-level geometric domination | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Tools.Runtime.FitnessLevelsOfPastEventSuccess`](../ECTheoryLib/Tools/Runtime/FitnessLevelsFromHistory.lean#L61); [`ECTheoryLib.Tools.Runtime.PathFitnessLevelsGeometricBound`](../ECTheoryLib/Tools/Runtime/FitnessLevelsFromHistory.lean#L93) | Success bounds hold on every past-measurable event for an adapted process. Positive level probabilities, geometric waiting times starting at 1, skipped stages and infinite times are handled; stages need not be independent. |
| 1.8.7 | History-conditional binary sums | Proved | Explicit conventions | [`ECTheoryLib.Probability.BinarySequentialSumUpper`](../ECTheoryLib/Probability/StochasticOrder/BinarySequentialSum.lean#L45); [`ECTheoryLib.Probability.BinarySequentialSumLower`](../ECTheoryLib/Probability/StochasticOrder/BinarySequentialSum.lean#L74) | Full positive-probability binary histories; the actual variables may be dependent, while the reference family is independent and need not be identically distributed. |
| 1.8.8 | Sequential sums under conditional domination | Proved | Explicit conventions | [`ECTheoryLib.Probability.StochasticDominatedFiniteSequentialSum`](../ECTheoryLib/Probability/StochasticOrder/SequentialSum.lean#L263); [`ECTheoryLib.Probability.StochasticDominatedFiniteSequentialSumLower`](../ECTheoryLib/Probability/StochasticOrder/SequentialSum.lean#L297) | Countably supported real actual variables and full positive-probability prefixes. Extended-natural interfaces also retain infinity; no finite-mean premise is imposed. |
| 1.8.9 | Binomial and geometric law comparisons | Partly proved as printed; all corrected comparisons proved | Revised geometric direction / explicit conventions | [`ECTheoryLib.Probability.BinomialStochasticDominated`](../ECTheoryLib/Probability/Distributions/BinomialDomination.lean#L135); [`ECTheoryLib.Probability.ConditionalBinomialBounds`](../ECTheoryLib/Probability/Distributions/BinomialConditioning.lean#L133); [`ECTheoryLib.Probability.GeometricWaitingStochasticAntitone`](../ECTheoryLib/Probability/Distributions/GeometricDomination.lean#L60) | Binomial endpoints and zero trials are included. Conditional events must have positive mass. Geometric waiting times are antitone in success probability; this reverses the printed direction of part (d). |
| 1.8.10 | Ordered couplings | Proved | Original conclusion | [`ECTheoryLib.Probability.StochasticDominatedIffExistsOrderedCoupling`](../ECTheoryLib/Probability/StochasticOrder/OrderedCoupling.lean#L28); [`ECTheoryLib.Probability.ExistsOrderedCouplingOfStochasticDominated`](../ECTheoryLib/Probability/StochasticOrder/OrderedCoupling.lean#L43) | Real probability laws, atoms and unbounded supports are allowed. The quantile construction on the open unit interval requires no finite mean. |
| 1.8.12 | Mutation preserves OneMax stochastic order | Proved | Original conclusion | [`ECTheoryLib.Analysis.OneMaxMutation.MutationOneMaxStochasticMonotone`](../ECTheoryLib/Analysis/OneMax/MutationDomination.lean#L90) | Arbitrary parents ordered by one-count; mutation p≤1/2 including endpoints. Standard rate 1/n therefore needs n≥2, separately from the generic statement. |
| 1.9.1 | Coupon collection: exact mean and asymptotics | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Analysis.CouponCollector.ExpectedDrawsExact`](../ECTheoryLib/Analysis/CouponCollector/ExactRuntime.lean#L56); [`ECTheoryLib.Analysis.CouponCollector.ExpectedDrawsAsymptotic`](../ECTheoryLib/Analysis/CouponCollector/ExactRuntime.lean#L87) | Actual uniform draws with replacement. The exact nHₙ formula includes the empty collection n=0; the ratio to n log n is a separate limit as n tends to infinity. |
| 1.9.2 | Coupon-collector upper tails | Partly proved as printed; corrected endpoints proved | Revised version | [`ECTheoryLib.Analysis.CouponCollector.AdditiveUpperTailCeiling`](../ECTheoryLib/Analysis/CouponCollector/TailBounds.lean#L27); [`ECTheoryLib.Analysis.CouponCollector.MultiplicativeUpperTailCeiling`](../ECTheoryLib/Analysis/CouponCollector/TailBounds.lean#L41) | For n>0 and nonnegative deviation, strict/rounded natural thresholds preserve the integer waiting-time event. The literal closed real-threshold endpoint is not silently substituted. |
| 1.9.3 | Coupon-collector lower tails | Proved (floor interfaces) | Explicit conventions | [`ECTheoryLib.Analysis.CouponCollector.AdditiveLowerTailFloor`](../ECTheoryLib/Analysis/CouponCollector/LowerTail.lean#L104); [`ECTheoryLib.Analysis.CouponCollector.MultiplicativeLowerTailFloor`](../ECTheoryLib/Analysis/CouponCollector/LowerTail.lean#L124) | For n>0 the floor interfaces allow arbitrary real deviations. Their integer events and the separate real-threshold equivalence retain endpoint and nontermination conventions. |
| 1.9.4 | Universal EA lower tail | Proved (corrected evaluation bound) | Revised version | [`ECTheoryLib.Analysis.UniversalEA.UniformRuntimePowerLowerTail`](../ECTheoryLib/Analysis/OnePlusOneEA/UniversalLowerTail.lean#L33); [`ECTheoryLib.Analysis.UniversalEA.CorrectedEvaluationLowerTail`](../ECTheoryLib/Analysis/OnePlusOneEA/UniversalLowerTail.lean#L145) | Uniform initialization, standard bit mutation, weak maximization and a specified unique optimum. The evaluation version charges initialization, assumes n≥2 and uses the corrected (n/2)^ε factor. Update and evaluation events are distinct. |
| 1.10.1 | Multiplicative Chernoff upper tails | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.UnitIndependentSumFiniteChernoffUpper`](../ECTheoryLib/Probability/Concentration/FiniteChernoff.lean#L237); [`ECTheoryLib.Probability.FiniteChernoffUpperBoundLeExp`](../ECTheoryLib/Probability/Concentration/FiniteChernoff.lean#L306) | Independent finite [0,1] families on a probability space; actual mean, all displayed comparison forms, empty sums and zero-mean endpoints are included. |
| 1.10.2 | Nested-log power-tail threshold | Proved (repaired display) | Revised version | [`ECTheoryLib.Probability.PowerTailThreshold.displayedThreshold_bound_of_denominator_pos`](../ECTheoryLib/Probability/Concentration/LogarithmicThreshold.lean#L33); [`ECTheoryLib.Probability.PowerTailThreshold.repairedThreshold_bound`](../ECTheoryLib/Probability/Concentration/LogarithmicThreshold.lean#L180); [`ECTheoryLib.Probability.PowerTailThreshold.repairedThreshold_larger_bound`](../ECTheoryLib/Probability/Concentration/LogarithmicThreshold.lean#L236) | The source quotient is proved on its positive-denominator domain. At the interior singularity t=exp(e), an explicit e² threshold repairs the full original interval; Lean’s total division is not used to hide the singularity. |
| 1.10.3 | Mutation tails over one or several rounds | Proved (repaired singular input) | Revised version / explicit conventions | [`ECTheoryLib.Analysis.BitMutation.RecordedMutationMultiroundFailureThreshold`](../ECTheoryLib/Analysis/BitMutation/RecordedTailBounds.lean#L96) | Actual raw offspring at rate α/n, legal mutation probability, positive thresholds and the stated q,T domains. A same-path event union bound needs no round independence. The nested-log singular input is explicitly repaired; selected offspring are not identified with raw proposals. |
| 1.10.4 | Base-two upper tail | Proved | Original conclusion | [`ECTheoryLib.Probability.UnitIndependentSumBaseTwoUpperTail`](../ECTheoryLib/Probability/Concentration/Chernoff.lean#L184) | For k≥2eE[X], including empty/zero-mean and k=0 cases, with the closed event and any threshold atom retained. |
| 1.10.5–1.10.6 | Chernoff lower and two-sided tails | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.UnitIndependentSumFiniteChernoffLower`](../ECTheoryLib/Probability/Concentration/LowerChernoff.lean#L285); [`ECTheoryLib.Probability.UnitIndependentSumTwoSidedChernoff`](../ECTheoryLib/Probability/Concentration/TwoSidedChernoff.lean#L18) | Independent [0,1] variables, relative deviation in [0,1], closed events, mean-zero and endpoint power conventions. |
| 1.10.7–1.10.9 | Hoeffding bounds and uniform Hamming distance | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.UnitIndependentSumUpperTail`](../ECTheoryLib/Probability/Concentration/Hoeffding.lean#L120); [`ECTheoryLib.Probability.UnitIndependentSumLowerTail`](../ECTheoryLib/Probability/Concentration/Hoeffding.lean#L132); [`ECTheoryLib.Probability.BoundedIndependentSumUpperTail`](../ECTheoryLib/Probability/Concentration/Hoeffding.lean#L25); [`ECTheoryLib.Probability.BoundedIndependentSumLowerTail`](../ECTheoryLib/Probability/Concentration/Hoeffding.lean#L70); [`ECTheoryLib.Analysis.RLSHamming.UniformHammingHoeffdingDeviation`](../ECTheoryLib/Analysis/TargetOneMax/RLS/InitializationHoeffding.lean#L39) | Mathlib sub-Gaussian bounds are bridged to actual means and interval widths. Real intervals may have negative endpoints. Zero total width has a separate deterministic conclusion; uniform Hamming uses the actual RLS initialization law. |
| 1.10.10 | Additive Chernoff upper deviations | Proved (stated finite and comparison forms) | Explicit domains and boundary conventions | [`ECTheoryLib.Probability.UnitIndependentSumFiniteAdditiveChernoffUpper`](../ECTheoryLib/Probability/Concentration/FiniteAdditiveChernoff.lean#L63); [`ECTheoryLib.Probability.AdditiveChernoffPowerLeQuadratic`](../ECTheoryLib/Probability/Concentration/FiniteAdditiveChernoff.lean#L117) | For λ≥0, the finite bound has explicit branches at and beyond n−μ. The logarithmic equality needs μ>0; only the small-deviation simplification needs λ≤μ. Zero mean and empty families have explicit power/finite conventions. |
| 1.10.11 | Additive Chernoff lower deviations | Partly proved as printed; valid-domain formulas proved | Restricted / revised version | [`ECTheoryLib.Probability.UnitIndependentSumFiniteAdditiveChernoffLower`](../ECTheoryLib/Probability/Concentration/AdditiveChernoffLower.lean#L72); [`ECTheoryLib.Probability.UnitIndependentSumAdditiveChernoffLowerQuadratic`](../ECTheoryLib/Probability/Concentration/AdditiveChernoffLower.lean#L178) | The lower power chain keeps 0≤λ≤μ. Finite lower tails for λ>μ vanish; the quadratic probability bound covers every λ≥0. At zero mean its total-division display gives a weak bound rather than an undefined logarithm. |
| 1.10.12–1.10.14 | Variance-sensitive Chernoff, Bennett and scaled tails | Proved (stated positive-scale forms) | Explicit conventions | [`ECTheoryLib.Probability.IndependentSumFiniteVarianceUpper`](../ECTheoryLib/Probability/Concentration/VarianceFiniteChernoff.lean#L320); [`ECTheoryLib.Probability.IndependentSumFiniteVarianceLower`](../ECTheoryLib/Probability/Concentration/VarianceFiniteChernoff.lean#L546); [`ECTheoryLib.Probability.IndependentSumBennettUpper`](../ECTheoryLib/Probability/Concentration/Bennett.lean#L137); [`ECTheoryLib.Probability.IndependentSumFiniteVarianceUpperScaled`](../ECTheoryLib/Probability/Concentration/ScaledVarianceChernoff.lean#L25) | Complete independence, actual coordinate variance and finite second moments; one-sided centered bounds. The general scale is b>0; b=0 has a separate deterministic treatment. The four comparison forms preserve their parameter domains. |
| 1.10.21 | Substituting a mean estimate | Partly proved | Selected original consequences / explicit domains | [`ECTheoryLib.Probability.UnitIndependentSumChernoffUpperOfMeanLe`](../ECTheoryLib/Probability/Concentration/ChernoffMeanUpper.lean#L79); [`ECTheoryLib.Probability.UnitIndependentSumChernoffLowerOfLeMean`](../ECTheoryLib/Probability/Concentration/ChernoffMeanLower.lean#L86); [`ECTheoryLib.Probability.IndependentSumBennettUpperOfMeanLe`](../ECTheoryLib/Probability/Concentration/Bennett.lean#L362) | Upper/lower mean estimates are supported by the listed Chernoff, Hoeffding and variance-sensitive interfaces. Additive power/log forms retain their domains; nonnegative upper estimates are explicit for relative variance bounds. Not every consequence in the source discussion is mapped. |
| 1.10.22 | Transfer from conditional to independent sums | Proved by composition | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.StochasticDominatedFiniteSequentialSum`](../ECTheoryLib/Probability/StochasticOrder/SequentialSum.lean#L263); [`ECTheoryLib.Probability.StochasticDominatedFiniteSequentialSumLower`](../ECTheoryLib/Probability/StochasticOrder/SequentialSum.lean#L297); [`ECTheoryLib.Probability.StochasticDominatedIffClosedTail`](../ECTheoryLib/Probability/StochasticOrder/StochasticDomination.lean#L125) | Compose sequential domination with closed-tail order. Complete positive-probability histories, an independent reference family, arbitrary real thresholds and atoms are retained; a different proof route does not leave the conclusion unproved. |
| 1.10.23–1.10.24 | Negative-dependence concentration | Partly proved | Selected original bounds / explicit conventions | [`ECTheoryLib.Probability.OneNegativeCorrelationFiniteVarianceUpper`](../ECTheoryLib/Probability/NegativeDependence/NegativeCorrelationFiniteVariance.lean#L192); [`ECTheoryLib.Probability.ZeroNegativeCorrelationFiniteVarianceLower`](../ECTheoryLib/Probability/NegativeDependence/NegativeCorrelationFiniteVariance.lean#L246) | All-subfamily 1-/0-negative correlation and same-sample affine identities are required. Hoeffding, multiplicative and variance-sensitive families are present, including positive scales and zero-scale handling. Variance parameters are sums of marginal variances, not the total variance. Not every mean-substitution consequence is included. |
| 1.10.25 | Uniform subsets and hypergeometric counts | Partly proved | Selected original conclusions | [`ECTheoryLib.Probability.UniformSubset.OneNegativeCorrelation`](../ECTheoryLib/Probability/Sampling/UniformSubset.lean#L142); [`ECTheoryLib.Probability.UniformSubset.ZeroNegativeCorrelation`](../ECTheoryLib/Probability/Sampling/UniformSubset.lean#L214); [`ECTheoryLib.Probability.UniformSubset.ObservedCountMinUpperTail`](../ECTheoryLib/Probability/Sampling/Hypergeometric.lean#L245) | Actual fixed-size sampling PMFs, both negative-correlation directions, point masses, symmetry and finite Chernoff bounds are present. The full collection of variance-sensitive consequences is not mapped. |
| 1.10.26 | Independent unions of uniform subsets | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.UniformSubsetUnion.IndependentUniformSubsetsNegativelyCorrelated`](../ECTheoryLib/Probability/Sampling/UniformSubsetUnion.lean#L33) | A finite independent family with possibly different prescribed sizes; also permits empty families and zero sizes. An external HasLaw/iIndepFun interface is provided. |
| 1.10.27 | Bounded differences | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.IndependentBoundedDifferencesUpperTail`](../ECTheoryLib/Probability/Concentration/BoundedDifferences.lean#L305); [`ECTheoryLib.Probability.IndependentBoundedDifferencesLowerTail`](../ECTheoryLib/Probability/Concentration/BoundedDifferences.lean#L325) | Independent measurable coordinates and global coordinate widths for a measurable function; integrability is derived. Arbitrary measurable spaces, nonnegative widths and empty families are supported. The displayed constant 2 is preserved. |
| 1.10.28 | Bounded conditional expectations | Proved | Original conclusion / explicit conventions | [`ECTheoryLib.Probability.FutureCoordinateMean`](../ECTheoryLib/Probability/Concentration/BoundedDifferences.lean#L371); [`ECTheoryLib.Probability.IndependentBoundedConditionalExpectationsUpperTail`](../ECTheoryLib/Probability/Concentration/BoundedDifferences.lean#L693); [`ECTheoryLib.Probability.IndependentBoundedConditionalExpectationsLowerTail`](../ECTheoryLib/Probability/Concentration/BoundedDifferences.lean#L715) | Bounds on the actual future-coordinate average for every deterministic prefix, including zero-probability prefixes. Independent coordinates, measurable function, derived integrability and the source constant are retained; no StandardBorel assumption is added. |
| 1.10.30 | Azuma–Hoeffding | Partly proved | Restricted version | [`ECTheoryLib.Probability.BoundedConditionalSumUpperTail`](../ECTheoryLib/Probability/Concentration/AzumaHoeffding.lean#L71); [`ECTheoryLib.Probability.FiniteMartingaleAzumaUpperTail`](../ECTheoryLib/Probability/Concentration/AzumaHoeffding.lean#L85) | Finite horizon, true one-step conditional means, almost-everywhere increment bounds and an explicit StandardBorel environment. Initial values may be random/noncentered. The related maximal Azuma result does not by itself complete all of 1.10.31. |
| 1.10.37 | A binomial choose-moment tail | Proved | Original conclusion | [`ECTheoryLib.Probability.BinomialChooseMoment`](../ECTheoryLib/Probability/Distributions/BinomialTail.lean#L16); [`ECTheoryLib.Probability.BinomialChooseUpperTail`](../ECTheoryLib/Probability/Distributions/BinomialTail.lean#L70) | Bridges Mathlib binomial mass identities and Markov’s inequality; all n,k and p∈[0,1], including k>n. |


### Chapter 1 items without an established mapping

The following are not claimed as implemented textbook entries in this release:

- **1.4.2–1.4.5 and 1.4.7–1.4.13:** the full elementary-inequality, binomial
  coefficient and explicit Stirling families. Related Mathlib lemmas are candidates,
  not a verified correspondence for every displayed formula.
- **1.5.2–1.5.5:** the exact Needle distance statements and Bonferroni families.
  Existing Needle runtime analyses do not establish those particular statements.
- **1.8.11:** the general mutation-based black-box algorithm class and its runtime
  domination result.
- **1.10.15–1.10.20:** the remaining lower/anti-concentration results in that block.
- **1.10.29:** the cGA neutral-bit absorption model.
- **1.10.31–1.10.36:** the complete maximal-transfer and geometric-waiting-sum
  tail families and all listed algorithm applications. Related maximal Azuma,
  fitness-level and EA expectation theorems are available, but do not complete
  these entries.
- **1.10.38–1.10.39:** the refined binomial tail/point-mass estimates.

See the partly proved rows for the remaining gaps within implemented families.

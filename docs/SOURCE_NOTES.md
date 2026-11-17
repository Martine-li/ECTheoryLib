# Source notes

These comparisons refer to the 2020 Springer edition and its numbering, as
identified in [SOURCES](SOURCES.md). [COVERAGE](COVERAGE.md) is the current
implementation map. The entries below distinguish explicit probability/model
conventions from substantive changes of a mathematical statement.

**Review status.** The comparisons are AI-assisted against the supplied edition,
the current Lean statements and existing formal counterexamples. The displays
discussed below were compared with the local PDF during release preparation.
Lean checking establishes the formal results and examples, not the correctness of
every interpretation of the source. No independent human source audit or
publisher-confirmed errata status is recorded. A comparison with a different
edition or the cited original papers remains a separate task.

<a id="conditioning"></a>
## Conditioning: §2.2 and 2.3.1, 2.3.3, 2.3.11, 2.4.5

The source defines drift by conditioning on the current raw potential level.
The library offers three distinct interfaces:

| Adopted interface | Additional information | Effect |
| --- | --- | --- |
| Raw-level drift | Absorption at zero is explicit | A level identifies an active pre-hit state. |
| Surviving-level drift | Condition on t<T and X_t=s | The original process may leave zero later; no full-history drift inequality is required. |
| Full-history drift | A conditional-mean inequality before the hit | More history is controlled; this is not equivalent to the surviving-level condition. |

Measurability, positive-probability conditioning events, finite ranges or the
stated integrability replacement, and the gap above zero are explicit in the
corresponding declarations. Initial success is handled without inserting log(0)
into a displayed positive-initial-state formula.

The extra conditioning/absorption requirement is more than a choice of notation
if the raw-level display is read without it.
[Conditioning.lean](../Examples/Conditioning.lean), namespace
`AbsorptionConditioningAudit`, constructs a three-path process satisfying the
raw-level drift inequalities with infinite expected first hitting time. Its
`Counterexample`, `RawMultiplicativeTailFails` and
`RawCounterexampleFailsSurvivingDrift` show both the failure and why the
surviving-level repair excludes that process. This concerns that literal reading
of the displays, not every possible intended convention of the chapter.

<a id="linear"></a>
## Example 2.3.12: positive linear functions

The source reduces nonzero signed weights to positive sorted weights by symmetry,
then discusses several drift proofs and general mutation rates. The implemented
standard-rate theorem
[`RankRuntimeUpperBound`](../ECTheoryLib/Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean)
proves E[T]≤4en(1+log(2n)) for all strictly positive real weights in arbitrary
order, including ties, and every initial PMF. It acts on the original weakly
minimizing kernel with independent mutation probability 1/n.

This proves the positive-weight O(n log n) conclusion through a rank potential.
It is not only a OneMax specialization. Using this proof route does not leave
that conclusion unproved. A signed-weight reduction, the source unweighted-count
coupling proof, all illustrated potential choices, arbitrary constant c/n and
the sharp leading constant are not supplied by this release. No equivalence to
those broader models is inferred solely from the positive-weight theorem.

<a id="weak-walk"></a>
## Example 2.4.6: weak drift and the mean

The source starts at n and specifies mean decrease 1/n⁴, but displays mean n⁴.
For the library’s completed finite walk the exact mean is n/(1/n⁴)=n⁵:
[`WeakDriftExpectedRuntime`](../ECTheoryLib/Analysis/RandomWalk/WeakDriftRuntime.lean).
This is a substantive correction of the displayed mean, separately from an
explicit upper-boundary convention: at N the walk moves down with probability
1/n⁴ and otherwise holds. Zero is absorbing. This law preserves the specified
drift; it does not silently reflect an unbiased upward step at the boundary.

The [tail analysis](../ECTheoryLib/Analysis/RandomWalk/WeakDriftTail.lean) proves
the cubic high-probability conclusion at its stated capacity and n≥2 conditions
by a separate argument. No claim is made to reproduce every coupling step in
the source proof. The source display and the formal kernel/mean were compared;
other boundary completions require their own analysis.

<a id="additive-tails"></a>
## Theorem 2.4.7: geometric-jump additive tails

The library proves upper and lower tails with its explicit q/M constants in
[GeometricAdditiveTail](../ECTheoryLib/Tools/Drift/GeometricAdditiveTail.lean)
and [GeometricAdditiveLowerTail](../ECTheoryLib/Tools/Drift/GeometricAdditiveLowerTail.lean).
They retain history conditioning on active states and allow a real target,
overshoot and a nonabsorbing original process. A closed integer jump envelope
includes k=0; a strict-envelope conversion changes the constant to account for
the shift. These are proved replacement bounds, not a transcription of the
printed constants.

In [TailConditions.lean](../Examples/TailConditions.lean), namespace
`AdditiveTailSourceAudit`, `PrintedLowerTailFails` proves a finite counterexample
to the printed lower-tail expression under the displayed hypotheses. The same
file proves the process, jump and drift premises. The replacement lower-tail
bound and its strict/closed event conventions are checked separately. The
published counterexample here concerns the lower-tail display; the different
upper-tail constants are presented as an independently proved alternative.

<a id="general-tails"></a>
## Theorem 2.4.8: exponential moments and strictness

Two source-display differences are substantive:

- Weak separation g(s)≥g(a) only gives a non-strict upper probability bound.
  The strict interface requires strict separation and positive parameters.
- For the lower hitting-time tail, the implemented exponential-moment premise
  is an **upper** bound. It is combined with control of g inside the target
  and prefix-sum, or β≥1 product, hypotheses; it is not the printed lower
  bound on the moment.

See
[`GeneralExponentialDriftUpperTailOfCondExp`](../ECTheoryLib/Tools/Drift/GeneralExponentialUpperTail.lean)
and the sum/product interfaces in
[GeneralExponentialLowerTail](../ECTheoryLib/Tools/Drift/GeneralExponentialLowerTail.lean).
Fixed-initial-value results are distinct from marginal probability statements;
neither is relabeled as an F₀-conditional assertion.

[TailConditions.lean](../Examples/TailConditions.lean), namespace
`GeneralTailSourceAudit`, contains `PrintedStrictUpperTailFails` and
`PrintedLowerTailFails`. They verify the relevant displayed premises and the
failed conclusion on explicit finite processes. The current interfaces were
compared with the source displays; these examples are not claims about every
theorem in the original papers cited by the chapter.

<a id="negative-drift"></a>
## Theorem 2.4.9: finite global versus interval-local drift

The printed finite-range setup imposes drift away from the target at every
exterior level, for all times. In the corresponding formal model, these
hypotheses with an initially exterior state are incompatible:
`NegativeDriftSourceAudit.PrintedFiniteModelEmpty` in
[FiniteRangeDrift.lean](../Examples/FiniteRangeDrift.lean).
This is a vacuity issue in that literal model, not a false conclusion obtained
from a satisfiable instance.

The usable replacement is interval-local and permits unbounded processes:
[`GeometricJumpNegativeDriftTailOfActiveIncrement`](../ECTheoryLib/Tools/Drift/GeneralGeometricJumpNegative.lean),
with the geometric absolute-jump bound and asymptotic scale stated in its
interfaces. It is applied to actual walks and algorithm cases. Dropping a common
finite range while changing a global condition to an interval-local condition
is described here as a revised model, rather than declaring a blanket
generalization of the printed statement. The finite obstruction and adopted
interval model were compared; an intended-model assessment across sources
remains separate from this formal result.

<a id="tail-means"></a>
## Corollary 1.6.2: tails to means

The discrete additive forms use **natural centers** in the library. The
continuous upper-tail form is available under its measurable/integrable domain;
the lower-mean repair explicitly requires a nonnegative variable. These domains
are separated rather than combined into the source’s real-center/signed display.

[ExpectationConditions.lean](../Examples/ExpectationConditions.lean) contains:

- `BookExponentialTailSourceAudit.RealCenterUpper.Counterexample`: the integer
  variable X=1 at real center 1/2 satisfies the sampled upper-tail premise but
  violates its claimed mean bound for the chosen positive parameters.
- `BookExponentialTailSourceAudit.SignedLower.Counterexample`: an integrable
  four-point integer variable with values −4,1,1,1 satisfies the continuous
  lower-tail premise but has mean −1/4, violating the displayed lower bound 0.

These are finite/integrable counterexamples, not artifacts of an undefined or
infinite expectation. The relevant displays and repaired interfaces were
compared. The library’s full real and extended-time mean interfaces are linked
in [COVERAGE](COVERAGE.md).

<a id="other-probability"></a>
## Other Chapter 1 domain and endpoint differences

| Source | Adopted statement and impact | Lean entry | Comparison status |
| --- | --- | --- | --- |
| 1.6.6 | The numbered Hamming-mean formulas are retained. The crossover prose probability 1/2 applies to differing parental bits; an equal parental bit is inherited with probability 1. | [Uniform crossover expectation](../ECTheoryLib/Analysis/Crossover/UniformExpectation.lean) | Display/prose and model compared; no formula correction claimed. |
| 1.6.11 | The nonpositive-event second-moment bound uses a positive mean; merely nonzero mean does not supply its sign. | [Second moment](../ECTheoryLib/Probability/Concentration/SecondMoment.lean) | Source domain and formal sign condition compared. |
| 1.8.9(d) | Geometric waiting time decreases stochastically as success probability increases. The source direction is reversed. | [Geometric domination](../ECTheoryLib/Probability/Distributions/GeometricDomination.lean) | Printed direction and formal antitone law compared. |
| 1.9.2 | Upper coupon tails retain strict or rounded integer thresholds, with the closed next-integer form separate. | [Coupon tails](../ECTheoryLib/Analysis/CouponCollector/TailBounds.lean) | Threshold conventions compared; no substitution of a closed real event. |
| 1.9.4 | The repaired evaluation lower tail charges initialization and uses the (n/2)^ε factor. | [Universal EA](../ECTheoryLib/Analysis/OnePlusOneEA/UniversalLowerTail.lean) | Formula, cost convention and formal repair compared. |
| 1.10.2–1.10.3 | At the interior nested-log singularity the quotient is replaced explicitly by e² (scaled by α for mutation); elsewhere the original expression is retained on its domain. | [Logarithmic threshold](../ECTheoryLib/Probability/Concentration/LogarithmicThreshold.lean), [recorded mutation](../ECTheoryLib/Analysis/BitMutation/RecordedTailBounds.lean) | Denominator domain and repair compared. |
| 1.10.10–1.10.11 | The upper logarithmic equality needs μ>0, and its small-deviation simplification needs λ≤μ. The lower power chain keeps 0≤λ≤μ. Beyond the mean the finite lower tail is zero, while a separate quadratic probability bound covers λ≥0. | [Finite additive upper](../ECTheoryLib/Probability/Concentration/FiniteAdditiveChernoff.lean), [additive lower](../ECTheoryLib/Probability/Concentration/AdditiveChernoffLower.lean) | Domain distinctions compared; boundary conventions remain explicit. |

The tables do not classify all source discrepancies as confirmed textbook
errata. Source-specific mathematical examples are included when cited above;
full internal audit logs and historical comparisons are archival material.

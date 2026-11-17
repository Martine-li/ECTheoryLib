import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationFinite
import ECTheoryLib.Probability.NegativeDependence.ZeroNegativeCorrelation
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelation
import ECTheoryLib.Probability.Sampling.CouponCoverage
import ECTheoryLib.Problems.OneMax

/-!
# Concentration of actual collected and missing coupon counts

Reuse the existing true/zero coordinate counts on the Boolean record.
Both event families have the required all-subset product bounds, despite
being dependent. Exact means and upper tails refer to the actual Evolve
and PathMeasure laws, rather than independent reference indicators.
-/

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- The existing count of true coordinates is the number of collected coupons. -/
abbrev CollectedCount {n : ℕ} (x : Probability.CouponCollector.State n) : ℕ := OneMax x

/-- The same state record counts missing coupons by its zero coordinates. -/
abbrev UncollectedCount {n : ℕ} (x : Probability.CouponCollector.State n) : ℕ := Problems.OneMax.ZeroCount x

theorem CollectedCountAsEventSum {n : ℕ} (x : Probability.CouponCollector.State n) :
    (CollectedCount x : ℝ)=∑ i : Fin n, {y : Probability.CouponCollector.State n | y i=true}.indicator
      (fun _ => (1 : ℝ)) x := by
  classical
  simp only [CollectedCount,OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  cases Value : x i <;> simp [Value]

theorem UncollectedCountAsEventSum {n : ℕ} (x : Probability.CouponCollector.State n) :
    (UncollectedCount x : ℝ)=∑ i : Fin n, {y : Probability.CouponCollector.State n | y i=false}.indicator
      (fun _ => (1 : ℝ)) x := by
  classical
  rw [UncollectedCount,← Problems.OneMax.ZeroBitCountAsReal]
  apply Finset.sum_congr rfl
  intro i _
  cases Value : x i <;> simp [Value]

theorem CoverageOneNegativeCorrelationEvents {n : ℕ} (Positive : 0<n) (t : ℕ) :
    OneNegativelyCorrelated (Evolve (Probability.CouponCollector.Step n)
      (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true}) := by
  intro A
  have Joint : (⋂ i∈A, {x : Probability.CouponCollector.State n | x i=true})=
      {x | Probability.CouponCollector.Covers A x} := by ext x; simp [Probability.CouponCollector.Covers]
  rw [Joint]
  have Singleton (i : Fin n) : {x : Probability.CouponCollector.State n | x i=true}=
      {x | Probability.CouponCollector.Covers {i} x} := by ext x; simp [Probability.CouponCollector.Covers]
  simp_rw [Singleton]
  exact Probability.CouponCollector.CoverageOneNegativeCorrelation Positive A t

theorem MissingOneNegativeCorrelationEvents {n : ℕ} (Positive : 0<n) (t : ℕ) :
    OneNegativelyCorrelated (Evolve (Probability.CouponCollector.Step n)
      (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false}) := by
  intro A
  have Joint : (⋂ i∈A, {x : Probability.CouponCollector.State n | x i=false})=
      {x | Probability.CouponCollector.Misses A x} := by ext x; simp [Probability.CouponCollector.Misses]
  rw [Joint]
  have Singleton (i : Fin n) : {x : Probability.CouponCollector.State n | x i=false}=
      {x | Probability.CouponCollector.Misses {i} x} := by ext x; simp [Probability.CouponCollector.Misses]
  simp_rw [Singleton]
  exact Probability.CouponCollector.CoverageZeroNegativeCorrelation Positive A t

theorem CollectedMarginal {n : ℕ} (Positive : 0<n) (t : ℕ) (i : Fin n) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | x i=true}=1-(1-1/(n : ℝ))^t := by
  have Event : {x : Probability.CouponCollector.State n | x i=true}=
      {x | Probability.CouponCollector.Covers {i} x} := by ext x; simp [Probability.CouponCollector.Covers]
  rw [Event]
  exact Probability.CouponCollector.SingletonCoverageProbability Positive i t

theorem UncollectedMarginal {n : ℕ} (Positive : 0<n) (t : ℕ) (i : Fin n) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | x i=false}=(1-1/(n : ℝ))^t := by
  have Event : {x : Probability.CouponCollector.State n | x i=false}=
      {x | Probability.CouponCollector.Misses {i} x} := by ext x; simp [Probability.CouponCollector.Misses]
  rw [Event]
  have Bound := Probability.CouponCollector.MissingSetProbabilityExact Positive {i} t
  norm_num only [Finset.card_singleton,Nat.cast_one] at Bound
  exact Bound

theorem CollectedCountUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (1+d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))≤(CollectedCount x : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))) := by
  have Bound := OneNegativeCorrelationChernoffUpper _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true})
    (fun _ => (Set.to_countable _).measurableSet) (CoverageOneNegativeCorrelationEvents Positive t) d Nonnegative
  simp_rw [CollectedMarginal Positive,← CollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem UncollectedCountUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (1+d)*((n : ℝ)*(1-1/(n : ℝ))^t)≤(UncollectedCount x : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((n : ℝ)*(1-1/(n : ℝ))^t)) := by
  have Bound := OneNegativeCorrelationChernoffUpper _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false})
    (fun _ => (Set.to_countable _).measurableSet) (MissingOneNegativeCorrelationEvents Positive t) d Nonnegative
  simp_rw [UncollectedMarginal Positive,← UncollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

end
end ECTheoryLib.Analysis.CouponCollector

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory ECTheoryLib.Probability
noncomputable section

theorem CollectedCountExpectation {n : ℕ} (Positive : 0<n) (t : ℕ) :
    (∫ x, (CollectedCount x : ℝ)
      ∂(Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure)=
        (n : ℝ)*(1-(1-1/(n : ℝ))^t) := by
  simp_rw [CollectedCountAsEventSum]
  rw [EventCountExpectation _ _ (fun _ => (Set.to_countable _).measurableSet)]
  simp_rw [CollectedMarginal Positive]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem UncollectedCountExpectation {n : ℕ} (Positive : 0<n) (t : ℕ) :
    (∫ x, (UncollectedCount x : ℝ)
      ∂(Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure)=
        (n : ℝ)*(1-1/(n : ℝ))^t := by
  simp_rw [UncollectedCountAsEventSum]
  rw [EventCountExpectation _ _ (fun _ => (Set.to_countable _).measurableSet)]
  simp_rw [UncollectedMarginal Positive]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem CollectedCountPathUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (PathMeasure (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n))).real
      {Path | (1+d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))≤(CollectedCount (Path t) : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))) := by
  have Marginal := PathMeasureCoordinateEvent (Probability.CouponCollector.Step n)
    (PMF.pure (Probability.CouponCollector.Empty n)) t
    {x | (1+d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))≤(CollectedCount x : ℝ)}
  simp only [Set.mem_ofPred_eq] at Marginal
  unfold Measure.real
  rw [Marginal]
  exact CollectedCountUpperTail Positive t d Nonnegative

theorem UncollectedCountPathUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (PathMeasure (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n))).real
      {Path | (1+d)*((n : ℝ)*(1-1/(n : ℝ))^t)≤(UncollectedCount (Path t) : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((n : ℝ)*(1-1/(n : ℝ))^t)) := by
  have Marginal := PathMeasureCoordinateEvent (Probability.CouponCollector.Step n)
    (PMF.pure (Probability.CouponCollector.Empty n)) t
    {x | (1+d)*((n : ℝ)*(1-1/(n : ℝ))^t)≤(UncollectedCount x : ℝ)}
  simp only [Set.mem_ofPred_eq] at Marginal
  unfold Measure.real
  rw [Marginal]
  exact UncollectedCountUpperTail Positive t d Nonnegative

end
end ECTheoryLib.Analysis.CouponCollector

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory Set ECTheoryLib.Probability
noncomputable section

theorem CoverageZeroNegativeCorrelationEvents {n : ℕ} (Positive : 0<n) (t : ℕ) :
    ZeroNegativelyCorrelated (Evolve (Probability.CouponCollector.Step n)
      (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true}) := by
  have Events : (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true}ᶜ)=
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false}) := by
    funext i
    ext x
    cases Value : x i <;> simp [Value]
  unfold ZeroNegativelyCorrelated
  rw [Events]
  exact MissingOneNegativeCorrelationEvents Positive t

theorem MissingZeroNegativeCorrelationEvents {n : ℕ} (Positive : 0<n) (t : ℕ) :
    ZeroNegativelyCorrelated (Evolve (Probability.CouponCollector.Step n)
      (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false}) := by
  have Events : (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false}ᶜ)=
      (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true}) := by
    funext i
    ext x
    cases Value : x i <;> simp [Value]
  unfold ZeroNegativelyCorrelated
  rw [Events]
  exact CoverageOneNegativeCorrelationEvents Positive t

/-- This lower bound uses the original collected mean, rather than treating
an upper tail of missing coupons as though its mean were unchanged. -/
theorem CollectedCountLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (CollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))}≤
        Real.exp (-(d+(1-d)*Real.log (1-d))*((n : ℝ)*(1-(1-1/(n : ℝ))^t))) := by
  have Bound := ZeroNegativeCorrelationChernoffLower _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true})
    (fun _ => (Set.to_countable _).measurableSet) (CoverageZeroNegativeCorrelationEvents Positive t) d InUnit
  simp_rw [CollectedMarginal Positive,← CollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem UncollectedCountLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (UncollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-1/(n : ℝ))^t)}≤
        Real.exp (-(d+(1-d)*Real.log (1-d))*((n : ℝ)*(1-1/(n : ℝ))^t)) := by
  have Bound := ZeroNegativeCorrelationChernoffLower _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false})
    (fun _ => (Set.to_countable _).measurableSet) (MissingZeroNegativeCorrelationEvents Positive t) d InUnit
  simp_rw [UncollectedMarginal Positive,← UncollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem CollectedCountPathLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (PathMeasure (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n))).real
      {Path | (CollectedCount (Path t) : ℝ)≤(1-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))}≤
        Real.exp (-(d+(1-d)*Real.log (1-d))*((n : ℝ)*(1-(1-1/(n : ℝ))^t))) := by
  have Marginal := PathMeasureCoordinateEvent (Probability.CouponCollector.Step n)
    (PMF.pure (Probability.CouponCollector.Empty n)) t
    {x | (CollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))}
  simp only [Set.mem_ofPred_eq] at Marginal
  unfold Measure.real
  rw [Marginal]
  exact CollectedCountLowerTail Positive t d InUnit

theorem UncollectedCountPathLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (PathMeasure (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n))).real
      {Path | (UncollectedCount (Path t) : ℝ)≤(1-d)*((n : ℝ)*(1-1/(n : ℝ))^t)}≤
        Real.exp (-(d+(1-d)*Real.log (1-d))*((n : ℝ)*(1-1/(n : ℝ))^t)) := by
  have Marginal := PathMeasureCoordinateEvent (Probability.CouponCollector.Step n)
    (PMF.pure (Probability.CouponCollector.Empty n)) t
    {x | (UncollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-1/(n : ℝ))^t)}
  simp only [Set.mem_ofPred_eq] at Marginal
  unfold Measure.real
  rw [Marginal]
  exact UncollectedCountLowerTail Positive t d InUnit

end
end ECTheoryLib.Analysis.CouponCollector

namespace ECTheoryLib.Analysis.CouponCollector
open MeasureTheory Set ECTheoryLib.Probability
noncomputable section

theorem CollectedCountFiniteUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (1+d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))≤(CollectedCount x : ℝ)}≤
        FiniteChernoffUpperBound n ((n : ℝ)*(1-(1-1/(n : ℝ))^t)) d := by
  have Bound := OneNegativeCorrelationFiniteChernoffUpper _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true})
    (fun _ => (Set.to_countable _).measurableSet) (CoverageOneNegativeCorrelationEvents Positive t) d Nonnegative
  simp_rw [CollectedMarginal Positive,← CollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem UncollectedCountFiniteUpperTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (Nonnegative : 0≤d) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (1+d)*((n : ℝ)*(1-1/(n : ℝ))^t)≤(UncollectedCount x : ℝ)}≤
        FiniteChernoffUpperBound n ((n : ℝ)*(1-1/(n : ℝ))^t) d := by
  have Bound := OneNegativeCorrelationFiniteChernoffUpper _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false})
    (fun _ => (Set.to_countable _).measurableSet) (MissingOneNegativeCorrelationEvents Positive t) d Nonnegative
  simp_rw [UncollectedMarginal Positive,← UncollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem CollectedCountFiniteLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (CollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-(1-1/(n : ℝ))^t))}≤
        FiniteChernoffLowerBound n ((n : ℝ)*(1-(1-1/(n : ℝ))^t)) d := by
  have Bound := ZeroNegativeCorrelationFiniteChernoffLower _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=true})
    (fun _ => (Set.to_countable _).measurableSet) (CoverageZeroNegativeCorrelationEvents Positive t) d InUnit
  simp_rw [CollectedMarginal Positive,← CollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

theorem UncollectedCountFiniteLowerTail {n : ℕ} (Positive : 0<n) (t : ℕ) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (Evolve (Probability.CouponCollector.Step n) (PMF.pure (Probability.CouponCollector.Empty n)) t).toMeasure.real
      {x | (UncollectedCount x : ℝ)≤(1-d)*((n : ℝ)*(1-1/(n : ℝ))^t)}≤
        FiniteChernoffLowerBound n ((n : ℝ)*(1-1/(n : ℝ))^t) d := by
  have Bound := ZeroNegativeCorrelationFiniteChernoffLower _
    (fun i : Fin n => {x : Probability.CouponCollector.State n | x i=false})
    (fun _ => (Set.to_countable _).measurableSet) (MissingZeroNegativeCorrelationEvents Positive t) d InUnit
  simp_rw [UncollectedMarginal Positive,← UncollectedCountAsEventSum] at Bound
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Bound

end
end ECTheoryLib.Analysis.CouponCollector

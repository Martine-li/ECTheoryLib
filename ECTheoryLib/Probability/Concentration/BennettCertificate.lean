import ECTheoryLib.Probability.Concentration.Bennett

/-!
# Bennett tails from a centered exponential-moment certificate

Independence is unnecessary when the actual sum already supplies the
Bennett MGF estimate. The variance parameter remains the sum of actual
marginal variances. Zero marginal variance uses the existing deterministic
lemma, which itself requires no independence.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- A dependent family may provide a centered Bennett MGF certificate.
The parameter is the sum of actual marginal variances, not Var(sum X). -/
theorem SumBennettUpperOfCertificate {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (SquareIntegrable : ∀ i, MemLp (X i) 2 P)
    (Upper : ∀ i, ∀ᵐ ω ∂P, X i ω≤(∫ w, X i w ∂P)+1)
    (Certificate : ∀ t : ℝ, 0≤t →
      mgf (fun ω => (∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)) P t≤
        Real.exp ((∑ i, variance (X i) P)*(Real.exp t-1-t)))
    (d : ℝ) (NonnegativeDeviation : 0≤d) :
    P.real {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}≤
      BennettUpperBound (∑ i, variance (X i) P) d := by
  by_cases ZeroDeviation : d=0
  · simp only [BennettUpperBound,ZeroDeviation,ite_true]
    exact measureReal_le_one
  by_cases ZeroVariance : (∑ i, variance (X i) P)=0
  · simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false,ite_true]
    have Zero := ZeroVarianceSumDeviationProbability P X SquareIntegrable ZeroVariance d
      (lt_of_le_of_ne NonnegativeDeviation (Ne.symm ZeroDeviation))
    have Subset : {ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω}⊆
        {ω | d≤|(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)|} := by
      intro ω hω
      change (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω at hω
      exact (by linarith : d≤(∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)).trans (le_abs_self _)
    have EventZero := measure_mono_null Subset Zero
    simp only [Measure.real,EventZero,ENNReal.toReal_zero,le_refl]
  have PositiveVariance : 0<∑ i, variance (X i) P :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => variance_nonneg (X i) P)) (Ne.symm ZeroVariance)
  simp only [BennettUpperBound,ZeroDeviation,ZeroVariance,ite_false]
  let v := ∑ i, variance (X i) P
  let Z := fun ω => (∑ i, X i ω)-(∫ w, ∑ i, X i w ∂P)
  have MeanSum : (∫ w, ∑ i, X i w ∂P)=∑ i, ∫ w, X i w ∂P :=
    integral_finsetSum _ (fun i _ => (SquareIntegrable i).integrable (by norm_num))
  have UpperZ : ∀ᵐ ω ∂P, Z ω≤(Fintype.card ι : ℝ) := by
    filter_upwards [ae_all_iff.mpr Upper] with ω Bounds
    have Each := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Bounds i)
    simpa only [Z,MeanSum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,sub_le_iff_le_add,add_comm] using Each
  have MeasurableZ : AEMeasurable Z P := by
    simpa only [Z,Finset.sum_apply] using
      (Finset.aemeasurable_sum Finset.univ (fun i _ => (SquareIntegrable i).aemeasurable)).sub_const
        (∫ w, ∑ i, X i w ∂P)
  have TiltNonnegative : 0≤Real.log (1+d/v) :=
    Real.log_nonneg (by have := div_nonneg NonnegativeDeviation PositiveVariance.le; linarith)
  have IntExp := UpperBoundedExponentialIntegrable P Z (Fintype.card ι) _
    MeasurableZ UpperZ TiltNonnegative
  have BoundMGF := Certificate (Real.log (1+d/v)) TiltNonnegative
  rw [Real.exp_log (by have := div_nonneg NonnegativeDeviation PositiveVariance.le; linarith),
    add_sub_cancel_left] at BoundMGF
  have Bound := BennettUpperTailOfMGF P Z v d PositiveVariance NonnegativeDeviation IntExp BoundMGF
  have Event : {ω | d≤Z ω}={ω | (∫ w, ∑ i, X i w ∂P)+d≤∑ i, X i ω} := by
    ext ω
    simp only [mem_ofPred_eq,Z]
    constructor <;> intro h <;> linarith
  rw [Event] at Bound
  exact Bound

end
end ECTheoryLib.Probability

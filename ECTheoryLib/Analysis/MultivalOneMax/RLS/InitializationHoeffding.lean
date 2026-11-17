import ECTheoryLib.Probability.Concentration.Hoeffding
import ECTheoryLib.Analysis.MultivalOneMax.RLS.UniformInitialLaw

/-!
# Hoeffding concentration of actual uniform Hamming initialization

The existing whole-vector product law supplies independent coordinate
mismatch indicators. Their sum is the actual Hamming distance and the
existing expectation theorem supplies its center n(1-1/r). No independence
or distribution assumption is left to the caller. Empty strings and a
one-symbol alphabet remain valid initialization models.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- The actual uniform initialization has the Hoeffding absolute-deviation bound. -/
theorem UniformHammingHoeffdingDeviation {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (d : ℝ) (Nonnegative : 0 ≤ d) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real
      {x | d ≤ |(Hamming Target x : ℝ)-(n : ℝ)*(1-1/(r : ℝ))|} ≤
      2*Real.exp (-2*d^2/(n : ℝ)) := by
  classical
  let P := (MultivalRLSInit n r PositiveAlphabet).toMeasure
  let X := fun (i : Fin n) (x : MultiValues n r) => if x i = Target i then (0 : ℝ) else 1
  have MeasurableX (i : Fin n) : AEMeasurable (X i) P := (measurable_of_finite _).aemeasurable
  have Independent : iIndepFun X P := by
    change iIndepFun X (MultivalRLSInit n r PositiveAlphabet).toMeasure
    rw [MultivalRLSInitProduct]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun v : Fin r => if v = Target i then (0 : ℝ) else 1)).aemeasurable)
  have InUnit (i : Fin n) : ∀ᵐ x ∂P, X i x ∈ Set.Icc 0 1 := by
    apply ae_of_all
    intro x
    dsimp only [X]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have SumHamming (x : MultiValues n r) : (∑ i, X i x) = (Hamming Target x : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumDeviation P n X MeasurableX Independent InUnit d Nonnegative
  simp only [SumHamming] at Bound
  change (MultivalRLSInit n r PositiveAlphabet).toMeasure.real
      {x | d ≤ |(Hamming Target x : ℝ)-
        (∫ y, (Hamming Target y : ℝ) ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure)|} ≤ _ at Bound
  rw [UniformHammingExpectation] at Bound
  exact Bound

/-- The binary finite alphabet has mean n/2, giving Doerr Lemma 1.10.8. -/
theorem UniformBinaryHammingHoeffdingDeviation {n : ℕ} (Target : MultiValues n 2)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (MultivalRLSInit n 2 (by decide)).toMeasure.real
      {x | d ≤ |(Hamming Target x : ℝ)-(n : ℝ)/2|} ≤
      2*Real.exp (-2*d^2/(n : ℝ)) := by
  have Bound := UniformHammingHoeffdingDeviation (by decide : 0 < 2) Target d Nonnegative
  simp only [Nat.cast_ofNat] at Bound
  have Mean : (n : ℝ)*(1-1/(2 : ℝ)) = (n : ℝ)/2 := by ring
  rw [Mean] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSMultival

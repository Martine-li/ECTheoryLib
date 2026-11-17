import ECTheoryLib.Algorithms.MultivalRLSInit
import ECTheoryLib.Problems.MultivalOneMax
import ECTheoryLib.Probability.Distributions.BinomialExpectation
import Mathlib.Probability.Distributions.Binomial

/-!
# Hamming-distance law under uniform multi-valued initialization

Independent uniform coordinates mismatch a fixed target with probability
`1-1/r`. The mismatch set has the Bernoulli random-set law, and its cardinality
has distribution `Binomial(n, 1-1/r)`. The results concern the actual initial
PMF and include its mass at zero distance.
-/

namespace ECTheoryLib.Analysis.RLSMultival

open MeasureTheory ProbabilityTheory ECTheoryLib.Problems.MultivalOneMax
open scoped unitInterval

noncomputable section

/-- Mismatch probability of a uniformly initialized coordinate against its target. -/
def MismatchProbability (r : Nat) (PositiveAlphabet : 0 < r) : I :=
  ⟨1 - 1 / (r : ℝ), by
    have hr : (1 : ℝ) ≤ r := by exact_mod_cast PositiveAlphabet
    constructor
    · exact sub_nonneg.mpr (div_le_one (by positivity) |>.mpr hr)
    · exact sub_le_self _ (by positivity)⟩

theorem UniformValueMismatchLaw {r : Nat} (PositiveAlphabet : 0 < r) (z : Fin r) :
    (UniformValue r PositiveAlphabet).toMeasure.map (fun v => v ≠ z) =
      unitInterval.toNNReal (MismatchProbability r PositiveAlphabet) •
        Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm (MismatchProbability r PositiveAlphabet)) •
        Measure.dirac False := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hr : (r : ℝ) ≠ 0 := by positivity
  by_cases hb : b
  · have heq : b = True := propext (iff_true_intro hb)
    subst b
    have Fiber : (fun v : Fin r => v ≠ z) ⁻¹' {True} = {v | v ≠ z} := by ext; simp
    rw [Fiber]
    simp only [UniformValue, measureReal_def,
      PMF.toMeasure_uniformOfFintype_apply _ (Set.to_countable _).measurableSet,
      Fintype.card_fin]
    simp [MismatchProbability, ENNReal.toReal_div]
    field_simp
    have Card : ({x : Fin r | x ≠ z} : Finset (Fin r)).card = r - 1 := by
      simpa only [Fintype.card_subtype] using OtherCoordinateValuesCard z
    rw [Card, Nat.cast_sub PositiveAlphabet, Nat.cast_one]
  · have heq : b = False := propext (iff_false_intro hb)
    subst b
    have Fiber : (fun v : Fin r => v ≠ z) ⁻¹' {False} = {z} := by ext; simp
    rw [Fiber]
    simp [measureReal_def, UniformValueProbability,
      MismatchProbability]

/-- The mismatch-coordinate set is an independent Bernoulli random set
with inclusion probability `1-1/r`. -/
theorem UniformMismatchSetLaw {n r : Nat} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.map
        (fun x => {i | x i ≠ Target i}) =
      setBernoulli Set.univ (MismatchProbability r PositiveAlphabet) := by
  rw [MultivalRLSInitProduct, setBernoulli_eq_map, Measure.infinitePi_eq_pi]
  have Maps := Measure.pi_map_pi (μ := fun _ : Fin n => (UniformValue r PositiveAlphabet).toMeasure)
    (fun i => (measurable_of_finite (fun v : Fin r => v ≠ Target i)).aemeasurable)
  have MeasurablePred : Measurable (fun x : MultiValues n r => fun i => x i ≠ Target i) := by
    exact measurable_of_finite _
  change Measure.map ((fun b : Fin n → Prop => {i | b i}) ∘
    (fun x : MultiValues n r => fun i => x i ≠ Target i)) _ = _
  rw [← Measure.map_map (measurable_of_finite (fun b : Fin n → Prop => {i | b i})) MeasurablePred,
    Maps]
  simp only [UniformValueMismatchLaw, Set.mem_univ]

/-- The initial Hamming distance has law `Binomial(n, 1-1/r)`, expressed
as the pushforward of the actual uniform initialization measure. -/
theorem UniformHammingBinomial {n r : Nat} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.map (Hamming Target) =
      binomial n (MismatchProbability r PositiveAlphabet) := by
  classical
  have HammingAsCard : Hamming Target = fun x => Set.ncard {i | x i ≠ Target i} := by
    funext x
    simp only [Hamming, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
      Finset.card_filter, ite_not]
  rw [HammingAsCard]
  change Measure.map (Set.ncard ∘ (fun x : MultiValues n r => {i | x i ≠ Target i})) _ = _
  rw [← Measure.map_map (measurable_of_finite Set.ncard)
    (measurable_of_finite (fun x : MultiValues n r => {i | x i ≠ Target i})),
    UniformMismatchSetLaw]
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton Set.finite_univ, binomial_real_singleton]
  simp only [Set.ncard_univ, Nat.card_fin]

/-- The actual uniform initialization has mean Hamming distance `n(1-1/r)`.
The full binomial law above supplies the hypotheses of the general mean theorem;
no independence or distribution premise is left to the caller. -/
theorem UniformHammingExpectation {n r : Nat} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    (∫ x, (Hamming Target x : ℝ) ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) =
      (n : ℝ) * (1 - 1 / (r : ℝ)) := by
  have InitialLaw : HasLaw (Hamming Target)
      (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure := by
    constructor
    · exact (measurable_of_finite _).aemeasurable
    · exact UniformHammingBinomial PositiveAlphabet Target
  have Mean := ECTheoryLib.Probability.BinomialNatExpectationOfLaw
    (MultivalRLSInit n r PositiveAlphabet).toMeasure (Hamming Target) n
    (MismatchProbability r PositiveAlphabet) InitialLaw
  change (∫ x, (Hamming Target x : ℝ) ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) =
    (1 - 1 / (r : ℝ)) * n at Mean
  rw [Mean, mul_comm]

end
end ECTheoryLib.Analysis.RLSMultival

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Ring

/-!
# Bounded, conditionally centered increments

Construct Mathlib's existing conditional sub-Gaussian MGF from an ambient
almost-sure absolute bound and genuine past-conditioned mean zero.
The ambient probability space is standard Borel; the conditioning
sub-sigma-algebra may be arbitrary. Zero scale is allowed.
-/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- Boundedness and genuine past-conditioned centering supply Mathlib's conditional MGF. -/
theorem ConditionalSubGaussianOfBoundedCentered {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (Below : m ≤ mΩ) (Z : Ω → ℝ) (c : ℝ≥0)
    (Observable : AEMeasurable Z P) (Bounded : ∀ᵐ ω ∂P, |Z ω| ≤ (c : ℝ))
    (Centered : P[Z | m] =ᵐ[P] (fun _ => 0)) :
    HasCondSubgaussianMGF m Below Z (c ^ 2) P := by
  have Interval : ∀ᵐ ω ∂P, Z ω ∈ Set.Icc (-(c : ℝ)) (c : ℝ) := by
    filter_upwards [Bounded] with ω Bound
    exact abs_le.mp Bound
  have IntegrableZ : Integrable Z P :=
    Integrable.of_mem_Icc (-(c : ℝ)) (c : ℝ) Observable Interval
  have TrimCentered : P[Z | m] =ᵐ[P.trim Below] (fun _ => 0) :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable Below
      stronglyMeasurable_condExp stronglyMeasurable_const Centered
  have KernelMean :=
    condExp_ae_eq_trim_integral_condExpKernel (mΩ := mΩ) Below IntegrableZ
  have KernelInterval : ∀ᵐ ω' ∂P.trim Below,
      ∀ᵐ ω ∂condExpKernel (mΩ := mΩ) P m ω',
        Z ω ∈ Set.Icc (-(c : ℝ)) (c : ℝ) := by
    apply Measure.ae_ae_of_ae_comp
    simpa only [condExpKernel_comp_trim] using Interval
  have KernelIntegrable : ∀ᵐ ω' ∂P.trim Below,
      Integrable Z (condExpKernel (mΩ := mΩ) P m ω') := by
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [condExpKernel_comp_trim] using IntegrableZ
  have Parameter : ((‖(c : ℝ) - -(c : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) = c ^ 2 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, div_pow, sq_abs]
    ring
  change Kernel.HasSubgaussianMGF Z (c ^ 2) (condExpKernel (mΩ := mΩ) P m) (P.trim Below)
  refine ⟨?_, ?_⟩
  · intro t
    simpa only [condExpKernel_comp_trim] using
      (integrable_exp_mul_of_mem_Icc (t := t) Observable Interval)
  · filter_upwards [KernelInterval, KernelIntegrable, KernelMean, TrimCentered]
      with ω IntervalAt IntegrableAt MeanAt ZeroAt
    have MeanZero : (∫ w, Z w ∂condExpKernel (mΩ := mΩ) P m ω) = 0 :=
      MeanAt.symm.trans ZeroAt
    have Bound := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      IntegrableAt.aemeasurable IntervalAt MeanZero
    rw [Parameter] at Bound
    exact Bound.mgf_le

end
end ECTheoryLib.Probability


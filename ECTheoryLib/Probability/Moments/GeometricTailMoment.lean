import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute exponential moments from geometric tails

Integer-threshold tail bounds imply integrability, even for unbounded variables.
Mathlib supplies nonnegative integral/sum interchange and geometric summation.
The strict gap exp(q)<A is essential. No distribution is reimplemented.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integer-threshold geometric tails control a positive exponential moment.
No finite range or finite sample space is required. -/
theorem AbsoluteExponentialMomentOfGeometricTail
    (μ : Measure Ω) (Z : Ω → ℝ) (q A r : ℝ)
    (NonnegativeQ : 0≤q) (PositiveA : 0<A) (ExpBelow : Real.exp q<A)
    (NonnegativeR : 0≤r) (Observable : Measurable Z)
    (Tail : ∀ j : ℕ, μ {ω | (j : ℝ)≤|Z ω|} ≤ ENNReal.ofReal (r/A^j)) :
    Integrable (fun ω => Real.exp (q*|Z ω|)) μ ∧
    (∫ ω, Real.exp (q*|Z ω|) ∂μ) ≤ r*Real.exp q/(1-Real.exp q/A) := by
  classical
  let C (j : ℕ) : Set Ω := {ω | (j : ℝ)≤|Z ω|}
  have Cells (j : ℕ) : MeasurableSet (C j) :=
    measurableSet_le measurable_const Observable.abs
  let F (j : ℕ) : Ω → ℝ≥0∞ :=
    (C j).indicator (fun _ => ENNReal.ofReal (Real.exp (q*((j : ℝ)+1))))
  have MeasurableF (j : ℕ) : Measurable (F j) := measurable_const.indicator (Cells j)
  have Pointwise (ω : Ω) :
      ENNReal.ofReal (Real.exp (q*|Z ω|)) ≤ ∑' j : ℕ, F j ω := by
    let j := Nat.floor |Z ω|
    have Member : ω∈C j := Nat.floor_le (abs_nonneg (Z ω))
    calc
      _ ≤ F j ω := by
        change ENNReal.ofReal (Real.exp (q*|Z ω|)) ≤
          (C j).indicator (fun _ => ENNReal.ofReal (Real.exp (q*((j : ℝ)+1)))) ω
        rw [Set.indicator_of_mem Member]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one |Z ω|).le NonnegativeQ
      _ ≤ _ := ENNReal.le_tsum j
  let ratio := Real.exp q/A
  have NonnegativeRatio : 0≤ratio := div_nonneg (Real.exp_pos _).le PositiveA.le
  have RatioBelow : ratio<1 := (div_lt_one PositiveA).mpr ExpBelow
  have NonnegativeCoefficient : 0≤r*Real.exp q := mul_nonneg NonnegativeR (Real.exp_pos _).le
  have Each (j : ℕ) :
      (∫⁻ ω, F j ω ∂μ) ≤ ENNReal.ofReal ((r*Real.exp q)*ratio^j) := by
    have Algebra : Real.exp (q*((j : ℝ)+1))*(r/A^j) = (r*Real.exp q)*ratio^j := by
      rw [show q*((j : ℝ)+1)=(j : ℝ)*q+q by ring, Real.exp_add, Real.exp_nat_mul]
      dsimp [ratio]
      rw [div_pow]
      ring
    change (∫⁻ ω, (C j).indicator (fun _ => ENNReal.ofReal (Real.exp (q*((j : ℝ)+1)))) ω ∂μ) ≤ _
    rw [lintegral_indicator (Cells j), lintegral_const]
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (q*((j : ℝ)+1)))*ENNReal.ofReal (r/A^j) :=
        mul_le_mul' le_rfl (Tail j)
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Algebra]
  have Series : Summable (fun j : ℕ => (r*Real.exp q)*ratio^j) :=
    (summable_geometric_of_lt_one NonnegativeRatio RatioBelow).mul_left _
  have Total : (∫⁻ ω, ENNReal.ofReal (Real.exp (q*|Z ω|)) ∂μ) ≤
      ENNReal.ofReal (r*Real.exp q/(1-Real.exp q/A)) := by
    calc
      _ ≤ ∫⁻ ω, ∑' j : ℕ, F j ω ∂μ := lintegral_mono Pointwise
      _ = ∑' j : ℕ, ∫⁻ ω, F j ω ∂μ := lintegral_tsum (fun j => (MeasurableF j).aemeasurable)
      _ ≤ ∑' j : ℕ, ENNReal.ofReal ((r*Real.exp q)*ratio^j) := ENNReal.tsum_le_tsum Each
      _ = ENNReal.ofReal (∑' j : ℕ, (r*Real.exp q)*ratio^j) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg NonnegativeCoefficient (pow_nonneg NonnegativeRatio j)) Series).symm
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one NonnegativeRatio RatioBelow]; rfl
  have ObservableExp : Measurable (fun ω => Real.exp (q*|Z ω|)) :=
    Real.measurable_exp.comp (Observable.abs.const_mul q)
  have NonnegativeExp : 0≤ᵐ[μ] (fun ω => Real.exp (q*|Z ω|)) :=
    ae_of_all _ (fun ω => (Real.exp_pos _).le)
  have IntegrableExp : Integrable (fun ω => Real.exp (q*|Z ω|)) μ := by
    refine ⟨ObservableExp.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal NonnegativeExp).mpr (Total.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨IntegrableExp, ?_⟩
  have NonnegativeBound : 0≤r*Real.exp q/(1-Real.exp q/A) :=
    div_nonneg NonnegativeCoefficient (sub_pos.mpr RatioBelow).le
  apply (ENNReal.ofReal_le_ofReal_iff NonnegativeBound).mp
  rw [ofReal_integral_eq_lintegral_ofReal IntegrableExp NonnegativeExp]
  exact Total

/-- Radius used in the corrected simplified drift proof. -/
def GeometricJumpMomentRadius (eta : ℝ) : ℝ := Real.log (1+eta/2)

/-- Explicit absolute-moment bound for jump tails r/(1+eta)^j. -/
def GeometricJumpMomentBound (eta r : ℝ) : ℝ := r*(1+eta/2)*(2+2/eta)

theorem GeometricJumpMomentRadiusPositive (eta : ℝ) (PositiveEta : 0<eta) :
    0<GeometricJumpMomentRadius eta := Real.log_pos (by linarith)

theorem GeometricJumpMomentBoundPositive (eta r : ℝ) (PositiveEta : 0<eta)
    (PositiveR : 0<r) : 0<GeometricJumpMomentBound eta r := by
  dsimp [GeometricJumpMomentBound]
  positivity

/-- The constants depend only on the geometric decay parameter and linearly
on its prefactor. The integral exists even for unbounded real variables. -/
theorem AbsoluteExponentialMomentOfJumpTail
    (μ : Measure Ω) (Z : Ω → ℝ) (eta r : ℝ) (PositiveEta : 0<eta)
    (NonnegativeR : 0≤r) (Observable : Measurable Z)
    (Tail : ∀ j : ℕ, μ {ω | (j : ℝ)≤|Z ω|} ≤ ENNReal.ofReal (r/(1+eta)^j)) :
    Integrable (fun ω => Real.exp (GeometricJumpMomentRadius eta*|Z ω|)) μ ∧
    (∫ ω, Real.exp (GeometricJumpMomentRadius eta*|Z ω|) ∂μ) ≤
      GeometricJumpMomentBound eta r := by
  have PositiveBase : 0<1+eta/2 := by linarith
  have Exponential : Real.exp (GeometricJumpMomentRadius eta)=1+eta/2 :=
    Real.exp_log PositiveBase
  have Bound := AbsoluteExponentialMomentOfGeometricTail μ Z (GeometricJumpMomentRadius eta)
    (1+eta) r (GeometricJumpMomentRadiusPositive eta PositiveEta).le
    (by linarith) (by rw [Exponential]; linarith) NonnegativeR Observable Tail
  have Algebra : r*(1+eta/2)/(1-(1+eta/2)/(1+eta))=GeometricJumpMomentBound eta r := by
    have PositiveDenominator : 0<1-(1+eta/2)/(1+eta) := by
      apply sub_pos.mpr
      apply (div_lt_one (by linarith : 0<1+eta)).mpr
      linarith
    apply (div_eq_iff PositiveDenominator.ne').mpr
    dsimp [GeometricJumpMomentBound]
    field_simp [PositiveEta.ne', show (1+eta)≠0 by linarith]
    ring
  rw [Exponential, Algebra] at Bound
  exact Bound

end
end ECTheoryLib.Probability

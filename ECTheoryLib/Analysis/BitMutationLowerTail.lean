import ECTheoryLib.Probability.Processes.BackwardBound
import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Problems.TargetOneMax
import ECTheoryLib.Algorithms.OnePlusOneEA
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Hitting lower tails for selected independent bit mutation

The selector returns either parent or child and preserves the target.
Only fresh mutation coordinates are assumed independent; dependence
created by selection is retained. Arbitrary initial laws and all fixed
rates in [0,1] are covered before specializing uniform initialization.
-/

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- A Hamming power is a product of one-coordinate agreement factors. -/
theorem HammingPowerProduct {n : ℕ} (Target x : Bits n) (a : ℝ) :
    a^Hamming Target x=∏ i : Fin n, if x i=Target i then 1 else a := by
  classical
  rw [Hamming,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

/-- Only a wrong coordinate that remains wrong is an unavoidable mismatch.
The input comparison may choose either parent or child. -/
theorem SelectedHammingPowerPointwise {n : ℕ} (Target x y z : Bits n) (a : ℝ)
    (Nonnegative : 0≤a) (AtMostOne : a≤1) (Chosen : z=x ∨ z=y) :
    a^Hamming Target z≤
      ∏ i : Fin n, if x i=Target i then 1 else if y i=Target i then 1 else a := by
  classical
  rw [HammingPowerProduct]
  apply Finset.prod_le_prod
  · intro i _
    split_ifs <;> positivity
  · intro i _
    rcases Chosen with Equal | Equal
    · rw [Equal]
      split_ifs <;> simp_all
    · rw [Equal]
      split_ifs <;> simp_all

theorem UnrepairedCoordinatePowerIntegral (p : I) (Target Parent : Bool) (a : ℝ) :
    (∫ b, (if Parent=Target then (1 : ℝ) else if b=Target then 1 else a)
      ∂bernoulliMeasure true false (MutationOneProbability p Parent))=
        if Parent=Target then 1 else (p : ℝ)+(1-(p : ℝ))*a := by
  rw [integral_bernoulliMeasure]
  cases Parent <;> cases Target <;>
    simp [MutationOneProbability,unitInterval.coe_symm_eq]
  ring

/-- A product bound for any selection choosing the parent or its offspring.
This retains the initially wrong coordinates and the exact mutation rate. -/
theorem SelectedHammingPowerIntegral {n : ℕ} (p : I) (Target x : Bits n)
    (Select : Bits n → Bits n → Bits n) (Selection : ∀ x y, Select x y=x ∨ Select x y=y)
    (a : ℝ) (Nonnegative : 0≤a) (AtMostOne : a≤1) :
    (∫ z, a^Hamming Target z
      ∂((IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).map (Select x)).toMeasure)≤
        ((p : ℝ)+(1-(p : ℝ))*a)^Hamming Target x := by
  classical
  rw [PMFIntegralMap]
  apply (integral_mono (Integrable.of_finite) (Integrable.of_finite)
    (fun y => SelectedHammingPowerPointwise Target x y (Select x y) a Nonnegative AtMostOne (Selection x y))).trans
  rw [← IndependentBitMutationProductLaw]
  rw [integral_fintype_prod_eq_prod (fun i (b : Bool) =>
    if x i=Target i then (1 : ℝ) else if b=Target i then 1 else a)]
  simp_rw [UnrepairedCoordinatePowerIntegral]
  rw [HammingPowerProduct]

end
end ECTheoryLib.Analysis.BitMutation

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- Exact generating power under actual uniform bit-string initialization. -/
theorem UniformInitialHammingPower (n : ℕ) (Target : Bits n) (a : ℝ) :
    (∫ x, a^Hamming Target x ∂(OnePlusOneEAInit n).toMeasure)=((1+a)/2)^n := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [OnePlusOneEAInit,PMF.uniformOfFintype_apply,smul_eq_mul,
    ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  simp_rw [HammingPowerProduct]
  have Sum : (∑ x : Bits n, ∏ i : Fin n, if x i=Target i then (1 : ℝ) else a)=(1+a)^n := by
    rw [← Fintype.prod_sum (fun i (b : Bool) => if b=Target i then (1 : ℝ) else a)]
    have Each (i : Fin n) : (∑ b : Bool, if b=Target i then (1 : ℝ) else a)=1+a := by
      rw [Fintype.sum_bool]
      cases Target i <;> simp [add_comm]
    simp only [Each,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Sum]
  have Card : Fintype.card (Bits n)=2^n := by simp [Bits]
  rw [Card,Nat.cast_pow,Nat.cast_ofNat,div_pow]
  ring

/-- Every parent-or-child selector preserving the target obeys a finite-time
hitting bound. Selection can create dependence between coordinates; only the
fresh mutation law is a product measure. -/
theorem SelectedMutationRuntimeLowerTail {n : ℕ} (p : I) (Target : Bits n)
    (Select : Bits n → Bits n → Bits n)
    (Selection : ∀ x y, Select x y=x ∨ Select x y=y)
    (PreservesTarget : ∀ y, Select Target y=Target)
    (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (fun x => (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) x).map (Select x)) Initial).real
      {Path | FirstHittingTime (fun x => x=Target) Path≤(t : WithTop ℕ)}≤
        ∫ x, (1-(1-(p : ℝ))^t)^Hamming Target x ∂Initial.toMeasure := by
  classical
  let Step : Transition (Bits n) := fun x =>
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).map (Select x)
  let f : ℕ → Bits n → ℝ := fun r x => (1-(1-(p : ℝ))^r)^Hamming Target x
  have Local (r : ℕ) (x : Bits n) : (∫ y, f r y ∂(Step x).toMeasure)≤f (r+1) x := by
    have FactorNonnegative : 0≤1-(p : ℝ) := sub_nonneg.mpr p.2.2
    have FactorAtMostOne : 1-(p : ℝ)≤1 := by linarith [p.2.1]
    have Nonnegative : 0≤1-(1-(p : ℝ))^r :=
      sub_nonneg.mpr (pow_le_one₀ FactorNonnegative FactorAtMostOne)
    have AtMostOne : 1-(1-(p : ℝ))^r≤1 := by
      have := pow_nonneg FactorNonnegative r
      linarith
    have Bound := SelectedHammingPowerIntegral p Target x Select Selection
      (1-(1-(p : ℝ))^r) Nonnegative AtMostOne
    have Factor : (p : ℝ)+(1-(p : ℝ))*(1-(1-(p : ℝ))^r)=1-(1-(p : ℝ))^(r+1) := by
      rw [pow_succ]
      ring
    rw [Factor] at Bound
    exact Bound
  have Terminal : f 0={x | x=Target}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases Goal : x=Target
    · have Distance := (HammingEqZeroIffEq Target x).mpr Goal
      dsimp [f]
      rw [Distance]
      simp [Goal]
    · have Distance : Hamming Target x≠0 := fun Zero => Goal ((HammingEqZeroIffEq Target x).mp Zero)
      simp [f,Goal,Distance]
  have Absorbing : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, x=Target → y=Target := by
    intro x
    have CandidateProperty : ∀ᵐ y ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) x).toMeasure, x=Target → Select x y=Target :=
      ae_of_all _ (fun y Equal => by subst x; exact PreservesTarget y)
    change ∀ᵐ y ∂((IndependentBitMutation (ENNReal.ofReal (p : ℝ))
      (MutationProbabilityBound p) x).map (Select x)).toMeasure, _
    rw [← PMF.toMeasure_map (Select x) _ (measurable_of_finite _)]
    exact (ae_map_iff (measurable_of_finite (Select x)).aemeasurable
      (Set.to_countable _).measurableSet).mpr CandidateProperty
  exact FirstHittingProbabilityOfBackwardBound Step Initial (fun x => x=Target)
    Absorbing f Terminal Local t

theorem UniformSelectedMutationRuntimeLowerTail {n : ℕ} (p : I) (Target : Bits n)
    (Select : Bits n → Bits n → Bits n)
    (Selection : ∀ x y, Select x y=x ∨ Select x y=y)
    (PreservesTarget : ∀ y, Select Target y=Target) (t : ℕ) :
    (PathMeasure (fun x => (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) x).map (Select x)) (OnePlusOneEAInit n)).real
      {Path | FirstHittingTime (fun x => x=Target) Path≤(t : WithTop ℕ)}≤
        (1-(1-(p : ℝ))^t/2)^n := by
  have Bound := SelectedMutationRuntimeLowerTail p Target Select Selection PreservesTarget (OnePlusOneEAInit n) t
  rw [UniformInitialHammingPower] at Bound
  have Factor : (1+(1-(1-(p : ℝ))^t))/2=1-(1-(p : ℝ))^t/2 := by ring
  rwa [Factor] at Bound

end
end ECTheoryLib.Analysis.BitMutation

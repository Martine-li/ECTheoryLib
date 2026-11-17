import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationHoeffding
import ECTheoryLib.Probability.Concentration.FiniteMGFCertificate

/-!
# Finite-size Chernoff tails for affine negative correlation

Every variable is a_i+(b_i-a_i)1_Ei on the same sample, with
0 <= a_i <= b_i <= 1. One-negative correlation gives upper tails and
zero-negative correlation gives lower tails. Empty families, zero and
maximal means, and closed endpoints are included. Exact means and
logarithmic exponential comparisons are provided. Variance families and
all mean-replacement statements from1.10.23/24 remain separate.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AffineIndicatorInUnit {Ω : Type*} (E : Set Ω) (a b : ℝ)
    (Ordered : a≤b) (NonnegativeA : 0≤a) (AtMostOneB : b≤1) (ω : Ω) :
    a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω∈Icc 0 1 := by
  have Bound := AffineIndicatorInInterval E a b Ordered ω
  exact ⟨NonnegativeA.trans Bound.1,Bound.2.trans AtMostOneB⟩

theorem AffineIndicatorMeanInUnit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (a b : ℝ)
    (Ordered : a≤b) (NonnegativeA : 0≤a) (AtMostOneB : b≤1) :
    a+(b-a)*P.real E∈Icc 0 1 := by
  have ProbabilityLower : 0≤P.real E := ENNReal.toReal_nonneg
  have ProbabilityUpper : P.real E≤1 := measureReal_le_one
  constructor
  · exact add_nonneg NonnegativeA (mul_nonneg (sub_nonneg.mpr Ordered) ProbabilityLower)
  · have Bound := mul_le_mul_of_nonneg_left ProbabilityUpper (sub_nonneg.mpr Ordered)
    nlinarith

theorem AffineSumInUnitRange {Ω : Type*} {n : ℕ} (Events : Fin n → Set Ω) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1) (ω : Ω) :
    (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))∈Icc 0 (n : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (AffineIndicatorInUnit (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i) ω).1)
  · calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ =>
        (AffineIndicatorInUnit (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i) ω).2)
      _ = _ := by simp

theorem AffineSumMeanInUnitRange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (Events : Fin n → Set Ω)
    (a b : Fin n → ℝ) (Ordered : ∀ i, a i≤b i)
    (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1) :
    (∑ i, (a i+(b i-a i)*P.real (Events i)))∈Icc 0 (n : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ =>
      (AffineIndicatorMeanInUnit P (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i)).1)
  · calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ =>
        (AffineIndicatorMeanInUnit P (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i)).2)
      _ = _ := by simp

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The unit-interval chord and AM-GM preserve the finite-size correction
for general same-sample affine indicators. -/
theorem OneNegativeCorrelationAffineFiniteMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1)
    (t : ℝ) (Nonnegative : 0≤t) :
    mgf (fun ω => ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) P t≤
      (1+((∑ i, (a i+(b i-a i)*P.real (Events i)))/(n : ℝ))*(Real.exp t-1))^n := by
  by_cases Empty : n=0
  · subst n
    simp [mgf]
  have PositiveLength : 0<n := Nat.pos_of_ne_zero Empty
  have Bound := OneNegativeCorrelationAffineMGF P Events MeasurableEvents Correlated a b Ordered t Nonnegative
  have Chord (i : Fin n) :
      (1-P.real (Events i))*Real.exp (t*a i)+P.real (Events i)*Real.exp (t*b i)≤
        1+(a i+(b i-a i)*P.real (Events i))*(Real.exp t-1) := by
    have Single := UnitIntervalMGFChord P
      (fun ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)
      (AffineIndicatorMeasurable (Events i) (MeasurableEvents i) (a i) (b i)).aemeasurable
      (Filter.Eventually.of_forall (AffineIndicatorInUnit (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i))) t
    rwa [AffineIndicatorMGF P (Events i) (MeasurableEvents i),
      AffineIndicatorIntegral P (Events i) (MeasurableEvents i)] at Single
  apply Bound.trans
  calc
    _ ≤ ∏ i, (1+(a i+(b i-a i)*P.real (Events i))*(Real.exp t-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        have ProbabilityUpper := measureReal_le_one (μ := P) (s := Events i)
        positivity
      · intro i _
        exact Chord i
    _ ≤ ((∑ i : Fin n, (1+(a i+(b i-a i)*P.real (Events i))*(Real.exp t-1)))/(n : ℝ))^n := by
      apply NonnegativeProductLeMeanPow PositiveLength
      intro i
      have MeanNonnegative := (AffineIndicatorMeanInUnit P (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i)).1
      have ExpAtLeastOne : 1≤Real.exp t := Real.one_le_exp_iff.mpr Nonnegative
      positivity
    _ = _ := by
      congr 1
      rw [Finset.sum_add_distrib,← Finset.sum_mul]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      have NonzeroN : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr PositiveLength.ne'
      field_simp

/-- At the maximum sum every bounded coordinate equals one. Integrating
the product and applying the affine-product correlation bound handles the
endpoint without a singular optimizing tilt. -/
theorem OneNegativeCorrelationAffineFiniteEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1) :
    P.real {ω | (n : ℝ)≤∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      ((∑ i, (a i+(b i-a i)*P.real (Events i)))/(n : ℝ))^n := by
  by_cases Empty : n=0
  · subst n
    simp
  let X := fun i ω => a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω
  have Bounded (i : Fin n) (ω : Ω) : X i ω∈Icc 0 1 :=
    AffineIndicatorInUnit (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i) ω
  have MeasurableX (i : Fin n) : Measurable (X i) :=
    AffineIndicatorMeasurable (Events i) (MeasurableEvents i) (a i) (b i)
  let E : Set Ω := {ω | (n : ℝ)≤∑ i, X i ω}
  have MeasurableE : MeasurableSet E := measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => MeasurableX i))
  have IntegrableProduct : Integrable (fun ω => ∏ i, X i ω) P := by
    apply Integrable.of_mem_Icc 0 1 (Finset.measurable_prod _ (fun i _ => MeasurableX i)).aemeasurable
    apply ae_of_all
    intro ω
    exact ⟨Finset.prod_nonneg (fun i _ => (Bounded i ω).1),
      Finset.prod_le_one (fun i _ => (Bounded i ω).1) (fun i _ => (Bounded i ω).2)⟩
  have IndicatorLe (ω : Ω) : E.indicator (fun _ => (1 : ℝ)) ω≤∏ i, X i ω := by
    by_cases Inside : ω∈E
    · rw [indicator_of_mem Inside]
      change (n : ℝ)≤∑ i, X i ω at Inside
      have SumBound : (∑ i, X i ω)≤∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (Bounded i ω).2)
      have SumEqual : (∑ i, X i ω)=∑ _i : Fin n, (1 : ℝ) :=
        le_antisymm SumBound (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using Inside)
      have AllOne (i : Fin n) : X i ω=1 :=
        (Finset.sum_eq_sum_iff_of_le (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => (Bounded j ω).2)).mp SumEqual i (Finset.mem_univ i)
      simp_rw [AllOne]
      simp
    · rw [indicator_of_notMem Inside]
      exact Finset.prod_nonneg (fun i _ => (Bounded i ω).1)
  have First := integral_mono ((integrable_const (1 : ℝ)).indicator MeasurableE) IntegrableProduct IndicatorLe
  rw [integral_indicator_const _ MeasurableE] at First
  simp only [smul_eq_mul,mul_one] at First
  apply First.trans
  apply (OneNegativeCorrelationAffineProduct P Events MeasurableEvents Correlated a
    (fun i => b i-a i) NonnegativeA (fun i => sub_nonneg.mpr (Ordered i)) Finset.univ).trans
  exact NonnegativeProductLeMeanPow (Nat.pos_of_ne_zero Empty) _
    (fun i => (AffineIndicatorMeanInUnit P (Events i) (a i) (b i) (Ordered i) (NonnegativeA i) (AtMostOneB i)).1)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Finite-size Chernoff upper bound for actual affine event indicators
with 0 ≤ aᵢ ≤ bᵢ ≤ 1 and all-subset one-negative correlation. -/
theorem OneNegativeCorrelationAffineFiniteChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1)
    (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*(∑ i, (a i+(b i-a i)*P.real (Events i)))≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      FiniteChernoffUpperBound n (∑ i, (a i+(b i-a i)*P.real (Events i))) d := by
  apply FiniteMGFCertificateChernoffUpper P
  · exact (AffineSumMeasurable Events MeasurableEvents a b).aemeasurable
  · exact ae_of_all _ (AffineSumInUnitRange Events a b Ordered NonnegativeA AtMostOneB)
  · exact OneNegativeCorrelationAffineFiniteMGF P Events MeasurableEvents Correlated a b Ordered NonnegativeA AtMostOneB
  · exact OneNegativeCorrelationAffineFiniteEndpoint P Events MeasurableEvents Correlated a b Ordered NonnegativeA AtMostOneB
  · exact Finset.sum_nonneg (fun i _ => (AffineIndicatorMeanInUnit P (Events i) (a i) (b i)
      (Ordered i) (NonnegativeA i) (AtMostOneB i)).1)
  · exact Nonnegative

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Complement both the event and its ordered endpoints to represent the
actual value 1-Y on the same sample. -/
theorem AffineComplementIndicator {Ω : Type*} (E : Set Ω) (a b : ℝ) (ω : Ω) :
    (1-b)+((1-a)-(1-b))*Eᶜ.indicator (fun _ => (1 : ℝ)) ω=
      1-(a+(b-a)*E.indicator (fun _ => (1 : ℝ)) ω) := by
  by_cases Inside : ω∈E <;> simp [Inside]

theorem AffineComplementSum {Ω : Type*} {n : ℕ} (Events : Fin n → Set Ω)
    (a b : Fin n → ℝ) (ω : Ω) :
    (∑ i, ((1-b i)+((1-a i)-(1-b i))*(Events i)ᶜ.indicator (fun _ => (1 : ℝ)) ω))=
      (n : ℝ)-(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)) := by
  simp_rw [AffineComplementIndicator]
  rw [Finset.sum_sub_distrib]
  simp

theorem AffineComplementMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i)) (a b : Fin n → ℝ) :
    (∑ i, ((1-b i)+((1-a i)-(1-b i))*P.real (Events i)ᶜ))=
      (n : ℝ)-(∑ i, (a i+(b i-a i)*P.real (Events i))) := by
  simp_rw [probReal_compl_eq_one_sub (MeasurableEvents _)]
  have Each (i : Fin n) : (1-b i)+((1-a i)-(1-b i))*(1-P.real (Events i))=
      1-(a i+(b i-a i)*P.real (Events i)) := by ring
  simp_rw [Each]
  rw [Finset.sum_sub_distrib]
  simp

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- The complement endpoint retains the finite-size correction for a
zero-negatively correlated affine sum, including n=0 and d=1. -/
theorem ZeroNegativeCorrelationAffineFiniteEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤0}≤
      (1-(∑ i, (a i+(b i-a i)*P.real (Events i)))/(n : ℝ))^n := by
  by_cases Empty : n=0
  · subst n
    simp
  have Bound := OneNegativeCorrelationAffineFiniteEndpoint P (fun i => (Events i)ᶜ)
    (fun i => (MeasurableEvents i).compl) Correlated (fun i => 1-b i) (fun i => 1-a i)
    (fun i => sub_le_sub_left (Ordered i) 1) (fun i => sub_nonneg.mpr (AtMostOneB i))
    (fun i => sub_le_self 1 (NonnegativeA i))
  simp_rw [AffineComplementSum,AffineComplementMean P Events MeasurableEvents] at Bound
  have Event : {ω | (n : ℝ)≤(n : ℝ)-(∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))}=
      {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤0} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event,sub_div,div_self (Nat.cast_ne_zero.mpr Empty)] at Bound
  exact Bound

/-- Full finite-size lower Chernoff bound for same-sample affine indicators.
The actual complement preserves zero-negative correlation as one-negative
correlation; no independent replacement variables are introduced. -/
theorem ZeroNegativeCorrelationAffineFiniteChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
      (1-d)*(∑ i, (a i+(b i-a i)*P.real (Events i)))}≤
      FiniteChernoffLowerBound n (∑ i, (a i+(b i-a i)*P.real (Events i))) d := by
  apply FiniteMGFCertificateChernoffLower P
  · exact (AffineSumMeasurable Events MeasurableEvents a b).aemeasurable
  · exact ae_of_all _ (AffineSumInUnitRange Events a b Ordered NonnegativeA AtMostOneB)
  · exact AffineSumIntegral P Events MeasurableEvents a b
  · intro t Nonnegative
    have Bound := OneNegativeCorrelationAffineFiniteMGF P (fun i => (Events i)ᶜ)
      (fun i => (MeasurableEvents i).compl) Correlated (fun i => 1-b i) (fun i => 1-a i)
      (fun i => sub_le_sub_left (Ordered i) 1) (fun i => sub_nonneg.mpr (AtMostOneB i))
      (fun i => sub_le_self 1 (NonnegativeA i)) t Nonnegative
    simpa only [AffineComplementSum,AffineComplementMean P Events MeasurableEvents] using Bound
  · exact ZeroNegativeCorrelationAffineFiniteEndpoint P Events MeasurableEvents Correlated a b Ordered NonnegativeA AtMostOneB
  · exact InUnit

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem OneNegativeCorrelationAffineChernoffUpper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : OneNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1)
    (d : ℝ) (Nonnegative : 0≤d) :
    P.real {ω | (1+d)*(∑ i, (a i+(b i-a i)*P.real (Events i)))≤
      ∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω)}≤
      Real.exp (-((1+d)*Real.log (1+d)-d)*(∑ i, (a i+(b i-a i)*P.real (Events i)))) := by
  exact (OneNegativeCorrelationAffineFiniteChernoffUpper P Events MeasurableEvents Correlated a b
    Ordered NonnegativeA AtMostOneB d Nonnegative).trans
    (FiniteChernoffUpperBoundLeExp n _ d
      (AffineSumMeanInUnitRange P Events a b Ordered NonnegativeA AtMostOneB).1 Nonnegative)

theorem ZeroNegativeCorrelationAffineChernoffLower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Events : Fin n → Set Ω) (MeasurableEvents : ∀ i, MeasurableSet (Events i))
    (Correlated : ZeroNegativelyCorrelated P Events) (a b : Fin n → ℝ)
    (Ordered : ∀ i, a i≤b i) (NonnegativeA : ∀ i, 0≤a i) (AtMostOneB : ∀ i, b i≤1)
    (d : ℝ) (InUnit : d∈Icc 0 1) :
    P.real {ω | (∑ i, (a i+(b i-a i)*(Events i).indicator (fun _ => (1 : ℝ)) ω))≤
      (1-d)*(∑ i, (a i+(b i-a i)*P.real (Events i)))}≤
      Real.exp (-(d+(1-d)*Real.log (1-d))*(∑ i, (a i+(b i-a i)*P.real (Events i)))) := by
  exact (ZeroNegativeCorrelationAffineFiniteChernoffLower P Events MeasurableEvents Correlated a b
    Ordered NonnegativeA AtMostOneB d InUnit).trans
    (FiniteChernoffLowerBoundLeExp n _ d (AffineSumMeanInUnitRange P Events a b Ordered NonnegativeA AtMostOneB) InUnit)

end
end ECTheoryLib.Probability

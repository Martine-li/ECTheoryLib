import ECTheoryLib.Analysis.MultivalOneMax.RLS.InitializationHoeffding
import ECTheoryLib.Analysis.MultivalOneMax.RLS.BinarySpecialization

/-!
# Uniform binary initialization around an arbitrary target

Doerr Lemma 1.10.8 is stated on actual Bool bit strings and RLSInit.
The existing binary encoding preserves Hamming distance; singleton masses
verify that decoding the uniform two-symbol law is exactly RLSInit.
Transporting the finite-alphabet bound gives the two-sided exponential
tail around n/2 without assumptions on the target or positive length.
-/

namespace ECTheoryLib.Analysis.RLSHamming
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Analysis.RLSMultivalBinary
noncomputable section

/-- Decoding the uniformly initialized two-symbol alphabet gives the actual uniform bit-string law. -/
theorem UniformBinaryDecodedLaw (n : ℕ) :
    (MultivalRLSInit n 2 (by decide)).toMeasure.map DecodeBits = (RLSInit n).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  have Preimage : DecodeBits ⁻¹' {x} = {EncodeBits x} := by
    ext y
    change DecodeBits y = x ↔ y = EncodeBits x
    constructor
    · intro Decoded
      rw [← Decoded, EncodeDecodeBits]
    · intro Encoded
      rw [Encoded, DecodeEncodeBits]
  rw [Measure.map_apply (measurable_of_finite DecodeBits) (measurableSet_singleton x), Preimage,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    MultivalRLSInitProbability, RLSInitProbability]
  simp only [Nat.cast_ofNat]

/-- The actual uniform initialization has the Hoeffding absolute-deviation bound. -/
theorem UniformHammingHoeffdingDeviation {n : ℕ} (Target : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (RLSInit n).toMeasure.real
      {x | d ≤ |(Problems.TargetOneMax.Hamming Target x : ℝ)-(n : ℝ)/2|} ≤
      2*Real.exp (-2*d^2/(n : ℝ)) := by
  have Bound := RLSMultival.UniformBinaryHammingHoeffdingDeviation (EncodeBits Target) d Nonnegative
  rw [← UniformBinaryDecodedLaw, map_measureReal_apply (measurable_of_finite DecodeBits)
    ((Set.to_countable _).measurableSet)]
  have HammingIdentity (x : MultiValues n 2) :
      Problems.MultivalOneMax.Hamming (EncodeBits Target) x =
        Problems.TargetOneMax.Hamming Target (DecodeBits x) := by
    have Encoded := HammingEncodeBits Target (DecodeBits x)
    rw [EncodeDecodeBits] at Encoded
    exact Encoded
  simp only [HammingIdentity] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSHamming

import ECTheoryLib.Algorithms.RLS

/-!
# Single-coordinate search with a user-supplied selection policy

`CoordinateSearchStep` chooses a coordinate from a state-dependent PMF and uses
the existing one-bit mutation and elitist selection. `HalfUniformChoice` is a
concrete policy with a uniform half and an arbitrary preferred-coordinate half.
These definitions contain no objective-specific analysis or runtime assumptions.
-/
namespace ECTheoryLib
noncomputable section

/-- One iteration of single-bit search with an arbitrary state-dependent coordinate PMF.
`NotWorse` is applied to the candidate first, then the parent, as in `RLSUpdate`. -/
def CoordinateSearchStep {n : Nat} (Choice : Bits n → PMF (Fin n))
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (x : Bits n) : PMF (Bits n) :=
  (Choice x).map (RLSUpdate NotWorse x)

/-- Choosing coordinates uniformly recovers the existing RLS transition exactly. -/
theorem CoordinateSearchUniformEqRLS {n : Nat} (hn : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (x : Bits n) :
    CoordinateSearchStep (fun _ => UniformBitIndex n hn) NotWorse x =
      RLSStep hn NotWorse x := by
  exact (RLSStepEqUniformUpdate hn NotWorse x).symm

/-- Choose uniformly with probability one half; otherwise choose the preferred
coordinate. The preferred coordinate may depend on the complete current state. -/
def HalfUniformChoice {n : Nat} (hn : 0 < n) (Preferred : Bits n → Fin n)
    (x : Bits n) : PMF (Fin n) :=
  (PMF.uniformOfFintype Bool).bind
    (fun b => if b then UniformBitIndex n hn else PMF.pure (Preferred x))

/-- Every coordinate retains probability at least `1/(2n)` under the mixed policy. -/
theorem HalfUniformChoiceProbabilityLower {n : Nat} (hn : 0 < n)
    (Preferred : Bits n → Fin n) (x : Bits n) (i : Fin n) :
    (2 : ENNReal)⁻¹ * (n : ENNReal)⁻¹ ≤ HalfUniformChoice hn Preferred x i := by
  unfold HalfUniformChoice
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.uniformOfFintype_apply,
    Fintype.card_bool, UniformBitIndexProbability]
  norm_num only [Nat.cast_ofNat]
  exact le_add_of_nonneg_right
    (show (0 : ENNReal) ≤ (2 : ENNReal)⁻¹ * PMF.pure (Preferred x) i from bot_le)

end
end ECTheoryLib

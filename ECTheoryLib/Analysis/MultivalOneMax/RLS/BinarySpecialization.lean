import ECTheoryLib.Algorithms.MultivalRLS
import ECTheoryLib.Problems.MultivalOneMax
import ECTheoryLib.Analysis.TargetOneMax.RLS.Drift
import ECTheoryLib.Analysis.TargetOneMax.RLS.ExactRuntime
import ECTheoryLib.Analysis.MultivalOneMax.RLS.ExactRuntime
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Function.Basic

/-!
# Binary specialization of the real multivalued RLS kernel

For r = 2, an admissible replacement is the unique other alphabet value.
The equivalence below identifies the interval-distance fitness, accepted
coordinate updates, and the full probability kernel with binary Hamming RLS.
-/

namespace ECTheoryLib.Analysis.RLSMultivalBinary

noncomputable section

/-- Encode false and true as the two values 0 and 1 of Fin 2. -/
def EncodeBits {n : Nat} (State : Bits n) : MultiValues n 2 :=
  fun i => finTwoEquiv.symm (State i)

/-- Decode the finite binary alphabet to Bool coordinate by coordinate. -/
def DecodeBits {n : Nat} (State : MultiValues n 2) : Bits n :=
  fun i => finTwoEquiv (State i)

theorem DecodeEncodeBits {n : Nat} (State : Bits n) :
    DecodeBits (EncodeBits State) = State := by
  funext i
  exact finTwoEquiv.apply_symm_apply (State i)

theorem EncodeDecodeBits {n : Nat} (State : MultiValues n 2) :
    EncodeBits (DecodeBits State) = State := by
  funext i
  exact finTwoEquiv.symm_apply_apply (State i)

theorem EncodeBitsValue {n : Nat} (State : Bits n) (i : Fin n) :
    (EncodeBits State i).val = Bool.toNat (State i) := by
  unfold EncodeBits
  cases State i with
  | false => rfl
  | true => rfl

/-- The genuine interval-distance objective becomes the binary Hamming objective. -/
theorem DistanceEncodeBits {n : Nat} (Target State : Bits n) :
    Problems.MultivalOneMax.Distance (EncodeBits Target) (EncodeBits State) =
      Problems.TargetOneMax.Hamming Target State := by
  rw [Problems.TargetOneMax.HammingEqBinaryIntervalDistance]
  unfold Problems.MultivalOneMax.Distance
  apply Finset.sum_congr rfl
  intro i _Membership
  rw [EncodeBitsValue, EncodeBitsValue]

theorem DistanceEqDecodedHamming {n : Nat} (Target State : MultiValues n 2) :
    Problems.MultivalOneMax.Distance Target State =
      Problems.TargetOneMax.Hamming (DecodeBits Target) (DecodeBits State) := by
  have EncodedDistance := DistanceEncodeBits (DecodeBits Target) (DecodeBits State)
  rw [EncodeDecodeBits, EncodeDecodeBits] at EncodedDistance
  exact EncodedDistance

theorem HammingEncodeBits {n : Nat} (Target State : Bits n) :
    Problems.MultivalOneMax.Hamming (EncodeBits Target) (EncodeBits State) =
      Problems.TargetOneMax.Hamming Target State := by
  unfold Problems.MultivalOneMax.Hamming Problems.TargetOneMax.Hamming
  apply Finset.sum_congr rfl
  intro i _Membership
  have SameCoordinate : EncodeBits State i = EncodeBits Target i ↔ State i = Target i := by
    exact finTwoEquiv.symm.injective.eq_iff
  simp only [SameCoordinate]

/-- In a binary alphabet, any admissible other value decodes to the flipped bit. -/
theorem DecodeOtherValue (Parent Candidate : Fin 2) (Different : Candidate ≠ Parent) :
    finTwoEquiv Candidate = !(finTwoEquiv Parent) := by
  fin_cases Parent
  · fin_cases Candidate
    · exact False.elim (Different rfl)
    · rfl
  · fin_cases Candidate
    · rfl
    · exact False.elim (Different rfl)

theorem DecodeMutation {n : Nat} (State : MultiValues n 2) (i : Fin n)
    (Value : Fin 2) (Different : Value ≠ State i) :
    DecodeBits (Function.update State i Value) = OnebitMutation (DecodeBits State) i := by
  funext j
  by_cases SamePosition : j = i
  · subst j
    change finTwoEquiv (Function.update State i Value i) =
      OnebitMutation (DecodeBits State) i i
    rw [Function.update_self, OnebitMutationAt]
    exact DecodeOtherValue (State i) Value Different
  · change finTwoEquiv (Function.update State i Value j) =
      OnebitMutation (DecodeBits State) i j
    rw [Function.update_of_ne SamePosition,
      OnebitMutationAway (DecodeBits State) i j SamePosition]
    rfl

/-- Decoding preserves the actual interval-distance elitist selection, including ties. -/
theorem DecodeSelection {n : Nat} (Target Parent Candidate : MultiValues n 2) :
    DecodeBits
      (ElitistSelect (Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target))
        Parent Candidate) =
      ElitistSelect (Problems.MinNotWorse (Problems.TargetOneMax.Hamming (DecodeBits Target)))
        (DecodeBits Parent) (DecodeBits Candidate) := by
  have SameComparison :
      Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target) Candidate Parent ↔
        Problems.MinNotWorse (Problems.TargetOneMax.Hamming (DecodeBits Target))
          (DecodeBits Candidate) (DecodeBits Parent) := by
    unfold Problems.MinNotWorse
    rw [DistanceEqDecodedHamming, DistanceEqDecodedHamming]
  by_cases Accept :
      Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target) Candidate Parent
  · rw [ElitistSelectAccept _ _ _ Accept,
      ElitistSelectAccept _ _ _ (SameComparison.mp Accept)]
  · have DecodedReject :
        ¬ Problems.MinNotWorse (Problems.TargetOneMax.Hamming (DecodeBits Target))
          (DecodeBits Candidate) (DecodeBits Parent) := by
      intro DecodedAccept
      exact Accept (SameComparison.mpr DecodedAccept)
    rw [ElitistSelectReject _ _ _ Accept,
      ElitistSelectReject _ _ _ DecodedReject]

theorem DecodeUpdate {n : Nat} (Target State : MultiValues n 2) (i : Fin n)
    (Value : Fin 2) (Different : Value ≠ State i) :
    DecodeBits
      (MultivalRLSUpdate (Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target))
        State i Value) =
      RLSHamming.Update (DecodeBits Target) (DecodeBits State) i := by
  unfold MultivalRLSUpdate
  rw [DecodeSelection, DecodeMutation State i Value Different]
  rfl

/-- Every binary coordinate choice is determined by its index. -/
def BinaryChoiceEquiv {n : Nat} (State : MultiValues n 2) :
    CoordinateChoice State ≃ Fin n where
  toFun Choice := Choice.1
  invFun i := ⟨i, ⟨finTwoEquiv.symm (!(finTwoEquiv (State i))), by
    intro SameValue
    have SameBool := congrArg finTwoEquiv SameValue
    rw [finTwoEquiv.apply_symm_apply] at SameBool
    have NeverSelf : ∀ Bit : Bool, (!Bit) ≠ Bit := by
      intro Bit
      cases Bit with
      | false =>
          intro Equality
          cases Equality
      | true =>
          intro Equality
          cases Equality
    exact NeverSelf (finTwoEquiv (State i)) SameBool⟩⟩
  left_inv Choice := by
    cases Choice with
    | mk i Value =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Subtype.ext
          apply finTwoEquiv.injective
          rw [finTwoEquiv.apply_symm_apply]
          exact (DecodeOtherValue (State i) Value.val Value.property).symm
  right_inv i := rfl

/-- Uniform finite sampling is transported along an equivalence. -/
private theorem UniformMapEquiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (Equivalence : α ≃ β) :
    (PMF.uniformOfFintype α).map Equivalence = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, tsum_fintype]
  have Preimage : ∀ a : α, b = Equivalence a ↔ a = Equivalence.symm b := by
    intro a
    constructor
    · intro Equality
      exact ((congrArg Equivalence.symm Equality).trans
        (Equivalence.symm_apply_apply a)).symm
    · intro Equality
      rw [Equality, Equivalence.apply_symm_apply]
  simp_rw [Preimage, PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr Equivalence]
  simp

/-- Joint uniform sampling of (index, other value) reduces to uniform index sampling. -/
theorem UniformBinaryChoiceIndex {n : Nat} (PositiveLength : 0 < n)
    (State : MultiValues n 2) :
    (UniformCoordinateChoice PositiveLength (by decide : 2 ≤ 2) State).map
      (fun Choice => Choice.1) = UniformBitIndex n PositiveLength := by
  let : Nonempty (Fin n) := ⟨⟨0, PositiveLength⟩⟩
  let : Nonempty (CoordinateChoice State) :=
    ⟨(BinaryChoiceEquiv State).symm ⟨0, PositiveLength⟩⟩
  unfold UniformCoordinateChoice UniformBitIndex
  change (PMF.uniformOfFintype (CoordinateChoice State)).map (BinaryChoiceEquiv State) =
    PMF.uniformOfFintype (Fin n)
  exact UniformMapEquiv (BinaryChoiceEquiv State)

/-- The full true multivalued probability kernel specializes to binary Hamming RLS. -/
theorem DecodeStep {n : Nat} (PositiveLength : 0 < n)
    (Target State : MultiValues n 2) :
    (MultivalRLSStep PositiveLength (by decide : 2 ≤ 2)
      (Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target)) State).map DecodeBits =
      RLSHamming.Step PositiveLength (DecodeBits Target) (DecodeBits State) := by
  unfold MultivalRLSStep
  rw [PMF.map_comp]
  simp only [Function.comp_def]
  have UpdateFunctionsEqual :
      (fun Choice : CoordinateChoice State =>
        DecodeBits
          (MultivalRLSUpdate
            (Problems.MinNotWorse (Problems.MultivalOneMax.Distance Target))
            State Choice.1 Choice.2.val)) =
      (fun Choice : CoordinateChoice State =>
        RLSHamming.Update (DecodeBits Target) (DecodeBits State) Choice.1) := by
    funext Choice
    exact DecodeUpdate Target State Choice.1 Choice.2.val Choice.2.property
  rw [UpdateFunctionsEqual]
  change
    (UniformCoordinateChoice PositiveLength (by decide : 2 ≤ 2) State).map
      ((RLSHamming.Update (DecodeBits Target) (DecodeBits State)) ∘
        (fun Choice : CoordinateChoice State => Choice.1)) =
      RLSHamming.Step PositiveLength (DecodeBits Target) (DecodeBits State)
  rw [← PMF.map_comp]
  rw [UniformBinaryChoiceIndex]
  rw [RLSHamming.Step, RLSStepEqUniformUpdate]

/-- The exact expectation at alphabet size 2 agrees with the public binary
Hamming interface, complementing the equality of the actual kernels. -/
theorem ExpectedRuntimeEncodeBits {n : Nat} (PositiveLength : 0 < n)
    (Target InitialState : Bits n) :
    RLSMultival.ExpectedRuntime PositiveLength (by decide : 2 ≤ 2)
      (EncodeBits Target) (EncodeBits InitialState) =
      RLSHamming.ExpectedRuntime PositiveLength Target InitialState := by
  rw [RLSMultival.FixedRuntimeExact, HammingEncodeBits, RLSHamming.FixedRuntimeExact]
  norm_num

end
end ECTheoryLib.Analysis.RLSMultivalBinary

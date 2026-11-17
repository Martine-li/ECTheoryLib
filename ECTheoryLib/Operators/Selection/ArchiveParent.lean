import ECTheoryLib.Operators.Selection.ParetoArchive

/-!
# An archive-dependent parent policy with a uniform component

With probability one half choose a uniformly sampled archive member, and with
probability one half choose a user-specified member. The preferred member can
depend on the entire current archive. Membership is part of its type, so every
possible parent belongs to the archive. Each member retains probability at
least half its uniform-parent probability.
-/
namespace ECTheoryLib
noncomputable section

/-- Half-uniform parent policy with a user-specified current archive member. -/
def HalfUniformArchiveParent {α : Type*}
    (Preferred : (P : ParetoPopulation α) → {x // x ∈ P.val})
    (P : ParetoPopulation α) : PMF α :=
  (PMF.uniformOfFintype Bool).bind
    (fun b => if b then UniformParetoParent P else PMF.pure (Preferred P).val)

/-- Every member keeps at least half its uniform selection mass. -/
theorem HalfUniformArchiveParentLower {α : Type*}
    (Preferred : (P : ParetoPopulation α) → {x // x ∈ P.val})
    (P : ParetoPopulation α) (x : α) :
    (2 : ENNReal)⁻¹ * UniformParetoParent P x ≤ HalfUniformArchiveParent Preferred P x := by
  unfold HalfUniformArchiveParent
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  norm_num only [Nat.cast_ofNat]
  exact le_add_of_nonneg_right
    (show (0 : ENNReal) ≤ (2 : ENNReal)⁻¹ * PMF.pure (Preferred P).val x from bot_le)

/-- Both branches of the mixed policy select actual archive members. -/
theorem HalfUniformArchiveParentMember {α : Type*}
    (Preferred : (P : ParetoPopulation α) → {x // x ∈ P.val})
    (P : ParetoPopulation α) (x : α)
    (Possible : x ∈ (HalfUniformArchiveParent Preferred P).support) : x ∈ P.val := by
  obtain ⟨b, _PossibleBool, PossibleParent⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
  cases b with
  | false =>
      have Equal : x = (Preferred P).val := (PMF.mem_support_pure_iff _ _).mp PossibleParent
      rw [Equal]
      exact (Preferred P).property
  | true => exact (UniformParetoParentSupport P x).mp PossibleParent

end
end ECTheoryLib

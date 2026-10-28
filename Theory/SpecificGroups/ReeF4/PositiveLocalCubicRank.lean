module
public import Theory.SpecificGroups.Tits.PositiveLocalCubicRank
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Positive local cubic rank in Ree fixed groups

The genuine subfield Tits subgroup embeds in each binary Ree model. The
normalizer of its nontrivial two-local witness embeds in the normalizer of
the image, so positive local three-rank survives. The supplied exceptional
root endomorphism is retained through its actual fixed-group equivalence.

This is the Ree row of the nonnormal-component local-rank budget in
Aschbacher–Smith A.3.8, printed pp.45–46.
-/

public noncomputable section
namespace ReeF4.PositiveLocalCubicRank
/-- The genuine subfield Tits subgroup supplies a local cubic witness in each Ree model. -/
theorem model (m : ℕ) : 1 ≤ twoLocalPrimeRank 3 (Model m) := by
  obtain ⟨j,hj⟩ := Subfield.exists_tits_embedding m
  exact Tits.parrott_one_le_twoLocalPrimeRank_three.trans
    (twoLocalPrimeRank_le_of_injective 3 j hj)

/-- Transport to the fixed group of the supplied exceptional root endomorphism. -/
theorem fixedGroup {m : ℕ} (d : LocalBlockInput m) :
    1 ≤ twoLocalPrimeRank 3 d.fixedGroup :=
  (model m).trans (twoLocalPrimeRank_le_of_injective 3
    d.modelEquiv.symm.toMonoidHom d.modelEquiv.symm.injective)
end ReeF4.PositiveLocalCubicRank
